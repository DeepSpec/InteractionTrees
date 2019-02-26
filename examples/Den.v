From ITree Require Import
     ITree
     OpenSum
     Fix
     FixFacts
     Basics_Functions.

From Coq Require Import
     Program
     Morphisms.

Set Nested Proofs Allowed.
(** * Category of denotations *)

Definition den {E: Type -> Type} A B : Type := A -> itree E B.
(* den can represent both blocks (A -> block B) and asm (asm A B). *)

Section Den.

  (* (@den E) forms a traced monoidal category, i.e. a symmetric monoidal one with a loop operator *)
  (* Obj ≅ Type *)
  (* Arrow: A -> B ≅ terms of type (den A B) *)

  Context {E: Type -> Type}.
  Notation denE := (@den E).

  Section Equivalence.

    (* We work up to pointwise eutt *)
    Definition eq_den {A B} (d1 d2 : A -> itree E B) :=
      (forall a, eutt eq (d1 a) (d2 a)).

    Global Instance Equivalence_eq_den {A B} : Equivalence (@eq_den A B).
    Proof.
      split.
      - intros ab a; reflexivity.
      - intros ab ab' eqAB a; symmetry; auto.
      - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
    Qed.

    Global Instance eq_den_elim {A B C} :
      Proper (eq_den ==> eq_den ==> eq_den) (@sum_elim A B (itree E C)).
    Proof.
      repeat intro. destruct a; unfold sum_elim; auto.
    Qed.

  End Equivalence.

  Infix "⩰" := eq_den (at level 70).

  Section Structure.

    (* Composition *)
    Notation compose_den := ITree.cat.

    (* Identities *)
    Definition I: Type := Empty_set.
    Definition id_den {A} : denE A A := fun a => Ret a.

    (* Utility function to lift a pure computation into den *)
    Definition lift_den {A B} (f : A -> B) : denE A B := fun a => Ret (f a).

    (* Tensor product *)
    (* Tensoring on objects is simply the sum type constructor *)
    Definition tensor_den {A B C D}
               (ab : denE A B) (cd : denE C D) : den (A + C) (B + D) :=
      sum_elim (compose_den ab (lift_den inl)) (compose_den cd (lift_den inr)).

    (* Left and right unitors *)
    Definition λ_den  {A: Type}: denE (I + A) A := lift_den sum_empty_l.
    Definition λ_den' {A: Type}: denE A (I + A) := lift_den inr.
    Definition ρ_den  {A: Type}: denE (A + I) A := lift_den sum_empty_r.
    Definition ρ_den' {A: Type}: denE A (A + I) := lift_den inl.

    (* Associator *)
    Definition assoc_den_l {A B C: Type}: denE (A + (B + C)) ((A + B) + C) := lift_den sum_assoc_l.
    Definition assoc_den_r {A B C: Type}: denE ((A + B) + C) (A + (B + C)) := lift_den sum_assoc_r.

    (* Symmetry *)
    Definition sym_den {A B: Type}: denE (A + B) (B + A) := lift_den sum_comm.

    (*
   A [box : den (I + A) (I + B)] is a circuit, drawn below as ###,
   with two input wires labeled by I and A, and two output wires
   labeled by I and B.

   The [loop_den : den (I + A) (I + B) -> den A B] combinator closes
   the circuit, linking the box with itself by plugging the I output
   back into the input.

     +-----+
     | ### |
     +-###-+I
  A----###----B
       ###

     *)
    Definition loop_den {I A B} :
      (I + A -> itree E (I + B)) -> A -> itree E B := loop.

  End Structure.

  Infix "⊗" := (tensor_den) (at level 30).

  Section Laws.

    (** *** [compose_den] respect eq_den *)
    Global Instance eq_den_compose {A B C} :
      Proper (eq_den ==> eq_den ==> eq_den) (@ITree.cat _ A B C).
    Proof.
      intros ab ab' eqAB bc bc' eqBC.
      intro a.
      unfold ITree.cat.
      rewrite (eqAB a).
      apply eutt_bind; try reflexivity.
      intro b; rewrite (eqBC b); reflexivity.
    Qed.

    (** *** [compose_den] is associative *)
    Lemma compose_den_assoc {A B C D}
          (ab : den A B) (bc : den B C) (cd : den C D) :
      ((ab >=> bc) >=> cd) ⩰ (ab >=> (bc >=> cd)).
    Proof.
      intros a.
      unfold ITree.cat.
      rewrite bind_bind.
      apply eutt_bind; try reflexivity.
    Qed.

    (** *** [id_den] respect identity laws *)
    Lemma id_den_left {A B}: forall (f: denE A B),
        id_den >=> f ⩰ f.
    Proof.
      intros f a; unfold ITree.cat, id_den.
      rewrite itree_eta; rewrite ret_bind. rewrite <- itree_eta; reflexivity. 
    Qed.

    Lemma id_den_right {A B}: forall (f: denE A B),
        f >=> id_den ⩰ f.
    Proof.
      intros f a; unfold ITree.cat, id_den.
      rewrite <- (bind_ret (f a)) at 2.
      reflexivity.
    Qed.

    (** *** [lift_den] is well-behaved *)

    Global Instance eq_lift_den {A B} :
      Proper (eeq ==> eq_den) (@lift_den A B).
    Proof.
      repeat intro.
      unfold lift_den.
      erewrite (H a); reflexivity.
    Qed.

    Fact compose_lift_den {A B C} (ab : A -> B) (bc : B -> C) :
      (lift_den ab >=> lift_den bc) ⩰ (lift_den (bc ∘ ab)).
    Proof.
      intros a.
      unfold lift_den, ITree.cat.
      rewrite ret_bind_.
      reflexivity.
    Qed.

    Fact compose_lift_den_l {A B C D} (f: A -> B) (g: B -> C) (k: den C D) :
      (lift_den f >=> (lift_den g >=> k)) ⩰ (lift_den (g ∘ f) >=> k).
    Proof.
      rewrite <- compose_den_assoc.
      rewrite compose_lift_den.
      reflexivity.
    Qed.

    Fact compose_lift_den_r {A B C D} (f: B -> C) (g: C -> D) (k: den A B) :
      ((k >=> lift_den f) >=> lift_den g) ⩰ (k >=> lift_den (g ∘ f)).
    Proof.
      rewrite compose_den_assoc.
      rewrite compose_lift_den.
      reflexivity.
    Qed.

    Fact lift_compose_den {A B C}: forall (f:A -> B) (bc: den B C),
        lift_den f >=> bc ⩰ fun a => bc (f a).
    Proof.
      intros; intro a.
      unfold lift_den, ITree.cat.
      rewrite ret_bind_. reflexivity.
    Qed.

    Fact compose_den_lift {A B C}: forall (ab: den A B) (g:B -> C),
        eq_den (ab >=> lift_den g)
               (fun a => ITree.map g (ab a)).
    Proof.
      intros; intro a.
      unfold ITree.map.
      apply eutt_bind.
      reflexivity.
      intro; reflexivity.
    Qed.

    (** *** [sum_elim] lemmas *)

    Fact compose_sum_elim {A B C D} (ac : den A C) (bc : den B C) (cd : den C D) :
      sum_elim ac bc >=> cd ⩰ sum_elim (ac >=> cd) (bc >=> cd).
    Proof.
      intros; intros []; 
        (unfold ITree.map; simpl; apply eutt_bind; reflexivity).
    Qed.      

    Fact lift_sum_elim {A B C} (ac : A -> C) (bc : B -> C) :
      sum_elim (lift_den ac) (lift_den bc) ⩰ lift_den (sum_elim ac bc).
    Proof.
      intros []; reflexivity.
    Qed.

    (** *** [Unitors] lemmas *)

    Lemma elim_λ_den {A B: Type}: 
      forall (ab: @den E A (I + B)), ab >=> λ_den ⩰ (fun a: A => ITree.map sum_empty_l (ab a)).
    Proof.
      intros; apply compose_den_lift.
    Qed.

    Lemma elim_λ_den' {A B: Type}:
      forall (f: @den E (I + A) (I + B)),
        λ_den' >=> f ⩰ fun a => f (inr a).
    Proof.
      repeat intro.
      unfold λ_den', ITree.cat, lift_den.
      rewrite ret_bind_; reflexivity.
    Qed.

    Lemma elim_ρ_den' {A B: Type}:
      forall (f: @den E (A + I) (B + I)),
        ρ_den' >=> f ⩰ fun a => f (inl a).
    Proof.
      repeat intro.
      unfold ρ_den', ITree.cat, lift_den.
      rewrite ret_bind_; reflexivity.
    Qed.

    Lemma elim_ρ_den {A B: Type}: 
      forall (ab: @den E A (B + I)), ab >=> ρ_den ⩰ (fun a: A => ITree.map sum_empty_r (ab a)).
    Proof.
      intros; apply compose_den_lift.
    Qed.

    (** *** [tensor] lemmas *)

    Global Instance eq_den_tensor {A B C D}:
      Proper (eq_den ==> eq_den ==> eq_den) (@tensor_den A B C D).
    Proof.
      intros ac ac' eqac bd bd' eqbd. 
      unfold tensor_den.
      rewrite eqac, eqbd; reflexivity.
    Qed.

    Fact tensor_id_lift {A B C} (f : B -> C) :
        (@id_den A) ⊗ (lift_den f) ⩰ lift_den (sum_bimap id f).
    Proof.
      unfold tensor_den.
      rewrite compose_lift_den, id_den_left.
      rewrite lift_sum_elim.
      reflexivity.
    Qed.

    Fact tensor_lift_id {A B C} (f : A -> B) :
      (lift_den f) ⊗ (@id_den C) ⩰ lift_den (sum_bimap f id).
    Proof.
      unfold tensor_den.
      rewrite compose_lift_den, id_den_left.
      rewrite lift_sum_elim.
      reflexivity.
    Qed. 

    Lemma assoc_I {A B}:
      @assoc_den_r A I B >=> id_den ⊗ λ_den ⩰ ρ_den ⊗ id_den. 
    Proof.
      unfold ρ_den,λ_den.
      rewrite tensor_lift_id, tensor_id_lift.
      unfold assoc_den_r.
      rewrite compose_lift_den.
      apply eq_lift_den.
      intros [[|]|]; compute; try reflexivity.
      destruct i.
    Qed.

    Lemma lift_den_id {A: Type}: @id_den A ⩰ lift_den id.
    Proof.
      unfold id_den, lift_den; reflexivity.
    Qed.

    Lemma sum_elim_compose {A B C D F}:
      forall (ac: denE A (C + D)) (bc: denE B (C + D)) (cf: denE C F) (df: denE D F),
        sum_elim ac bc >=> sum_elim cf df ⩰
        sum_elim (ac >=> (sum_elim cf df)) (bc >=> (sum_elim cf df)).
    Proof.
      intros.
      unfold ITree.map.
      intros []; reflexivity.
    Qed.

    Lemma inl_sum_elim {A B C}:
      forall (ac: denE A C) (bc: denE B C),
        lift_den inl >=> sum_elim ac bc ⩰ ac.
    Proof.
      intros.
      unfold ITree.cat, lift_den.
      intros ?.
      rewrite ret_bind_.
      reflexivity. 
    Qed.

    Lemma inr_sum_elim {A B C}:
      forall (ac: denE A C) (bc: denE B C),
        lift_den inr >=> sum_elim ac bc ⩰ bc.
    Proof.
      intros.
      unfold ITree.cat, lift_den.
      intros ?.
      rewrite ret_bind_.
      reflexivity.
    Qed.

    Lemma tensor_den_slide {A B C D}:
      forall (ac: @den E A C) (bd: den B D),
        ac ⊗ bd ⩰ ac ⊗ id_den >=> id_den ⊗ bd.
    Proof.
      intros.
      unfold tensor_den.
      repeat rewrite id_den_left.
      rewrite sum_elim_compose.
      rewrite compose_den_assoc.
      rewrite inl_sum_elim, inr_sum_elim.
      reflexivity.
    Qed.

    Lemma assoc_coherent {A B C D}:
      @assoc_den_r A B C ⊗ @id_den D >=> assoc_den_r >=> id_den ⊗ assoc_den_r ⩰ 
       assoc_den_r >=> assoc_den_r.
    Proof.
      unfold tensor_den, assoc_den_r.
      repeat rewrite id_den_left.
      repeat rewrite compose_sum_elim.
      repeat rewrite compose_lift_den.
      rewrite lift_sum_elim.
      repeat rewrite compose_lift_den.
      rewrite lift_sum_elim.
      apply eq_lift_den.
      intros [[[|]|]|]; reflexivity.
    Qed.

    (** *** [sym] lemmas *)

    Lemma sym_unit_den {A} :
       sym_den >=> λ_den ⩰ @ρ_den A.
    Proof.
      unfold sym_den, ρ_den, λ_den.
      rewrite lift_compose_den.
      intros []; simpl; reflexivity.
    Qed.

    Lemma sym_assoc_den {A B C}:
      @assoc_den_r A B C >=> sym_den >=> assoc_den_r ⩰
      (sym_den ⊗ id_den) >=> assoc_den_r >=> (id_den ⊗ sym_den).
    Proof.
      unfold assoc_den_r, sym_den.
      rewrite tensor_lift_id, tensor_id_lift.
      repeat rewrite compose_lift_den.
      apply eq_lift_den.
      intros [[|]|]; compute; reflexivity.
    Qed.

    Lemma sym_nilpotent {A B: Type}:
      sym_den >=> sym_den ⩰ @id_den (A + B).
    Proof.
      unfold sym_den, id_den.
      rewrite compose_lift_den.
      unfold compose.
      unfold lift_den; intros a.
      setoid_rewrite iso_ff'; reflexivity.
    Qed. 

    Lemma tensor_swap {A B C D} (ab : den A B) (cd : den C D) :
      ab ⊗ cd ⩰ (sym_den >=> cd ⊗ ab >=> sym_den).
    Proof.
      unfold tensor_den.
      unfold sym_den.
      rewrite !(compose_den_lift cd), !(compose_den_lift ab), !lift_compose_den, !compose_den_lift.
      intros []; cbn; rewrite map_map; cbn;
        apply eutt_map; try intros []; reflexivity.
    Qed.

    (** *** [loop] lemmas *)

    Global Instance eq_den_loop {I A B} :
      Proper (eq_den ==> eq_den) (@loop_den I A B).
    Proof.
      repeat intro.
      unfold loop_den.
      apply eutt_loop; [| reflexivity].
      intros ? z ->.
      unfold compose.
      rewrite (H z); reflexivity.
    Qed.

    Lemma bind_map: forall {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z),
        eq_itree eq (ITree.map f (x <- t;; k x)) (x <- t;; ITree.map f (k x)).
    Proof.
      intros.
      unfold ITree.map.
      rewrite bind_bind.
      reflexivity.
    Qed.

    (* Naturality of (loop_den I A B) in A *)
    (* Or more diagrammatically:
[[
        +-----+
        | ### |
        +-###-+I
A----B----###----C
          ###

is equivalent to:

   +----------+
   |      ### |
   +------###-+I
A----B----###----C
          ###

]]
     *)

    Lemma compose_loop {I A B C}:
      forall (bc_: denE (I + B) (I + C)) (ab: denE A B),
        loop_den ((id_den ⊗ ab) >=> bc_) ⩰
                 ab >=> loop_den bc_.
    Proof.
    Admitted.
      

    (* Naturality of (loop_den I A B) in B *)
    (* Or more diagrammatically:
[[
   +-----+
   | ### |
   +-###-+I
A----###----B----C
     ###

is equivalent to:

   +----------+
   | ###      |
   +-###------+I
A----###----B----C
     ###

]]
     *)

    Lemma loop_compose {I A B B'}:
      forall (ab_: denE (I + A) (I + B)) (bc: denE B B'),
        loop_den (ab_ >=> (id_den ⊗ bc)) ⩰
                 loop_den ab_ >=> bc.
    Admitted.

    (* Dinaturality of (loop_den I A B) in I *)

    Lemma loop_rename_internal {I J A B}:
      forall (ab_: denE (I + A) (J + B)) (ji: denE J I),
        loop_den (ab_ >=> (ji ⊗ id_den)) ⩰
        loop_den ((ji ⊗ id_den) >=> ab_).
    Admitted.

    (* Loop over the empty set can be erased *)
    Lemma vanishing_den {A B: Type}:
      forall (f: denE (I + A) (I + B)),
        loop_den f ⩰ λ_den' >=> f >=> λ_den.
    Admitted.

    (* [loop_loop]:

These two loops:

[[
    +----------+
    | +-----+  |
    | | ### |  |
    | +-###-+I |
    +---###----+J
  A-----###-------B
        ###
]]

... can be rewired as a single one:


[[
     +-------+
     |  ###  |
     +--###--+(I+J)
     +--###--+
  A-----###-----B
        ###
]]

     *)

    Lemma loop_loop {I J A B}:
      forall (ab__: denE (I + (J + A)) (I + (J + B))),
        loop_den (loop_den ab__) ⩰
                 loop_den (assoc_den_r >=> ab__ >=> assoc_den_l).
    Admitted.

    Lemma tensor_den_loop {I A B C D}
          (ab : denE (I + A) (I + B)) (cd : denE C D) :
      (loop_den ab) ⊗ cd ⩰
                    loop_den (assoc_den_l >=> (ab ⊗ cd) >=> assoc_den_r).
    Proof.
    Admitted.

    Lemma yanking_den {A: Type}:
      loop_den sym_den ⩰ @id_den A.
    Admitted.
    (* Lemma loop_relabel {I J A B} *)
    (*       (f : I -> J) {f' : J -> I} *)
    (*       {ISO_f : Iso f f'} *)
    (*       (ab : den (I + A) (I + B)) : *)
    (*   eq_den (loop_den ab) *)
    (*          (loop_den (rewire_den' (sum_bimap f' id) (sum_bimap f id) ab)). *)
    (* Proof. *)
    (* Admitted. *)

  End Laws.
End Den.

Bind Scope den_scope with den.
Infix "⩰" := eq_den (at level 70).
Infix "⊗" := (tensor_den) (at level 30).

Hint Rewrite @compose_den_assoc : lift_den.
Hint Rewrite @tensor_id_lift : lift_den.
Hint Rewrite @tensor_lift_id : lift_den.
Hint Rewrite @lift_sum_elim : lift_den.


