From ITree Require Import
     ITree
     OpenSum
     Fix
     FixFacts
     Basics_Functions.

From Coq Require Import
     Program
     Morphisms.

(** * Category of denotations *)
Inductive done : Set := Done : done.
Definition den {E: Type -> Type} A B : Type := A -> itree E (B + done).
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
    Definition compose_den {A B C} (ab : denE A B) (bc : denE B C) : @denE A C :=
      fun a => ob <- ab a ;;
               match ob with
               | inl b => bc b
               | inr d => Ret (inr d)
               end.

    (* Identities *)
    Definition id_den {A} : denE A A := fun a => Ret (inl a).

    (* Utility function to lift a pure computation into den *)
    Definition lift_den {A B} (f : A -> B) : denE A B := fun a => Ret (inl (f a)).

    (* Tensor product *)
    (* Tensoring on objects is simply the sum type constructor *)
    Definition tensor_den {A B C D}
               (ab : denE A B) (cd : denE C D) : den (A + C) (B + D) :=
      sum_elim (compose_den ab (lift_den inl)) (compose_den cd (lift_den inr)).

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
      (I + A -> itree E ((I + B) + done)) -> A -> itree E (B + done) :=
      fun body => loop (compose (ITree.map sum_assoc_r) body).

  End Structure.

  Infix ">=>" := compose_den (at level 50, left associativity).
  Infix "⊗" := (tensor_den) (at level 30).

  Section Facts.

    (** *** [compose_den] respect eq_den *)
    Global Instance eq_den_compose {A B C} :
      Proper (eq_den ==> eq_den ==> eq_den) (@compose_den A B C).
    Proof.
      intros ab ab' eqAB bc bc' eqBC.
      intro a.
      unfold compose_den.
      rewrite (eqAB a).
      apply eutt_bind; try reflexivity.
      intros []; try reflexivity.
      rewrite (eqBC b); reflexivity.
    Qed.

    (** *** [compose_den] is associative *)
    Lemma compose_den_assoc {A B C D}
          (ab : den A B) (bc : den B C) (cd : den C D) :
      ((ab >=> bc) >=> cd) ⩰ (ab >=> (bc >=> cd)).
    Proof.
      intros a.
      unfold compose_den.
      rewrite bind_bind.
      apply eutt_bind; try reflexivity.
      intros []; try reflexivity.
      rewrite ret_bind; reflexivity.
    Qed.

    (** *** [id_den] respect identity laws *)
    Lemma id_den_left {A B}: forall (f: denE A B),
        id_den >=> f ⩰ f.
    Proof.
      intros f a; unfold compose_den, id_den; rewrite ret_bind; reflexivity. 
    Qed.

    Lemma id_den_right {A B}: forall (f: denE A B),
        f >=> id_den ⩰ f.
    Proof.
      intros f a; unfold compose_den, id_den.
      rewrite <- (bind_ret (f a)) at 2.
      apply eutt_bind; [reflexivity | intros []; reflexivity].
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
      unfold lift_den, compose_den.
      rewrite ret_bind.
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

    Fact lift_den_lift_den {A B C} (f: A -> B) (g: B -> C) :
      lift_den f >=> lift_den g ⩰ lift_den (g ∘ f).
    Proof.
      intros a.
      unfold lift_den, compose_den.
      rewrite ret_bind.
      reflexivity.
    Qed.

    Fact lift_compose_den {A B C}: forall (f:A -> B) (bc: den B C),
        lift_den f >=> bc ⩰ fun a => bc (f a).
    Proof.
      intros; intro a.
      unfold lift_den, compose_den.
      rewrite ret_bind; reflexivity.
    Qed.

    Fact compose_den_lift {A B C}: forall (ab: den A B) (g:B -> C),
        eq_den (ab >=> lift_den g)
               (fun a => ITree.map (sum_bimap g id) (ab a)).
    Proof.
      intros; intro a.
      unfold compose_den.
      unfold ITree.map.
      apply eutt_bind.
      reflexivity.
      intros []; reflexivity.
    Qed.

    (** *** [sum_elim] lemmas *)

    Fact compose_sum_elim {A B C D} (ac : den A C) (bc : den B C) (cd : den C D) :
      sum_elim ac bc >=> cd ⩰ sum_elim (ac >=> cd) (bc >=> cd).
    Proof.
      intros; intros []; 
        (unfold compose_den; simpl; apply eutt_bind; [reflexivity | intros []; reflexivity]).
    Qed.      

    Fact lift_sum_elim {A B C} (ac : A -> C) (bc : B -> C) :
      sum_elim (lift_den ac) (lift_den bc) ⩰ lift_den (sum_elim ac bc).
    Proof.
      intros []; reflexivity.
    Qed.

    (** *** [tensor] lemmas *)

    Lemma tensor_swap {A B C D} (ab : den A B) (cd : den C D) :
      ab ⊗ cd ⩰ (lift_den sum_comm >=> cd ⊗ ab >=> lift_den sum_comm).
    Proof.
      unfold tensor_den.
      rewrite !(compose_den_lift cd), !(compose_den_lift ab), !lift_compose_den, !compose_den_lift.
      intros []; cbn; rewrite map_map; cbn;
        apply eutt_map; try intros []; reflexivity.
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

    (** *** [loop] lemmas *)

    Global Instance eq_den_loop {I A B} :
      Proper (eq_den ==> eq_den) (@loop_den I A B).
    Proof.
    Admitted.     

    (* Should be a consequence of the others. *)
    Lemma seq_loop_l_seq {A B C I}
          (ab : den (I + A) (I + B)) (bc : den B C) :
       loop_den ab >=> bc ⩰
       loop_den (ab >=> tensor_den id_den bc).
    Proof.
    Admitted.

    (* Should be a consequence of the others *)
    Lemma seq_loop_r_seq {A B C I}
          (ab : den A B) (bc : den (I + B) (I + C)) :
      ab >=> loop_den bc ⩰
      loop_den (tensor_den id_den ab >=> bc).
    Proof.
    Admitted.

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

    (* I do not see a way to avoid the use of lift_den. *)

    Notation rewire_den f g ab :=
      (lift_den f >=> ab >=> lift_den g) (only parsing).

    Lemma loop_loop {I J A B}:
      forall (ab__: denE (I + (J + A)) (I + (J + B))),
        loop_den (loop_den ab__) ⩰
        loop_den (rewire_den sum_assoc_r sum_assoc_l ab__).
    Admitted.

    Lemma tensor_den_loop {I A B C D}
          (ab : denE (I + A) (I + B)) (cd : denE C D) :
        (loop_den ab) ⊗ cd ⩰
        loop_den (rewire_den sum_assoc_l sum_assoc_r (ab ⊗ cd)).
    Proof.
    Admitted.

    (* Lemma loop_relabel {I J A B} *)
    (*       (f : I -> J) {f' : J -> I} *)
    (*       {ISO_f : Iso f f'} *)
    (*       (ab : den (I + A) (I + B)) : *)
    (*   eq_den (loop_den ab) *)
    (*          (loop_den (rewire_den' (sum_bimap f' id) (sum_bimap f id) ab)). *)
    (* Proof. *)
    (* Admitted. *)

  End Facts.
End Den.

Bind Scope den_scope with den.
Infix "⩰" := eq_den (at level 70).
Infix ">=>" := compose_den (at level 50, left associativity).
Infix "⊗" := (tensor_den) (at level 30).

Hint Rewrite @compose_den_assoc : lift_den.
Hint Rewrite @lift_den_lift_den : lift_den.
Hint Rewrite @compose_lift_den_l : lift_den.
Hint Rewrite @tensor_id_lift : lift_den.
Hint Rewrite @tensor_lift_id : lift_den.
Hint Rewrite @lift_sum_elim : lift_den.
Hint Rewrite @compose_lift_den : lift_den.


