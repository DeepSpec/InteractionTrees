(** * The Category of Continuation Trees *)

(** The Kleisli category of ITrees. *)

(* begin hide *)
From ITree Require Import
     ITree
     OpenSum
     Fix
     FixFacts
     Basics_Functions.

From Coq Require Import
     Program
     Morphisms.
(* end hide *)

Definition ktree (E: Type -> Type) (A B : Type) : Type
  := A -> itree E B.
(* ktree can represent both blocks (A -> block B) and asm (asm A B). *)

Bind Scope ktree_scope with ktree.

(* (@ktree E) forms a traced monoidal category, i.e. a symmetric monoidal one with a loop operator *)
(* Obj ≅ Type *)
(* Arrow: A -> B ≅ terms of type (ktree A B) *)

(** ** KTree equivalence *)
Section Equivalence.

Context {E : Type -> Type}.

(* We work up to pointwise eutt *)
Definition eq_ktree {A B} (d1 d2 : ktree E A B) :=
  (forall a, eutt eq (d1 a) (d2 a)).

Global Instance Equivalence_eq_ktree {A B} : Equivalence (@eq_ktree A B).
Proof.
  split.
  - intros ab a; reflexivity.
  - intros ab ab' eqAB a; symmetry; auto.
  - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
Qed.

Global Instance eq_ktree_elim {A B C} :
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@sum_elim A B (itree E C)).
Proof.
  repeat intro. destruct a; unfold sum_elim; auto.
Qed.

End Equivalence.

Infix "⩯" := eq_ktree (at level 70).

(** *** Conversion to [itree] *)
(** A trick to allow rewriting with eq_ktree in pointful contexts. *)

Definition to_itree {E} (f : @ktree E unit unit) : itree E unit := f tt.

Global Instance Proper_to_itree {E} :
  Proper (eq_ktree ==> eutt eq) (@to_itree E).
Proof.
  repeat intro.
  apply H.
Qed.

Lemma fold_to_itree {E} (f : @ktree E unit unit) : f tt = to_itree f.
Proof. reflexivity. Qed.


(** ** Categorical operations *)

Section Operations.

Context {E : Type -> Type}.

(* Utility function to lift a pure computation into ktree *)
Definition lift_ktree {A B} (f : A -> B) : ktree E A B := fun a => Ret (f a).

(** *** Category *)

(** Identity morphism *)
Definition id_ktree {A} : ktree E A A := fun a => Ret a.

(** Composition is [ITree.cat], denoted as [>=>]. *)

(** *** Symmetric monoidal category *)

(** Monoidal unit *)
Definition I: Type := Empty_set.

(** Tensor product *)
(* Tensoring on objects is given by the coproduct *)
Definition tensor_ktree {A B C D}
           (ab : ktree E A B) (cd : ktree E C D)
  : ktree E (A + C) (B + D)
  := sum_elim (ab >=> lift_ktree inl) (cd >=> lift_ktree inr).

(* Left and right unitors *)
Definition λ_ktree  {A: Type}: ktree E (I + A) A := lift_ktree sum_empty_l.
Definition λ_ktree' {A: Type}: ktree E A (I + A) := lift_ktree inr.
Definition ρ_ktree  {A: Type}: ktree E (A + I) A := lift_ktree sum_empty_r.
Definition ρ_ktree' {A: Type}: ktree E A (A + I) := lift_ktree inl.

(* Associators *)
Definition assoc_ktree_l {A B C: Type}: ktree E (A + (B + C)) ((A + B) + C) := lift_ktree sum_assoc_l.
Definition assoc_ktree_r {A B C: Type}: ktree E ((A + B) + C) (A + (B + C)) := lift_ktree sum_assoc_r.

(* Symmetry *)
Definition sym_ktree {A B: Type}: ktree E (A + B) (B + A) := lift_ktree sum_comm.

(** Traced monoidal category *)

(* The trace is [Fix.loop].

   A [box : ktree (I + A) (I + B)] is a circuit, drawn below as ###,
   with two input wires labeled by I and A, and two output wires
   labeled by I and B.

   The [loop_ktree : ktree (I + A) (I + B) -> ktree A B] combinator closes
   the circuit, linking the box with itself by plugging the I output
   back into the input.

     +-----+
     | ### |
     +-###-+I
  A----###----B
       ###

 *)

End Operations.

Infix "⊗" := (tensor_ktree) (at level 30).

(** ** Equations *)

Section CategoryLaws.

Context {E : Type -> Type}.

(** *** [compose_ktree] respect eq_ktree *)
Global Instance eq_ktree_compose {A B C} :
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@ITree.cat E A B C).
Proof.
  intros ab ab' eqAB bc bc' eqBC.
  intro a.
  unfold ITree.cat.
  rewrite (eqAB a).
  apply eutt_bind; try reflexivity.
  intro b; rewrite (eqBC b); reflexivity.
Qed.

(** *** [compose_ktree] is associative *)
Lemma compose_ktree_assoc {A B C D}
      (ab : ktree E A B) (bc : ktree E B C) (cd : ktree E C D) :
  ((ab >=> bc) >=> cd) ⩯ (ab >=> (bc >=> cd)).
Proof.
  intros a.
  unfold ITree.cat.
  rewrite bind_bind.
  apply eutt_bind; try reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Lemma id_ktree_left {A B}: forall (f: ktree E A B),
    id_ktree >=> f ⩯ f.
Proof.
  intros f a; unfold ITree.cat, id_ktree.
  rewrite itree_eta; rewrite ret_bind. rewrite <- itree_eta; reflexivity.
Qed.

Lemma id_ktree_right {A B}: forall (f: ktree E A B),
    f >=> id_ktree ⩯ f.
Proof.
  intros f a; unfold ITree.cat, id_ktree.
  rewrite <- (bind_ret (f a)) at 2.
  reflexivity.
Qed.

End CategoryLaws.

(** *** [lift] properties *)

Section LiftLaws.

Context {E : Type -> Type}.

(** *** [lift_ktree] is well-behaved *)

Global Instance eq_lift_ktree {A B} :
  Proper (eeq ==> eq_ktree) (@lift_ktree E A B).
Proof.
  repeat intro.
  unfold lift_ktree.
  erewrite (H a); reflexivity.
Qed.

Lemma lift_ktree_id {A: Type}: @id_ktree E A ⩯ lift_ktree id.
Proof.
  unfold id_ktree, lift_ktree; reflexivity.
Qed.

Fact compose_lift_ktree {A B C} (ab : A -> B) (bc : B -> C) :
  (@lift_ktree E _ _ ab >=> lift_ktree bc) ⩯ (lift_ktree (bc ∘ ab)).
Proof.
  intros a.
  unfold lift_ktree, ITree.cat.
  rewrite ret_bind_.
  reflexivity.
Qed.

Fact compose_lift_ktree_l {A B C D} (f: A -> B) (g: B -> C) (k: ktree E C D) :
  (lift_ktree f >=> (lift_ktree g >=> k)) ⩯ (lift_ktree (g ∘ f) >=> k).
Proof.
  rewrite <- compose_ktree_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
Qed.

Fact compose_lift_ktree_r {A B C D} (f: B -> C) (g: C -> D) (k: ktree E A B) :
  ((k >=> lift_ktree f) >=> lift_ktree g) ⩯ (k >=> lift_ktree (g ∘ f)).
Proof.
  rewrite compose_ktree_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
Qed.

Fact lift_compose_ktree {A B C}: forall (f:A -> B) (bc: ktree E B C),
    lift_ktree f >=> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold lift_ktree, ITree.cat.
  rewrite ret_bind_. reflexivity.
Qed.

Fact compose_ktree_lift {A B C}: forall (ab: ktree E A B) (g:B -> C),
    eq_ktree (ab >=> lift_ktree g)
             (fun a => ITree.map g (ab a)).
Proof.
  intros; intro a.
  unfold ITree.map.
  apply eutt_bind.
  reflexivity.
  intro; reflexivity.
Qed.

Lemma sym_ktree_unfold {A B}:
  lift_ktree sum_comm ⩯ @sym_ktree E A B.
Proof.
  reflexivity.
Qed.

End LiftLaws.

Section MonoidalCategoryLaws.

Context {E : Type -> Type}.

(** *** [associators]  *)
Lemma assoc_lr {A B C} :
  @assoc_ktree_l E A B C >=> assoc_ktree_r ⩯ id_ktree.
Proof.
  unfold assoc_ktree_l, assoc_ktree_r.
  rewrite compose_lift_ktree.
  intros [| []]; reflexivity.
Qed.

Lemma assoc_rl {A B C} :
  @assoc_ktree_r E A B C >=> assoc_ktree_l ⩯ id_ktree.
Proof.
  unfold assoc_ktree_l, assoc_ktree_r.
  rewrite compose_lift_ktree.
  intros [[]|]; reflexivity.
Qed.

(** *** [sum_elim] lemmas *)

Fact compose_sum_elim {A B C D} (ac : ktree E A C) (bc : ktree E B C) (cd : ktree E C D) :
  sum_elim ac bc >=> cd ⩯ sum_elim (ac >=> cd) (bc >=> cd).
Proof.
  intros; intros [];
    (unfold ITree.map; simpl; apply eutt_bind; reflexivity).
Qed.

Fact lift_sum_elim {A B C} (ac : A -> C) (bc : B -> C) :
    sum_elim (@lift_ktree E _ _ ac) (lift_ktree bc)
  ⩯ lift_ktree (sum_elim ac bc).
Proof.
  intros []; reflexivity.
Qed.

(** *** [Unitors] lemmas *)

(* TODO: replacing l by λ breaks PG (retracts like crazy, or if you go too far it can't retract at all from the second lemma) (ρ is fine, interestingly) *)
Lemma elim_l_ktree {A B: Type} (ab: @ktree E A (I + B)) :
  ab >=> λ_ktree ⩯ (fun a: A => ITree.map sum_empty_l (ab a)).
Proof.
  intros; apply compose_ktree_lift.
Qed.

Lemma elim_l_ktree' {A B: Type} (f: @ktree E (I + A) (I + B)) :
  λ_ktree' >=> f ⩯ fun a => f (inr a).
Proof.
  repeat intro.
  unfold λ_ktree', ITree.cat, lift_ktree.
  rewrite ret_bind_; reflexivity.
Qed.

Lemma elim_ρ_ktree' {A B: Type} (f: @ktree E (A + I) (B + I)) :
  ρ_ktree' >=> f ⩯ fun a => f (inl a).
Proof.
  repeat intro.
  unfold ρ_ktree', ITree.cat, lift_ktree.
  rewrite ret_bind_; reflexivity.
Qed.

Lemma elim_ρ_ktree {A B: Type} (ab: @ktree E A (B + I)) :
  ab >=> ρ_ktree ⩯ (fun a: A => ITree.map sum_empty_r (ab a)).
Proof.
  intros; apply compose_ktree_lift.
Qed.

(** *** [tensor] lemmas *)

Global Instance eq_ktree_tensor {A B C D}:
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@tensor_ktree E A B C D).
Proof.
  intros ac ac' eqac bd bd' eqbd.
  unfold tensor_ktree.
  rewrite eqac, eqbd; reflexivity.
Qed.

Fact tensor_id_lift {A B C} (f : B -> C) :
  (@id_ktree E A) ⊗ (lift_ktree f) ⩯ lift_ktree (sum_bimap id f).
Proof.
  unfold tensor_ktree.
  rewrite compose_lift_ktree, id_ktree_left.
  rewrite lift_sum_elim.
  reflexivity.
Qed.

Fact tensor_lift_id {A B C} (f : A -> B) :
  (lift_ktree f) ⊗ (@id_ktree E C) ⩯ lift_ktree (sum_bimap f id).
Proof.
  unfold tensor_ktree.
  rewrite compose_lift_ktree, id_ktree_left.
  rewrite lift_sum_elim.
  reflexivity.
Qed.

Lemma tensor_id {A B} :
  id_ktree ⊗ id_ktree ⩯ @id_ktree E (A + B).
Proof.
  unfold tensor_ktree, ITree.cat, id_ktree.
  intros []; cbn; rewrite ret_bind_; reflexivity.
Qed.

Lemma assoc_I {A B}:
  @assoc_ktree_r E A I B >=> id_ktree ⊗ λ_ktree ⩯ ρ_ktree ⊗ id_ktree.
Proof.
  unfold ρ_ktree,λ_ktree.
  rewrite tensor_lift_id, tensor_id_lift.
  unfold assoc_ktree_r.
  rewrite compose_lift_ktree.
  apply eq_lift_ktree.
  intros [[|]|]; compute; try reflexivity.
  destruct i.
Qed.

Lemma cat_tensor {A1 A2 A3 B1 B2 B3}
      (f1 : ktree E A1 A2) (f2 : ktree E A2 A3)
      (g1 : ktree E B1 B2) (g2 : ktree E B2 B3) :
  (f1 ⊗ g1) >=> (f2 ⊗ g2) ⩯ (f1 >=> f2) ⊗ (g1 >=> g2).
Proof.
  unfold tensor_ktree, ITree.cat, lift_ktree; simpl.
  intros []; simpl;
    rewrite !bind_bind; setoid_rewrite ret_bind_; reflexivity.
Qed.

Lemma sum_elim_compose {A B C D F}
      (ac: ktree E A (C + D)) (bc: ktree E B (C + D))
      (cf: ktree E C F) (df: ktree E D F) :
    sum_elim ac bc >=> sum_elim cf df
  ⩯ sum_elim (ac >=> (sum_elim cf df)) (bc >=> (sum_elim cf df)).
Proof.
  intros.
  unfold ITree.map.
  intros []; reflexivity.
Qed.

Lemma inl_sum_elim {A B C} (ac: ktree E A C) (bc: ktree E B C) :
  lift_ktree inl >=> sum_elim ac bc ⩯ ac.
Proof.
  intros.
  unfold ITree.cat, lift_ktree.
  intros ?.
  rewrite ret_bind_.
  reflexivity.
Qed.

Lemma inr_sum_elim {A B C} (ac: ktree E A C) (bc: ktree E B C) :
  lift_ktree inr >=> sum_elim ac bc ⩯ bc.
Proof.
  intros.
  unfold ITree.cat, lift_ktree.
  intros ?.
  rewrite ret_bind_.
  reflexivity.
Qed.

Lemma tensor_ktree_slide {A B C D} (ac: ktree E A C) (bd: ktree E B D) :
  ac ⊗ bd ⩯ ac ⊗ id_ktree >=> id_ktree ⊗ bd.
Proof.
  intros.
  unfold tensor_ktree.
  repeat rewrite id_ktree_left.
  rewrite sum_elim_compose.
  rewrite compose_ktree_assoc.
  rewrite inl_sum_elim, inr_sum_elim.
  reflexivity.
Qed.

Lemma assoc_coherent_r {A B C D}:
    @assoc_ktree_r E A B C ⊗ @id_ktree E D
      >=> assoc_ktree_r
      >=> id_ktree ⊗ assoc_ktree_r
  ⩯ assoc_ktree_r >=> assoc_ktree_r.
Proof.
  unfold tensor_ktree, assoc_ktree_r.
  repeat rewrite id_ktree_left.
  repeat rewrite compose_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  apply eq_lift_ktree.
  intros [[[|]|]|]; reflexivity.
Qed.

Lemma assoc_coherent_l {A B C D}:
    @id_ktree E A ⊗ @assoc_ktree_l E B C D
      >=> assoc_ktree_l
      >=> assoc_ktree_l ⊗ id_ktree
  ⩯ assoc_ktree_l >=> assoc_ktree_l.
Proof.
  unfold tensor_ktree, assoc_ktree_l.
  repeat rewrite id_ktree_left.
  repeat rewrite compose_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  repeat rewrite compose_lift_ktree.
  rewrite lift_sum_elim.
  apply eq_lift_ktree.
  intros [|[|[|]]]; reflexivity.
Qed.

(** *** [sym] lemmas *)

Lemma sym_unit_ktree {A} :
  sym_ktree >=> λ_ktree ⩯ @ρ_ktree E A.
Proof.
  unfold sym_ktree, ρ_ktree, λ_ktree.
  rewrite lift_compose_ktree.
  intros []; simpl; reflexivity.
Qed.

Lemma sym_assoc_ktree {A B C}:
    @assoc_ktree_r E A B C >=> sym_ktree >=> assoc_ktree_r
  ⩯ (sym_ktree ⊗ id_ktree) >=> assoc_ktree_r >=> (id_ktree ⊗ sym_ktree).
Proof.
  unfold assoc_ktree_r, sym_ktree.
  rewrite tensor_lift_id, tensor_id_lift.
  repeat rewrite compose_lift_ktree.
  apply eq_lift_ktree.
  intros [[|]|]; compute; reflexivity.
Qed.

Lemma sym_nilpotent {A B: Type}:
  sym_ktree >=> sym_ktree ⩯ @id_ktree E (A + B).
Proof.
  unfold sym_ktree, id_ktree.
  rewrite compose_lift_ktree.
  unfold compose.
  unfold lift_ktree; intros a.
  setoid_rewrite iso_ff'; reflexivity.
Qed.

Lemma tensor_swap {A B C D} (ab : ktree E A B) (cd : ktree E C D) :
  ab ⊗ cd ⩯ (sym_ktree >=> cd ⊗ ab >=> sym_ktree).
Proof.
  unfold tensor_ktree.
  unfold sym_ktree.
  rewrite !(compose_ktree_lift cd), !(compose_ktree_lift ab), !lift_compose_ktree, !compose_ktree_lift.
  intros []; cbn; rewrite map_map; cbn;
    apply eutt_map; try intros []; reflexivity.
Qed.

End MonoidalCategoryLaws.

(** *** Traced monoidal categories *)

Section TraceLaws.

Context {E : Type -> Type}.

(** *** [loop] lemmas *)

Global Instance eq_ktree_loop {I A B} :
  Proper (eq_ktree ==> eq_ktree) (@loop E I A B).
Proof.
  repeat intro; apply eutt_loop; auto.
Qed.

(* Naturality of (loop_ktree I A B) in A *)
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

Lemma compose_loop {I A B C}
      (bc_: ktree E (I + B) (I + C)) (ab: ktree E A B) :
    loop ((id_ktree ⊗ ab) >=> bc_)
  ⩯ ab >=> loop bc_.
Proof.
  intros a.
  rewrite (loop_natural_l ab bc_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold tensor_ktree, sym_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, id_ktree, lift_ktree; simpl.
  - rewrite bind_bind, ret_bind_; reflexivity.
  - rewrite bind_bind, map_bind.
    setoid_rewrite ret_bind_; reflexivity.
Qed.

(* Naturality of (loop I A B) in B *)
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

Lemma loop_compose {I A B B'}
      (ab_: ktree E (I + A) (I + B)) (bc: ktree E B B') :
    loop (ab_ >=> (id_ktree ⊗ bc))
  ⩯ loop ab_ >=> bc.
Proof.
  intros a.
  rewrite (loop_natural_r bc ab_ a).
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold tensor_ktree, sym_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, id_ktree, lift_ktree; simpl.
  - apply eutt_bind; [reflexivity | intros []; simpl].
    rewrite ret_bind_; reflexivity.
    reflexivity.
  - apply eutt_bind; [reflexivity | intros []; simpl].
    rewrite ret_bind_; reflexivity.
    reflexivity.
Qed.

(* Dinaturality of (loop I A B) in I *)

Lemma loop_rename_internal {I J A B}
      (ab_: ktree E (I + A) (J + B)) (ji: ktree E J I) :
    loop (ab_ >=> (ji ⊗ id_ktree))
  ⩯ loop ((ji ⊗ id_ktree) >=> ab_).
Proof.
  unfold tensor_ktree, ITree.cat, lift_ktree, sum_elim.

  assert (EQ:forall (x: J + B),
             match x with
             | inl a => a0 <- ji a;; Ret (inl a0)
             | inr b => a <- id_ktree b;; Ret (inr a)
             end ≈
                 match x with
                 | inl a => Tau (ITree.map (@inl I B) (ji a))
                 | inr b => Ret (inr b)
                 end).
  {
    intros [].
    symmetry; apply tau_eutt.
    unfold id_ktree.
    rewrite ret_bind_; reflexivity.
  }
  intros ?.
  setoid_rewrite EQ.
  rewrite loop_dinatural.
  apply eutt_loop; [intros [] | reflexivity].
  all: unfold id_ktree.
  all: repeat rewrite bind_bind.
  2: repeat rewrite ret_bind_; reflexivity.
  apply eutt_bind; [reflexivity | intros ?].
  apply eutt_bind; [| intros ?; reflexivity].
  apply tau_eutt.
Qed.

(* Loop over the empty set can be erased *)
Lemma vanishing_ktree {A B: Type} (f: ktree E (I + A) (I + B)) :
  loop f ⩯ λ_ktree' >=> f >=> λ_ktree.
Proof.
  intros a.
  rewrite vanishing1.
  unfold λ_ktree,λ_ktree'.
  unfold ITree.cat, ITree.map, lift_ktree.
  rewrite bind_bind.
  rewrite ret_bind_.
  reflexivity.
Qed.

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

Lemma loop_loop {I J A B} (ab__: ktree E (I + (J + A)) (I + (J + B))) :
    loop (loop ab__)
  ⩯ loop (assoc_ktree_r >=> ab__ >=> assoc_ktree_l).
Proof.
  intros a.
  rewrite vanishing2.
  apply eutt_loop; [intros [[]|] | reflexivity].
  all: unfold ITree.map, ITree.cat, assoc_ktree_r, assoc_ktree_l, lift_ktree; cbn.
  all: rewrite bind_bind.
  all: rewrite ret_bind_.
  all: reflexivity.
Qed.

Lemma fold_map {R S}:
  forall (f: R -> S) (t: itree E R),
    (x <- t;; Ret (f x)) ≅ (ITree.map f t).
Proof.
  intros; reflexivity.
Qed.

Lemma tensor_ktree_loop {I A B C D}
      (ab : ktree E (I + A) (I + B)) (cd : ktree E C D) :
    (loop ab) ⊗ cd
  ⩯ loop (assoc_ktree_l >=> (ab ⊗ cd) >=> assoc_ktree_r).
Proof.
  unfold tensor_ktree, ITree.cat, assoc_ktree_l, assoc_ktree_r, lift_ktree, sum_elim.
  intros []; simpl.
  all:setoid_rewrite bind_bind.
  all:setoid_rewrite ret_bind_.
  all:rewrite fold_map.
  1:rewrite (@superposing1 E A B I C D).
  2:rewrite (@superposing2 E A B I C D).
  all:unfold sum_bimap, ITree.map, sum_assoc_r,sum_elim; cbn.
  all:apply eutt_loop; [intros [| []]; cbn | reflexivity].
  all: setoid_rewrite bind_bind.
  all:setoid_rewrite ret_bind_.
  all:reflexivity.
Qed.

Lemma yanking_ktree {A: Type}:
  loop sym_ktree ⩯ @id_ktree E A.
Proof.
  unfold sym_ktree, lift_ktree.
  intros ?; rewrite yanking.
  apply tau_eutt.
Qed.

Lemma loop_rename_internal' {I J A B} (ij : ktree E I J) (ji: ktree E J I)
      (ab_: @ktree E (I + A) (I + B)) :
  (ij >=> ji) ⩯ id_ktree ->
    loop ((ji ⊗ id_ktree) >=> ab_ >=> (ij ⊗ id_ktree))
  ⩯ loop ab_.
Proof.
  intros Hij.
  rewrite loop_rename_internal.
  rewrite <- compose_ktree_assoc.
  rewrite cat_tensor.
  rewrite Hij.
  rewrite id_ktree_left.
  rewrite tensor_id.
  rewrite id_ktree_left.
  reflexivity.
Qed.

End TraceLaws.

Hint Rewrite @compose_ktree_assoc : lift_ktree.
Hint Rewrite @tensor_id_lift : lift_ktree.
Hint Rewrite @tensor_lift_id : lift_ktree.
Hint Rewrite @lift_sum_elim : lift_ktree.

(* Here we show that we can implement [ITree.cat] using
   [tensor_ktree], [loop], and composition with the monoidal
   natural isomorphisms. *)
Section CatFromLoop.

Variable E : Type -> Type.

Theorem cat_from_loop {A B C} (ab : ktree E A B) (bc : ktree E B C) :
  loop (sym_ktree >=> ab ⊗ bc) ⩯ ab >=> bc.
Proof.
  rewrite tensor_ktree_slide.
  rewrite <- compose_ktree_assoc.
  rewrite loop_compose.
  rewrite tensor_swap.
  repeat rewrite <- compose_ktree_assoc.
  rewrite sym_nilpotent, id_ktree_left.
  rewrite compose_loop.
  erewrite yanking_ktree.
  rewrite id_ktree_right.
  reflexivity.
Qed.

End CatFromLoop.
