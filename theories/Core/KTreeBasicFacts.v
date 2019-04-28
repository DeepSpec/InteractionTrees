(** * Theorems about the cocartesian category of KTrees *)

(** Theorems about [loop] are separate, in [ITree.Core.KTreeFacts]. *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Function
     Basics.FunctionFacts
     Core.ITreeDefinition
     Core.KTree
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.

(* end hide *)

Global Instance Equivalence_eq_ktree {E A B} : @Equivalence (ktree E A B) eq2.
Proof.
  split; repeat intro.
  - reflexivity.
  - symmetry; auto.
  - etransitivity; eauto.
Qed.

Section UnfoldLemmas.

Local Opaque ITree.bind' eutt eq_itree.

Lemma assoc_l_itree {E A B C} (x : A + (B + C)) :
  assoc_l_ A B C x ≅ @lift_ktree E (A + (B + C)) _ assoc_l x.
Proof.
  cbv; destruct x as [ | []]; try rewrite bind_ret_; reflexivity.
Qed.

Lemma assoc_r_itree {E A B C} (x : (A + B) + C) :
  assoc_r_ A B C x ≅ @lift_ktree E ((A + B) + C) _ assoc_r x.
Proof.
  cbv; destruct x as [ [] | ]; try rewrite bind_ret_; reflexivity.
Qed.

Lemma assoc_l_ktree {E A B C} :
  assoc_l ⩯ @lift_ktree E (A + (B + C)) _ assoc_l.
Proof.
  cbv; intros [ | [] ]; try rewrite bind_ret_; reflexivity.
Qed.

Lemma assoc_r_ktree {E A B C} :
  assoc_r ⩯ @lift_ktree E ((A + B) + C) _ assoc_r.
Proof.
  intros ?; rewrite <- assoc_r_itree; reflexivity.
Qed.

End UnfoldLemmas.

(** ** Equations *)

Section CategoryLaws.

Context {E : Type -> Type}.

(** *** [compose_ktree] respect eq_ktree *)
Global Instance eq_ktree_compose {A B C} :
  @Proper (ktree E A B -> ktree E B C -> _) (eq2 ==> eq2 ==> eq2) cat.
Proof.
  intros ab ab' eqAB bc bc' eqBC.
  intro a.
  unfold cat, Cat_ktree, ITree.cat.
  rewrite (eqAB a).
  einit. ebind. econstructor; try reflexivity.
  intros; subst. specialize (eqBC u2). efinal.
Qed.

(** *** [compose_ktree] is associative *)
Global Instance CatAssoc_ktree : CatAssoc (ktree E).
Proof.
  intros A B C D f g h a.
  unfold cat, Cat_ktree, ITree.cat.
  rewrite bind_bind.
  reflexivity.
Qed.

(** *** [id_ktree] respect identity laws *)
Global Instance CatIdL_ktree : CatIdL (ktree E).
Proof.
  intros A B f a; unfold cat, Cat_ktree, ITree.cat, id_, Id_ktree.
  rewrite bind_ret. reflexivity.
Qed.

Global Instance CatIdR_ktree : CatIdR (ktree E).
Proof.
  intros A B f a; unfold cat, Cat_ktree, ITree.cat, id_, Id_ktree.
  rewrite <- (bind_ret2 (f a)) at 2.
  reflexivity.
Qed.

Global Instance Category_ktree : Category (ktree E).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance InitialObject_ktree : InitialObject (ktree E) void.
Proof. intros A f []. Qed.

End CategoryLaws.

(** *** [lift] properties *)

Section LiftLaws.

Context {E : Type -> Type}.

Local Open Scope cat.

(** *** [lift_ktree] is well-behaved *)

Global Instance eq_lift_ktree {A B} :
  Proper (eq2 ==> eq2) (@lift_ktree E A B).
Proof.
  repeat intro.
  unfold lift_ktree.
  erewrite (H a); reflexivity.
Qed.

Lemma lift_ktree_id {A: Type}: (id_ A ⩯ @lift_ktree E A A (id_ A))%cat.
Proof.
  reflexivity.
Qed.

Fact compose_lift_ktree {A B C} (ab : A -> B) (bc : B -> C) :
  (@lift_ktree E _ _ ab >>> lift_ktree bc ⩯ lift_ktree (ab >>> bc))%cat.
Proof.
  intros a.
  unfold lift_ktree, cat, Cat_ktree, ITree.cat.
  rewrite bind_ret_.
  reflexivity.
Qed.

Fact compose_lift_ktree_l {A B C D} (f: A -> B) (g: B -> C) (k: ktree E C D) :
  (lift_ktree f >>> (lift_ktree g >>> k) ⩯ lift_ktree (g ∘ f) >>> k)%cat.
Proof.
  rewrite <- cat_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
  typeclasses eauto.
Qed.

Fact compose_lift_ktree_r {A B C D} (f: B -> C) (g: C -> D) (k: ktree E A B) :
  ((k >>> lift_ktree f) >>> lift_ktree g ⩯ k >>> lift_ktree (g ∘ f))%cat.
Proof.
  rewrite cat_assoc.
  rewrite compose_lift_ktree.
  reflexivity.
  typeclasses eauto.
Qed.

Fact lift_compose_ktree {A B C}: forall (f:A -> B) (bc: ktree E B C),
    lift_ktree f >>> bc ⩯ fun a => bc (f a).
Proof.
  intros; intro a.
  unfold lift_ktree, cat, Cat_ktree, ITree.cat.
  rewrite bind_ret_. reflexivity.
Qed.

Fact compose_ktree_lift {A B C}: forall (ab: ktree E A B) (g:B -> C),
    (ab >>> lift_ktree g)
  ⩯ (fun a => ITree.map g (ab a)).
Proof.
  reflexivity.
Qed.

Lemma sym_ktree_unfold {A B}:
  @lift_ktree E (A + B) (B + A) swap ⩯ swap.
Proof.
  intros []; reflexivity.
Qed.

End LiftLaws.

Section MonoidalCategoryLaws.

Context {E : Type -> Type}.

Local Open Scope cat.

Fact lift_case_sum {A B C} (ac : A -> C) (bc : B -> C) :
    case_ (@lift_ktree E _ _ ac) (lift_ktree bc)
  ⩯ lift_ktree (case_ ac bc).
Proof.
  intros []; reflexivity.
Qed.

(** *** [Unitors] lemmas *)

(* This is probably generalizable into [Basics.Category]. *)

Lemma unit_l_ktree (A : Type) :
  unit_l ⩯ @lift_ktree E _ A unit_l.
Proof.
  intros [[]|]. reflexivity.
Qed.

Lemma unit_l'_ktree (A : Type) :
  unit_l' ⩯ @lift_ktree E A (void + A) unit_l'.
Proof.
  reflexivity.
Qed.

Lemma unit_r_ktree (A : Type) :
  unit_r ⩯ @lift_ktree E _ A unit_r.
Proof.
  intros [|[]]. reflexivity.
Qed.

Lemma unit_r'_ktree (A : Type) :
  unit_r' ⩯ @lift_ktree E A (A + void) unit_r'.
Proof.
  reflexivity.
Qed.

Lemma case_l_ktree {A B: Type} (ab: @ktree E A (void + B)) :
  ab >>> unit_l ⩯ (fun a: A => ITree.map unit_l (ab a)).
Proof.
  rewrite unit_l_ktree.
  reflexivity.
Qed.

Lemma case_l_ktree' {A B: Type} (f: @ktree E (void + A) (void + B)) :
  unit_l' >>> f ⩯ fun a => f (inr a).
Proof.
  rewrite unit_l'_ktree.
  intro. unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  rewrite bind_ret_; reflexivity.
Qed.

Lemma case_r_ktree' {A B: Type} (f: @ktree E (A + void) (B + void)) :
  unit_r' >>> f ⩯ fun a => f (inl a).
Proof.
  rewrite unit_r'_ktree.
  intro. unfold cat, Cat_ktree, ITree.cat, lift_ktree.
  rewrite bind_ret_; reflexivity.
Qed.

Lemma case_r_ktree {A B: Type} (ab: @ktree E A (B + void)) :
  ab >>> unit_r ⩯ (fun a: A => ITree.map unit_r (ab a)).
Proof.
  rewrite unit_r_ktree.
  reflexivity.
Qed.

(** *** [bimap] lemmas *)
Local Opaque paco2.
Local Opaque eutt loop ITree.bind'.

Fact bimap_id_lift {A B C} (f : B -> C) :
  bimap (id_ A) (@lift_ktree E _ _ f) ⩯ lift_ktree (bimap (id_ A) f).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_ktree.
  reflexivity.
  all: typeclasses eauto.
Qed.

Fact bimap_lift_id {A B C} (f : A -> B) :
  bimap (@lift_ktree E _ _ f) (id_ C) ⩯ lift_ktree (bimap f id).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_ktree.
  reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance Coproduct_ktree : Coproduct (ktree E) sum.
Proof.
  constructor.
  - intros a b c f g.
    unfold inl_, Inl_ktree.
    rewrite lift_compose_ktree.
    reflexivity.
  - intros a b c f g.
    unfold inr_, Inr_ktree.
    rewrite lift_compose_ktree.
    reflexivity.
  - intros a b c f g fg Hf Hg [x | y].
    + unfold inl_, Inl_ktree in Hf.
      rewrite lift_compose_ktree in Hf.
      specialize (Hf x). simpl in Hf. rewrite Hf. reflexivity.
    + unfold inr_, Inr_ktree in Hg.
      rewrite lift_compose_ktree in Hg.
      specialize (Hg y). simpl in Hg. rewrite Hg. reflexivity.
Qed.

End MonoidalCategoryLaws.
