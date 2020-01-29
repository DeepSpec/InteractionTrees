(** * Full subcategories *)

(** The category described by a subset of objects of an existing category. *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Category
     CategoryFunctor.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

Set Universe Polymorphism.

Section Subcategory.

(** A function [Embed : sobj -> obj] from some collection of objects [sobj]
    to objects of a category [C] induces a category on [sobj].
    When that function [Embed] is injective, that is a subcategory. *)
Context
  {obj : Type}
  (C : obj -> obj -> Type)
  {sobj : Type}
  (Embed : sobj -> obj).

Definition sub (a b : sobj) : Type := C (Embed a) (Embed b).

Definition subm (a b : sobj) (f : C (Embed a) (Embed b)) : sub a b := f.
Definition unsubm (a b : sobj) (f : sub a b) : C (Embed a) (Embed b) := f.

Context
  {Eq2_C : Eq2 C}
  {Id_C : Id_ C}
  {Cat_C : Cat C}.

Global Instance Eq2_sub : Eq2 sub :=
  fun _ _ => eq2 (C := C).

Global Instance Id_sub : Id_ sub :=
  fun _ => id_ (C := C) _.

Global Instance Cat_sub : Cat sub :=
  fun _ _ _ => cat (C := C).

Context
  (bif : obj -> obj -> obj)
  (sbif : sobj -> sobj -> sobj).

Class ToBifunctor : Type :=
  to_bif : forall a b, C (Embed (sbif a b)) (bif (Embed a) (Embed b)).

Class FromBifunctor : Type :=
  from_bif : forall a b, C (bif (Embed a) (Embed b)) (Embed (sbif a b)).

Arguments to_bif {_ a b}.
Arguments from_bif {_ a b}.

Context
  {ToBif : ToBifunctor}
  {FromBif : FromBifunctor}
  {IsoBif : forall a b, Iso C (a := Embed (sbif a b)) to_bif from_bif}.

Section Bimap.

Context
  {Bimap_C : Bimap C bif}.

Definition Bimap_sub : Bimap sub sbif :=
  fun _ _ _ _ f g => to_bif >>> bimap (C := C) f g >>> from_bif.

End Bimap.

Context
  {Case_C : Case C bif}
  {Inl_C : Inl C bif}
  {Inr_C : Inr C bif}.

Global Instance Case_sub : Case sub sbif :=
  fun _ _ _ f g => to_bif >>> case_ (C := C) f g.

Global Instance Inl_sub : Inl sub sbif :=
  fun _ _ => inl_ (C := C) >>> from_bif.

Global Instance Inr_sub : Inr sub sbif :=
  fun _ _ => inr_ (C := C) >>> from_bif.

Context
  {Iter_C : Iter C bif}.

Global Instance Iter_sub : Iter sub sbif :=
  fun _ _ f => iter (C := C) (cat (C := C) f to_bif).

Section CatLaws.

Context
  {Equivalence_C : forall a b, @Equivalence (C a b) eq2}
  {Category_C : Category C}.

Global Instance Equivalence_sub {a b} : @Equivalence (sub a b) eq2 :=
  Equivalence_C _ _.

Global Instance Category_sub : Category sub.
Proof.
  destruct Category_C; constructor; red; eauto.
  do 2 red. intros. eapply category_proper_cat; eauto.
Qed.

Global Instance Proper_subm {a b} : Proper (eq2 ==> eq2) (subm a b).
Proof. hnf; auto. Qed.

Global Instance Proper_unsubm {a b} : Proper (eq2 ==> eq2) (subm a b).
Proof. hnf; auto. Qed.

Global Instance Functor_unsubm : Functor sub C Embed unsubm.
Proof.
  constructor; reflexivity + typeclasses eauto.
Qed.

End CatLaws.

Ltac unfold_sub :=
  repeat progress (
    try change (eq2 (C := sub) (a := ?a) (b := ?b))
      with (eq2 (C := C) (a := Embed a) (b := Embed b));
    try change (id_ (C := sub) ?a)
      with (id_ (C := C) (Embed a));
    try change (cat (C := sub) (a := ?a) (b := ?b) (c := ?c))
      with (cat (C := C) (a := Embed a) (b := Embed b) (c := Embed c));
    try change (case_ (C := sub) (a := ?a) (b := ?b) (c := ?c) ?f ?g)
      with (to_bif >>> case_ (C := C) (a := Embed a) (b := Embed b) (c := Embed c) f g);
    try change (inl_ (C := sub) (a := ?a) (b := ?b))
      with (inl_ (C := C) (a := Embed a) (b := Embed b) >>> from_bif);
    try change (inr_ (C := sub) (a := ?a) (b := ?b))
      with (inr_ (C := C) (a := Embed a) (b := Embed b) >>> from_bif);
    try change (iter (C := sub) (a := ?a) (b := ?b) ?f)
      with (iter (C := C) (cat (C := C) f to_bif))
  ).


Ltac simpl_bif :=
  try rewrite <- (cat_assoc to_bif from_bif), (semi_iso to_bif from_bif);
  try rewrite <- (cat_assoc from_bif to_bif), (semi_iso from_bif to_bif);
  rewrite cat_id_l.

Section CoproductLaws.

Context
  {Equivalence_C : forall a b, @Equivalence (C a b) eq2}
  {Category_C : Category C}
  {Coproduct_C : Coproduct C bif}.

Global Instance Coproduct_sub : Coproduct sub sbif.
Proof.
  destruct Coproduct_C; constructor; red; intros.
  all: unfold Morphisms.respectful.
  all: unfold_sub.
  all: try rewrite !cat_assoc.
  all: try simpl_bif; eauto.
  - enough (from_bif >>> fg ⩯ case_ (C := C) f g).
    { rewrite <- H1, <- cat_assoc, (semi_iso _ _), cat_id_l. reflexivity. }
    apply case_universal; rewrite <- cat_assoc; eauto.
  - intros. unfold case_, Case_sub.
    apply category_proper_cat. reflexivity.
    eapply coproduct_proper_case; eauto.
Qed.

Lemma bimap_sub_unfold a b c d (f : sub a c) (g : sub b d) :
  eq2 (C := C) (bimap (C := sub) f g)
      (to_bif >>> bimap (C := C) f g >>> from_bif).
Proof.
  unfold bimap at 1, Bimap_Coproduct at 1.
  unfold_sub.
  rewrite <- 2 cat_assoc.
  rewrite <- cat_case. rewrite cat_assoc.
  reflexivity.
Qed.

Context
  {Iterative_C : Iterative C bif}.

Global Instance Iterative_sub : Iterative sub sbif.
Proof.
  constructor; red; intros.
  all: unfold Morphisms.respectful; unfold_sub.
  - rewrite iter_unfold, cat_assoc at 1. reflexivity.
  - rewrite bimap_sub_unfold.
    rewrite !(cat_assoc to_bif).
    rewrite <- (cat_assoc (C := C) f).
    rewrite cat_assoc, (cat_assoc _ from_bif).
    rewrite (semi_iso _ _), cat_id_r.
    rewrite iter_natural.
    reflexivity.
  - rewrite <- !(cat_assoc _ to_bif).
    rewrite !(cat_assoc _ _ to_bif).
    rewrite !cat_case.
    rewrite !(cat_assoc _ from_bif), !(semi_iso _ _), !cat_id_r.
    rewrite iter_dinatural.
    reflexivity.
  - rewrite <- !(cat_assoc _ to_bif).
    rewrite (cat_assoc _ _ to_bif).
    rewrite cat_case, cat_id_l.
    rewrite (cat_assoc _ _ to_bif), (semi_iso _ _), cat_id_r.
    rewrite iter_natural, iter_codiagonal.
    rewrite (cat_assoc _ (bimap _ _)), bimap_case, cat_id_l, cat_id_r.
    reflexivity.
  - intros; unfold iter, Iter_sub.
    apply iterative_proper_iter, category_proper_cat; auto; reflexivity.
Qed.

End CoproductLaws.

End Subcategory.

Arguments subm {obj C sobj Embed a b}.
Arguments unsubm {obj C sobj Embed a b}.
Arguments to_bif {_ C _ _ _ _ _ a b}.
Arguments from_bif {_ C _ _ _ _ _ a b}.
