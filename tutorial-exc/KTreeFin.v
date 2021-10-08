(** * Subcategory of KTrees indexed by finite types *)

(* Definition of the [subpure] function, mapping [sub Fun fin] (functions between finite
   types) to [sub (ktree E) fin] (KTrees between finite types) and proves that
   it commutes with the various combinators from [ITree.Basics.Category].
 *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.CategorySub.

Require Import Fin.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

(* General theory. Functors which preserve coproducts.
   Here we assume that the functor's object mapping is the identity function.
 *)
Section CocartesianFunctor.

Context
  {obj : Type} {C D : obj -> obj -> Type}
  {bif : obj -> obj -> obj}
  `{Eq2 _ C} `{Case _ C bif} `{Inl _ C bif} `{Inr _ C bif}
  `{Eq2 _ D} `{Case _ D bif} `{Inl _ D bif} `{Inr _ D bif}
  {fmap : forall a b, C a b -> D a b}.

Arguments fmap {a b}.

Class CocartesianFunctor : Prop :=
  { fmap_case : forall a b c (f : C a c) (g : C b c),
      fmap (case_ f g) ⩯ case_ (fmap f) (fmap g)
  ; fmap_inl : forall a b,
      fmap (inl_ (a := a) (b := b)) ⩯ inl_
  ; fmap_inr : forall a b,
      fmap (inr_ (a := a) (b := b)) ⩯ inr_
  }.

Context
  `{forall a b, Equivalence (eq2 (C := D) (a := a) (b := b))}
  `{Id_ _ C} `{Cat _ C}
  `{Id_ _ D} `{Cat _ D}
  `{forall a b c, Proper (eq2 ==> eq2 ==> eq2) (cat (C := D) (a := a) (b := b) (c := c))}
  `{@Coproduct _ D _ _ bif _ _ _}
  `{@Functor _ _ C D (fun x => x) (@fmap) _ _ _ _ _ _}
  `{CocartesianFunctor}.

Lemma fmap_swap {n m}
  : fmap swap ⩯ swap (a := n) (b := m).
Proof.
  unfold swap, Swap_Coproduct.
  rewrite fmap_case, fmap_inl, fmap_inr.
  reflexivity.
Qed.

Lemma fmap_bimap {n m p q} (f : C n m) (g : C p q)
  : fmap (bimap f g) ⩯ bimap (fmap f) (fmap g).
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite fmap_case, !fmap_cat0, fmap_inl, fmap_inr.
  reflexivity.
Qed.

Lemma fmap_assoc_l {n m p}
  : fmap (a := (bif n (bif m p))) assoc_l ⩯ assoc_l.
Proof.
  unfold assoc_l, AssocL_Coproduct.
  rewrite !fmap_case, !fmap_cat0, !fmap_inl, !fmap_inr.
  reflexivity.
Qed.

Lemma fmap_assoc_r {n m p}
  : fmap (a := (bif (bif n m) p)) assoc_r ⩯ assoc_r.
Proof.
  unfold assoc_r, AssocR_Coproduct.
  rewrite !fmap_case, !fmap_cat0, !fmap_inl, !fmap_inr.
  reflexivity.
Qed.

End CocartesianFunctor.

Notation Fun_fin := (sub Fun fin).
Notation ktree_fin E := (sub (ktree E) fin).

Section PureKF.

Context {E : Type -> Type}.

Definition subpure {n m} (f : Fun_fin n m) : ktree_fin E n m :=
  subm (pure (unsubm f)).

Global Instance Functor_pure : Functor _ _ _ (@subpure).
Proof.
  constructor; intros.
  - reflexivity.
  - unfold subpure. rewrite fmap_cat, fmap_cat0. reflexivity.
  - hnf; intros. apply Proper_subm, Proper_pure. auto.
Qed.

Global Instance CocartesianFunctor_pure : CocartesianFunctor (fmap := @subpure).
Proof.
  constructor; intros.
  - intros []; cbn.
    unfold unsubm, case_, Case_Kleisli, case_sum, Case_sub, case_.
    unfold cat, Cat_sub, Cat_Fun.
    unfold to_bif, ToBifunctor_ktree_fin, ToBifunctor_Fun_fin.
    rewrite bind_ret_l.
    destruct split_fin_sum; reflexivity.
  - intros ?; cbn. rewrite bind_ret_l. reflexivity.
  - intros ?; cbn; rewrite bind_ret_l; reflexivity.
Qed.

End PureKF.
