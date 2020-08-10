(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Category
     Basics.CategorySub.

Import CatNotations.
Local Open Scope cat.
(* end hide *)

Section CategoryTheory.

  Context
    {obj : Type} {C : obj -> obj -> Type}
    {bif : obj -> obj -> obj}
    {Eq2_C : Eq2 C}
    `{forall a b, Equivalence (eq2 (a := a) (b := b))}
    `{Category obj C (Eq2C := _)}
    `{Coproduct obj C (Eq2_C := _) (Cat_C := _) bif}.

  Lemma aux_app_asm_correct1 (I J A B : obj) :
    (assoc_r >>>
       bimap (id_ I) (assoc_l >>> bimap swap (id_ B) >>> assoc_r) >>>
       assoc_l)
    ⩯ bimap swap (id_ (bif A B)) >>>
      (assoc_r >>>
      (bimap (id_ J) assoc_l >>>
      (assoc_l >>> (bimap swap (id_ B) >>> assoc_r)))).
  Proof. cat_auto. Qed.

  Lemma aux_app_asm_correct2 (I J B D : obj) :
    (assoc_r >>>
             bimap (id_ I) (assoc_l >>> bimap swap (id_ D) >>> assoc_r) >>>
             assoc_l)
      ⩯ assoc_l >>>
      (bimap swap (id_ D) >>>
             (assoc_r >>>
                      (bimap (id_ J) assoc_r >>>
                             (assoc_l >>> bimap swap (id_ (bif B D)))))).
  Proof. cat_auto. Qed.

End CategoryTheory.

(** [(A + B) + (C + D) -> (A + C) + (B + D)]*)
Notation swap4 :=
(assoc_r >>> bimap (id_ _) (assoc_l >>> bimap swap (id_ _) >>> assoc_r) >>> assoc_l).

Require Import KTreeFin.

Lemma subpure_swap4 {E A B C D} :
  subpure (E := E) (n := (A + B) + (C + D)) swap4 ⩯ swap4.
Proof.
  rewrite !fmap_cat0, !fmap_assoc_r, !fmap_assoc_l.
  do 2 (apply category_proper_cat; try reflexivity).
  rewrite fmap_bimap, fmap_id0.
  rewrite fmap_cat0.
  apply (bifunctor_proper_bimap _ _); try reflexivity.
  rewrite fmap_cat0, fmap_assoc_l, fmap_assoc_r, fmap_bimap.
  rewrite fmap_swap, fmap_id0.
  reflexivity.
Qed.
