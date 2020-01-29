(** * Definition of a functor *)

From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryTheory.

Import CatNotations.
Local Open Scope cat_scope.

Section Functor.

Context
  {obj1 obj2 : Type}
  {C1 : obj1 -> obj1 -> Type}
  {C2 : obj2 -> obj2 -> Type}
  {F : obj1 -> obj2} {fmap : forall a b, C1 a b -> C2 (F a) (F b)}
  `{Eq2 _ C1} `{Id_ _ C1} `{Cat _ C1}
  `{Eq2 _ C2} `{Id_ _ C2} `{Cat _ C2}.

Arguments fmap {a b}.

Class Functor : Prop :=
  { fmap_id : forall a, fmap (id_ a) ⩯ id_ (F a)
  ; fmap_cat : forall a b c (f : C1 a b) (g : C1 b c), fmap (cat f g) ⩯ cat (fmap f) (fmap g)
  ; fmap_proper : forall a b, Proper (eq2 ==> eq2) (@fmap a b)
  }.

End Functor.  

Arguments Functor : clear implicits.
Arguments Functor {_ _} C1 C2 F fmap {_ _ _ _ _ _}.

Section FunctorId.

Context
  {obj : Type} {C1 C2 : obj -> obj -> Type}
  {fmap : forall a b, C1 a b -> C2 a b}
  `{Eq2 _ C1} `{Id_ _ C1} `{Cat _ C1}
  `{Eq2 _ C2} `{Id_ _ C2} `{Cat _ C2}
  {Functor_id : Functor C1 C2 (fun x => x) fmap}.

Lemma fmap_id0 : forall a, fmap _ _ (id_ a) ⩯ id_ a.
Proof. apply fmap_id. Qed.

Lemma fmap_cat0 : forall a b c (f : C1 a b) (g : C1 b c),
    fmap _ _ (f >>> g) ⩯ fmap _ _ f >>> fmap _ _ g.
Proof. apply fmap_cat. Qed.

End FunctorId.
