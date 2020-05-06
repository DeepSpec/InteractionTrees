From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryFunctor.

Import CatNotations.
Local Open Scope cat_scope.

Section Monad.

Context
  {obj : Type}
  {C : obj -> obj -> Type}
  {M : obj -> obj}
  {fmap : forall a b, C a b -> C (M a) (M b)}
  `{Eq2 _ C} `{Id_ _ C} `{Cat _ C}
.

Arguments fmap {a b}.

Class Monad : Prop :=
  {
    monad_functor :> Functor C C M (@fmap);
    ret : forall a, C a (M a);
    bind : forall a b, C (C a (M b)) (M b)
  }.

End Monad.
