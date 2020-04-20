From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Functor
     Basics.Monad.

Import CatNotations.
Import MonadNotation.
Local Open Scope cat_scope.
Local Open Scope cat.
Local Open Scope monad_scope.

Definition identityT (M: Type -> Type) (a: Type) : Type := a.
Definition identity (a : Type) : Type := a.


