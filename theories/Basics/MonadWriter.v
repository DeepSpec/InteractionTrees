(* begin hide *)
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

Definition writerT (W: Type) (M: Type -> Type) (A : Type) : Type :=
  M (prod W A).
Definition writer := prod.

