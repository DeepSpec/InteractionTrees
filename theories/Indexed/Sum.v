(** Sums of effects *)

From Coq Require Import
     Lists.List.

From ITree Require Import
     Basics.Basics
     Core.ITree.

Set Implicit Arguments.
Set Contextual Implicit.

(** Sums for extensible event types. *)

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).
Arguments inr1 {_ _} [_] _.
Arguments inl1 {_ _} [_] _.


Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 60, right associativity) : type_scope.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
  (at level 50, left associativity) : type_scope.

Variant void1 : Type -> Type := .
