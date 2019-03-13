(** * Sums of indexed types *)

(** In the context of interaction trees, effects can be combined
    using this sum type. *)

(* begin hide *)
From Coq Require Import
     Lists.List.

From ITree Require Import
     Basics.Basics
     Core.ITree.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** Sum of type constructors [Type -> Type].
    [sum1 : (Type -> Type) -> (Type -> Type) -> (Type -> Type)]. *)
Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).
Arguments inr1 {_ _} [_] _.
Arguments inl1 {_ _} [_] _.

(** An infix notation for convenience. *)
Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 60, right associativity) : type_scope.

(** The empty indexed type. *)
Variant void1 : Type -> Type := .

(** This sum type equips the space of indexed functions [_ ~> _] with
    the structure of a cocartesian category, see [Indexed.Function].
 *)
