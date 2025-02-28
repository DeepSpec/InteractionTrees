(** * Sums of indexed types *)

(** In the context of interaction trees, events can be combined
    using this sum type. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** Sum of type constructors [Type -> Type].

    [sum1 : (Type -> Type) -> (Type -> Type) -> (Type -> Type)]. *)
Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).
Arguments inr1 {E1 E2} [X].
Arguments inl1 {E1 E2} [X].

(** An infix notation for convenience. *)
Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 59, right associativity) : type_scope.

(** The empty indexed type. *)
Variant void1 : Type -> Prop := .

(** This sum type equips the space of indexed functions [_ ~> _] with
    the structure of a cocartesian category, see [Indexed.Function].
 *)

(* Eliminate [void1]. *)
Polymorphic Definition elim_void1@{u v} {E : Type@{u} -> Type@{v}}
  : forall T : Type@{u}, void1 T -> E T :=
  fun T (v : void1 T) => match v with end.
