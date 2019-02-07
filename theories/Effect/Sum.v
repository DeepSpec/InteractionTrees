(** Sums of effects *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Lists.List.

From ITree Require Import
     Basics
     Core.

(** Sums for extensible event types. *)

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).

Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 50, left associativity) : type_scope.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
  (at level 50, left associativity) : type_scope.

Variant emptyE : Type -> Type := .

Module Sum1.

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

(** [Sum1.swap] *)
Definition swap {A B : Type -> Type} : A +' B ~> B +' A :=
  fun _ ab =>
    match ab with
    | inl1 a => inr1 a
    | inr1 b => inl1 b
    end.

(** [Sum1.bimap] *)
Definition bimap {A B C D : Type -> Type}
           (f : A ~> B) (g : B ~> D) : A +' B ~> B +' D :=
  fun _ ab =>
    match ab with
    | inl1 a => inl1 (f _ a)
    | inr1 b => inr1 (g _ b)
    end.

Definition elim {A B C : Type -> Type}
           (f : A ~> C) (g : B ~> C) : A +' B ~> C :=
  fun _ ab =>
    match ab with
    | inl1 a => f _ a
    | inr1 b => g _ b
    end.

End Sum1.
