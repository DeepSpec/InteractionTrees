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
Arguments inr1 {_ _} [_] _.
Arguments inl1 {_ _} [_] _.


Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 60, right associativity) : type_scope.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
  (at level 50, left associativity) : type_scope.

Variant emptyE : Type -> Type := .

Module Sum1.

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

Definition elim_emptyE {A} : emptyE ~> A :=
  fun X (e : emptyE X) => match e with end.

Definition idE {A : Type -> Type} : A ~> A :=
  fun X (e : A X) => e.

Definition cmpE {A B C : Type -> Type} : (B ~> C) -> (A ~> B) -> (A ~> C) :=
  fun g f X a => g X (f X a).

               
(** [Sum1.swap] *)
Definition swap {A B : Type -> Type} : A +' B ~> B +' A :=
  fun _ ab =>
    match ab with
    | inl1 a => inr1 a
    | inr1 b => inl1 b
    end.

(** [Sum1.bimap] *)
Definition bimap {A B C D : Type -> Type}
           (f : A ~> B) (g : C ~> D) : A +' C ~> B +' D :=
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

(** [Sum1.assoc] *)
Definition assoc {A B C : Type -> Type} : A +' (B  +' C) ~> (A +' B) +' C :=
  fun _ abc =>
    match abc with
    | inl1 a => inl1 (inl1 a)
    | inr1 (inl1 b) => inl1 (inr1 b)
    | inr1 (inr1 c) => inr1 c
    end.

Definition emptyE_left {A : Type -> Type} : emptyE +' A ~> A :=
  elim elim_emptyE idE.

Definition emptyE_right {A : Type -> Type} : A +' emptyE ~> A :=
  elim idE elim_emptyE.

End Sum1.
