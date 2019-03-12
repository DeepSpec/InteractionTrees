(** * The Category of Functions

  Definitions to reason about Coq functions [A -> B] categorically.

 *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

Definition Fun (A B : Type) : Type := A -> B.

Definition applyFun {A B : Type} (f : Fun A B) : A -> B := f.

(** Extensional function equality *)
Instance eeq : Eq2 Fun :=
  fun A B f g => forall a : A, f a = g a.

Instance Id_Fun : Id_ Fun :=
  fun A => fun a => a.

Instance Cat_Fun : Cat Fun :=
  fun A B C f g => fun a => g (f a).

(** * [void] as an initial object. *)

Instance Initial_void : Initial Fun void :=
  fun _ v => match v : void with end.

(** * The [sum] coproduct. *)

(** ** Coproduct elimination *)

Instance case_sum : CoprodCase Fun sum :=
  fun {A B C} (f : A -> C) (g : B -> C) (x : A + B) =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

Instance sum_inl : CoprodInl Fun sum := @inl.
Instance sum_inr : CoprodInr Fun sum := @inr.
