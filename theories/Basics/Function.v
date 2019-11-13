(** * The Category of Functions *)

(** Definitions to work with Coq functions [A -> B] categorically.
 *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

(** The name of the category. *)
Definition Fun (A B : Type) : Type := A -> B.

(** The identity function, but can sometimes help type inference. *)
Definition apply_Fun {A B : Type} (f : Fun A B) : A -> B := f.

(** Extensional function equality *)
Instance eeq : Eq2 Fun :=
  fun A B f g => forall a : A, f a = g a.

(** Identity function *)
Instance Id_Fun : Id_ Fun :=
  fun A => fun a => a.

(** Function composition *)
Instance Cat_Fun : Cat Fun :=
  fun A B C f g => fun a => g (f a).

(** [void] as an initial object. *)
Instance Initial_void : Initial Fun void :=
  fun _ v => match v : void with end.

(** ** The [sum] coproduct. *)

(** Coproduct elimination *)
Instance case_sum : Case Fun sum :=
  fun {A B C} (f : A -> C) (g : B -> C) (x : A + B) =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

(** Injections *)
Instance sum_inl : Inl Fun sum := @inl.
Instance sum_inr : Inr Fun sum := @inr.
