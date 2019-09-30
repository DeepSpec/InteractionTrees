(** * Reader *)

(** Immutable environment. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Events.Exception
     Interp.Interp
     Interp.Handler.
(* end hide *)

Section Reader.

Variable (Env : Type).

Variant readerE : Type -> Type :=
| Ask : readerE Env.

Definition ask {E F} `{readerE +? F -< E} : itree E Env :=
  trigger Ask.

Definition eval_reader {E} : Env -> Handler readerE E :=
  fun r _ e =>
    match e with
    | Ask => Ret r
    end.

Definition run_reader {E F} `{readerE +? E -< F} : Env -> itree F ~> itree E :=
  fun r => interp (over (eval_reader r)).

End Reader.

Arguments ask {Env E F _}.
Arguments run_reader {Env E F _} _ _ _.
