(** * Reader *)

(** Immutable environment. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import List.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Interp.Interp
     Interp.Handler.
(* end hide *)

Section Reader.

Variable (Env : Type).

Variant readerE : Type -> Prop :=
| Ask : readerE Env.

Definition ask {E} `{readerE -< E} : itree E Env :=
  trigger Ask.

Definition eval_reader {E} : Env -> Handler readerE E :=
  fun r _ e =>
    match e with
    | Ask => Ret r
    end.

Definition run_reader {E} : Env -> itree (readerE +' E) ~> itree E :=
  fun r => interp (case_ (eval_reader r) (id_ _)).

End Reader.

Arguments ask {Env E _}.
Arguments run_reader {Env E} _ _ _.
