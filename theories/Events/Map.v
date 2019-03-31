(** * Mutable map *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib Require Import
     Core.RelDec.

From ExtLib.Structures Require
     Functor Monoid Maps.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Interp.Interp
     Events.State.

Import ITree.Basics.Basics.Monads.
(* end hide *)

Section Map.

  Variables (K V : Type).

  Variant mapE : Type -> Type :=
  | Insert : K -> V -> mapE unit
  | Lookup : K -> mapE (option V)
  | Remove : K -> mapE unit
  .

  Definition insert {E} `{mapE -< E} : K -> V -> itree E unit := embed Insert.
  Definition lookup {E} `{mapE -< E} : K -> itree E (option V) := embed Lookup.
  Definition remove {E} `{mapE -< E} : K -> itree E unit := embed Remove.

  Definition lookup_def {E} `{mapE -< E} : K -> V -> itree E V
    := fun k v =>
         ITree.bind (lookup k) (fun ov =>
         Ret (match ov with
              | None => v
              | Some v' => v'
              end)).

  Import Structures.Maps.

  Context {map : Type}.
  Context {M : Map K V map}.

  Definition handle_map {E} : mapE ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | Insert k v => Ret (Maps.add k v env, tt)
      | Lookup k => Ret (env, Maps.lookup k env)
      | Remove k => Ret (Maps.remove k env, tt)
      end.

  Definition run_map {E} : itree (mapE +' E) ~> stateT map (itree E) :=
    interp_state (case_ handle_map pure_state).

End Map.

Arguments insert {K V E _}.
Arguments lookup {K V E _}.
Arguments remove {K V E _}.
Arguments lookup_def {K V E _}.
Arguments run_map {K V map M _} [T].
