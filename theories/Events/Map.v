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

  Definition insert {E F} `{mapE +? F -< E} : K -> V -> itree E unit := fun k v => trigger (Insert k v).
  Definition lookup {E F} `{mapE +? F -< E} : K -> itree E (option V) := fun k => trigger (Lookup k).
  Definition remove {E F} `{mapE +? F -< E} : K -> itree E unit := fun k => trigger (Remove k).

  Definition lookup_def {E F} `{mapE +? F -< E} : K -> V -> itree E V
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

  Definition run_map {E F} `{mapE +? E -< F}
    : itree F ~> stateT map (itree E) :=
    interp_state (over handle_map).

End Map.

Arguments insert {K V E F _}.
Arguments lookup {K V E F _}.
Arguments remove {K V E F _}.
Arguments lookup_def {K V E F _}.
Arguments run_map  {K V map M _ _ _} [T].
