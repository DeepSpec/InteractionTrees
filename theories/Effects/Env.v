Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib Require Import
     Core.RelDec.

From ExtLib.Structures Require Import
     Functor Monoid Maps.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Indexed.Sum
     Indexed.OpenSum
     Interp.Interp
     Effects.State.

Import ITree.Basics.Basics.Monads.


(* Environment Effects ------------------------------------------------------ *)


Section Env.

  Variables (K V : Type).

  Variant envE : Type -> Type :=
  | addE : K -> V -> envE unit
  | lookupE : K -> envE (option V)
  | lookupDefaultE : K -> V -> envE V
  | removeE : K -> envE unit
  .

  (* SAZ: there is a naming convention clash here between the Map class and our Effects conventions *)
  Definition env_add {E} `{envE -< E} : K -> V -> itree E unit := embed addE.
  Definition env_lookup {E} `{envE -< E} : K -> itree E (option V) := embed lookupE.
  Definition env_lookupDefault {E} `{envE -< E} : K -> V -> itree E V := embed lookupDefaultE.
  Definition env_remove {E} `{envE -< E} : K -> itree E unit := embed removeE.


  Context {map : Type}.
  Context {M:Map K V map}.

  Definition eval_env {E} : envE ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | addE k v => Ret (add k v env, tt)
      | lookupE k => Ret (env, lookup k env)
      | lookupDefaultE k v => Ret (env, match lookup k env with None => v | Some x => x end)
      | removeE k => Ret (remove k env, tt)
      end.

  Definition run_env {E} : itree (envE +' E) ~> stateT map (itree E) :=
    interp_state (into_state eval_env).

End Env.

Arguments env_add {K V E _}.
Arguments env_lookup {K V E _}.
Arguments env_lookupDefault {K V E _}.
Arguments env_remove {K V E _}.
Arguments run_env {K V map M _}.
