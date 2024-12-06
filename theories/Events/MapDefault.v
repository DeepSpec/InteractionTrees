(** * Mutable map whose lookup operation provides a default value.*)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From ExtLib Require Import
     Core.RelDec
     Data.Monads.StateMonad.

From ExtLib.Structures Require
     Functor Monoid Maps.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Basics.Monad
     Indexed.Function
     Indexed.Sum
     Core.ITreeDefinition
     Core.Subevent
     Interp.Interp
     Interp.Handler
     Events.State.

(* end hide *)

Section Map.

  Variables (K V : Type).

  Variant mapE (d:V) : Type -> Type :=
  | Insert : K -> V -> mapE d unit
  | LookupDef : K -> mapE d V
  | Remove : K -> mapE d unit
  .

  Arguments Insert {d}.
  Arguments LookupDef {d}.
  Arguments Remove {d}.
  
  Definition insert {E d} `{(mapE d) -< E} : K -> V -> itree E unit := embed Insert.
  Definition lookup_def {E d} `{(mapE d) -< E} : K -> itree E V := embed LookupDef.
  Definition remove {E d} `{(mapE d) -< E} : K -> itree E unit := embed Remove.

  Import Structures.Maps.

  Context {map : Type}.
  Context {M : Map K V map}.

  Definition lookup_default {K V} `{Map K V} k d m :=
    match Maps.lookup k m with
    | Some v' => v'
    | None => d
    end.
  
  Definition handle_map {E d} : mapE d ~> stateT map (itree E) :=
    fun _ e =>
      match e with
      | Insert k v => mkStateT (fun env => Ret (tt, Maps.add k v env))
      | LookupDef k => mkStateT (fun env => Ret (lookup_default k d env, env))
      | Remove k => mkStateT (fun env => Ret (tt, Maps.remove k env))
      end.

  (* SAZ: I think that all of these [run_foo] functions should be renamed
     [interp_foo].  That would be more consistent with the idea that 
     we define semantics by nested interpretation.  Also, it seems a bit
     strange to define [interp_map] in terms of [interp_state].
  *)
  Definition interp_map {E d} : itree (mapE d +' E) ~> stateT map (itree E) :=
    interp_state (case_ (bif := sum1) (C := IFun) (c := stateT map (itree E))
                        handle_map pure_state).


  (* The appropriate notation of the equivalence on the state associated with
     the MapDefault effects.  Two maps are equivalent if they yield the same
     answers under [lookup_default] *)
  Definition eq_map (d:V) (m1 m2 : map) : Prop :=
    forall k, lookup_default k d m1 = lookup_default k d m2.
  
End Map.

Arguments insert {K V E d _}.
Arguments lookup_def {K V E d _}.
Arguments remove {K V E d _}.
Arguments interp_map {K V map M _ _ } [T].
Arguments eq_map {K V map M d}.
