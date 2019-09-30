(** * Mutable map whose lookup operation provides a default value.*)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

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

  Variant mapE (d:V) : Type -> Type :=
  | Insert : K -> V -> mapE d unit
  | LookupDef : K -> mapE d V
  | Remove : K -> mapE d unit
  .

  Arguments Insert {d}.
  Arguments LookupDef {d}.
  Arguments Remove {d}.

  Definition insert {E d F} `{(mapE d) +? F -< E} : K -> V -> itree E unit := fun k v => trigger (Insert k v).
  Definition lookup_def {E d F} `{(mapE d) +? F -< E} : K -> itree E V := fun k => trigger (LookupDef k).
  Definition remove {E d F} `{(mapE d) +? F -< E} : K -> itree E unit := fun k => trigger (Remove k).

  Import Structures.Maps.

  Context {map : Type}.
  Context {M : Map K V map}.

  Definition lookup_default {K V} `{Map K V} k d m :=
    match Maps.lookup k m with
    | Some v' => v'
    | None => d
    end.

  Definition handle_map {E d} : mapE d ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | Insert k v => Ret (Maps.add k v env, tt)
      | LookupDef k => Ret (env, lookup_default k d env)
      | Remove k => Ret (Maps.remove k env, tt)
      end.

  (* SAZ: I think that all of these [run_foo] functions should be renamed
     [interp_foo].  That would be more consistent with the idea that 
     we define semantics by nested interpretation.  Also, it seems a bit
     strange to define [interp_map] in terms of [interp_state].
  *)

  Definition interp_map {E d F} `{mapE d +? F -< E}
    : itree E ~> stateT map (itree F) :=
    interp_state (over handle_map).

  (* The appropriate notation of the equivalence on the state associated with
     the MapDefault effects.  Two maps are equivalent if they yield the same
     answers under [lookup_default] *)
  Definition eq_map (d:V) (m1 m2 : map) : Prop :=
    forall k, lookup_default k d m1 = lookup_default k d m2.

End Map.

Arguments insert {K V E d _ _}.
Arguments lookup_def {K V E d _ _}.
Arguments remove {K V E d _ _}.
Arguments interp_map {K V map M _ _ _ _} [T].
Arguments eq_map {K V map M d}.
