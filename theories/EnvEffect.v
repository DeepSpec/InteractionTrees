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
     Core Morphisms OpenSum.


(* Environments ------------------------------------------------------------- *)


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
  
  Definition eval_env {E} : eff_hom_s map envE E := 
    fun _ e env =>
      match e with
      | addE k v => Ret (add k v env, tt)
      | lookupE k => Ret (env, lookup k env)
      | lookupDefaultE k v => Ret (env, match lookup k env with None => v | Some x => x end)
      | removeE k => Ret (remove k env, tt)
      end.

  Definition run_env {E R} (env : map) (t : itree (envE +' E) R)
  : itree E (map * R) :=
    interp_state (into_state eval_env) t env.

End Env.

Arguments env_add {K V E _}.
Arguments env_lookup {K V E _}.
Arguments env_lookupDefault {K V E _}.
Arguments env_remove {K V E _}.
Arguments run_env {K V map M _ _}.



Module FunMap.

  Variables (K V : Type).
  Context {RD : RelDec (@eq K)}.
  Definition map := K -> option V.
  
  Definition fun_empty : map := fun _ => None.

  Definition fun_add (k:K) (v:V) (m:map) :=
    fun k' => if eq_dec k k' then Some v else m k'.

  Definition fun_remove (k:K) (m:map) :=
    fun k' => if eq_dec k k' then None else m k'.

  Definition fun_lookup (k:K) (m:map) := m k.

  Definition fun_union (m1 m2:map) :=
    fun k => match fun_lookup k m1 with
          | None => fun_lookup k m2
          | Some v => Some v
          end.
  
  Global Instance Map_fun : Map K V map := 
    { empty  := fun_empty 
    ; add    := @fun_add 
    ; remove := fun_remove
    ; lookup := fun_lookup
    ; union  := fun_union
    }.
    
End FunMap.

