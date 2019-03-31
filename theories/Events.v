(** * Standard event types *)

(* begin hide *)
From ITree.Events Require
     State
     Reader
     Writer
     Exception
     Nondeterminism
     Map
     Concurrency
     Dependent.
(* end hide *)

(** ** State *)

(**
[[
Variant stateE (S : Type) : Type -> Type :=
| Get : stateE S S
| Put : S -> stateE S unit.
]]
 *)

(** ** Reader *)

(**
[[
Variant readerE (R : Type) : Type -> Type :=
| Ask : readerE R R.
]]
 *)

(** ** Writer *)

(**
[[
Variant writerE (W : Type) : Type -> Type :=
| Tell : W -> writerE W unit.
]]
 *)

(** ** Exception *)

(**
[[
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.
]]
 *)

(** ** Nondeterminism *)

(**
[[
Variant nondetE : Type -> Type :=
| Or : nondetE bool.
]]
 *)

(** ** Map *)

(**
[[
Variant mapE (K V : Type) : Type -> Type :=
| Insert : K -> V -> mapE unit
| Lookup : K -> mapE (option V)
| Remove : K -> mapE unit
.
]]
 *)

(** ** Concurrency *)

(**
[[
Inductive spawnE (E : Type -> Type) : Type -> Type :=
| Spawn : itree (spawnE E +' E) unit -> spawnE E unit.
]]
 *)

(** ** Dependent *)

(**
[[
 Variant depE {I : Type} (F : I -> Type) : Type -> Type :=
| Dep (i : I) : depE F (F i).
]]
 *)
