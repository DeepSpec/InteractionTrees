(** * Exception event *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Interp.Interp.
(* end hide *)

(** Throw exceptions of type [Err]. *)
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.

(** Since the output type of [Throw] is [void], we can make it an action
    with any return type. *)
Definition throw {Err : Type} {E : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : itree E X
  := vis (Throw e) (fun v : void => match v with end).
