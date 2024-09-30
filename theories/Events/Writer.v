(** * Writer *)

(** Output events. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     List.
Import ListNotations.

From ExtLib Require Import
     Data.List
     Data.Monads.StateMonad
     Data.Monads.WriterMonad
     Structures.Functor
     Structures.Monad
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.MonadState
     Indexed.Function
     Indexed.Sum
     Core.ITreeDefinition
     Core.Subevent
     Interp.Interp
     Interp.Handler
     Events.State.

(* end hide *)

(** Event to output values of type [W]. *)
Variant writerE (W : Type) : Type -> Type :=
| Tell : W -> writerE W unit.

(** Output action. *)
Definition tell {W E} `{writerE W -< E} : W -> itree E unit :=
  fun w => trigger (Tell w).

(** One interpretation is to accumulate outputs in a list. *)

(** Note that this handler appends new outputs to the front of the list. *)
Definition handle_writer_list {W E}
  : writerE W ~> stateT (list W) (itree E)
  := fun _ e =>
       match e with
       | Tell w => mkStateT (fun s => Ret (tt, w :: s))
       end.

(* not sure why case_ requires the manual parameters *)
Definition run_writer_list_state {W E}
  : itree (writerE W +' E) ~> stateT (list W) (itree E)
  := interp_state (case_ (bif := sum1) (c := stateT (list W) (itree E))
                         handle_writer_list pure_state).

Arguments run_writer_list_state {W E} [T].

(** Returns the outputs in order: the first output at the head, the last
    output and the end of the list. *)
Definition run_writer_list {W E}
  : itree (writerE W +' E) ~> stateT (list W) (itree E)
  := fun _ t =>
       mkStateT (fun _ => ITree.map (fun wsx => (fst wsx, rev' (snd wsx)))
                                    (runStateT (run_writer_list_state t) [])).

Arguments run_writer_list {W E} [T].

(** When [W] is a monoid, we can also use that to append the outputs together. *)

Definition handle_writer {W E} `{Monoid_W : Monoid W}
  : writerE W ~> writerT Monoid_W (itree E)
  := fun _ e =>
       match e with
       | Tell w => MonadWriter.tell w
       end.

Definition pure_writer {W E} `{Monoid_W : Monoid W}
  : E ~> writerT Monoid_W (itree E)
  := fun _ e =>
      mkWriterT Monoid_W
        (Vis e (fun x => Ret (PPair.ppair x (monoid_unit Monoid_W)))).

(* not sure why case_ requires the manual parameters *)
Definition run_writer {W E} (Monoid_W : Monoid W)
  : itree (writerE W +' E) ~> writerT Monoid_W (itree E)
  := interp (M := writerT Monoid_W (itree E))
            (case_ (bif := sum1) (c := writerT Monoid_W (itree E))
                   handle_writer pure_writer).

Arguments run_writer {W E} Monoid_W [T].
