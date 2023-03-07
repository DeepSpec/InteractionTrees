(** * Writer *)

(** Output events. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     List.
Import ListNotations.

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

Import Basics.Basics.Monads.
(* end hide *)

(* begin extlib inline *)
Section unit_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable u : T.
  Variable equ : T -> T -> Prop.

  Class LeftUnit : Type :=
    lunit : forall a, equ (op u a) a.

  Class RightUnit : Type :=
    runit : forall a, equ (op a u) a.

End unit_op.

Section comm_op.
  Context {T U : Type}.
  Variable op : T -> T -> U.
  Variable equ : U -> U -> Prop.

  Class Commutative : Type :=
    commut : forall a b, equ (op a b) (op b a).

End comm_op.

Section assoc_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable equ : T -> T -> Prop.

  Class Associative : Type :=
    assoc : forall a b c, equ (op (op a b) c) (op a (op b c)).

End assoc_op.

Section Monoid.
  Universe u.
  Variable S : Type@{u}.

  Record Monoid@{} : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

  Class MonoidLaws@{} (M : Monoid) : Type :=
  { monoid_assoc :> Associative M.(monoid_plus) eq
  ; monoid_lunit :> LeftUnit M.(monoid_plus) M.(monoid_unit) eq
  ; monoid_runit :> RightUnit M.(monoid_plus) M.(monoid_unit) eq
  }.

End Monoid.

(* end extlib inline *)

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
  := fun _ e s =>
       match e with
       | Tell w => Ret (w :: s, tt)
       end.

Definition run_writer_list_state {W E}
  : itree (writerE W +' E) ~> stateT (list W) (itree E)
  := interp_state (case_ handle_writer_list pure_state).

Arguments run_writer_list_state {W E} [T].

(** Returns the outputs in order: the first output at the head, the last
    output and the end of the list. *)
Definition run_writer_list {W E}
  : itree (writerE W +' E) ~> writerT (list W) (itree E)
  := fun _ t =>
       ITree.map (fun wsx => (rev' (fst wsx), snd wsx))
                 (run_writer_list_state t []).

Arguments run_writer_list {W E} [T].

(** When [W] is a monoid, we can also use that to append the outputs together. *)

Definition handle_writer {W E} (Monoid_W : Monoid W)
  : writerE W ~> stateT W (itree E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (monoid_plus Monoid_W s w, tt)
       end.

Definition run_writer {W E} (Monoid_W : Monoid W)
  : itree (writerE W +' E) ~> writerT W (itree E)
  := fun _ t =>
       interp_state (case_ (handle_writer Monoid_W) pure_state) t
                    (monoid_unit Monoid_W).

Arguments run_writer {W E} Monoid_W [T].
