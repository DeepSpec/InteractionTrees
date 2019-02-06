Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib.Structures Require Import
     Monoid.

From ITree Require Import
     Core Morphisms.

(** Sums for extensible event types. *)

Variant prod1 (E1 E2 : Type -> Type) : Type -> Type :=
| pairE : forall {X Y} (e1 : E1 X) (e2 : E2 Y), prod1 E1 E2 (X * Y)%type
.

Variant unitE : Type -> Type := oneE : unitE unit.

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

(* TODO: dependent type propagation
Definition swap1 {A B : Type -> Type} {X Y : Type}
           (ab : prod1 A B (X * Y)) :  prod1 B A (Y * X) := 
*)

Notation "E1 *' E2" := (prod1 E1 E2)
(at level 50, left associativity) : type_scope.


Section Synch.
  (* This version of synchronizing two itrees runs both itrees until either one
     of them returns, in which case its answer is given along with the
     "residual" itree of other thread.  If both trees happen to return
     simultaneously, the pair of the results is gievn.  If either itree produces
     a visible event, the other itree is executed until it too produces an
     event, at which point both events are yielded simultaneously.  If one (or
     both) itrees diverge when theo other is waiting on an event, then the whole
     synchronized itree diverges too.

     Intuitively, this operation pads both itrees so that they have an identical
     number of Tau steps until their next visible event, and if that number
     happens to be infinity, then so be it.  *)

  
  Context {E1 E2 : Type -> Type} {R S : Type}.

  Inductive synch_result :=
  | left_ret (r:R) (t2:itree E2 S) 
  | both_ret (r:R) (s:S)
  | right_ret (t1:itree E1 R) (s:S)
  .           
  
  Definition synch_match
             (synch : itree E1 R -> itree E2 S -> itree (E1 *' E2) synch_result)
             (t1 : itree E1 R)
             (t2 : itree E2 S)
    : itree (E1 *' E2) synch_result :=
    match t1.(observe), t2.(observe) with
    | RetF r, RetF s => Ret (both_ret r s)
    | RetF r, _ => Ret (left_ret r t2)
    | _, RetF s => Ret (right_ret t1 s)
    | TauF t1', TauF t2' => Tau (synch t1' t2')
    | TauF t1', VisF e2 k2 => Tau (synch t1' t2)
    | VisF e1 k1, TauF t2' => Tau (synch t1 t2')
    | VisF e1 k1, VisF e2 k2 =>
      Vis (pairE e1 e2) (fun '(x, y) => synch (k1 x) (k2 y))
    end.

  CoFixpoint synch t1 t2 := synch_match synch t1 t2.
End Synch.

