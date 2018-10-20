(* We can view an [itree] as a generalized state machine,
   where at every step it either returns ([Ret]), steps silently
   ([Tau]), or perfoms some effect ([Vis]), moving to a new
   state depending on the environment's response. In other words,
   instead of a tree, we define a tuple
   [(S : Type, s : S, step : S -> output S)] for some functor
   [output] which is the sum of the above alternatives. *)

(* + No coinduction

   - Less efficiently executable (every [bind] grows the state type)
 *)

(* That tuple can be given the type
   [{ S : Type & S * (S -> output S) }], which is another
   representation of the final coalgebra of the functor [output].
   A basic theory of final coalgebras is in the module
   [ITree.CoAlgebra]. *)

From ExtLib.Structures Require Import
     Functor Applicative Monad.

From ITree Require Import
     CoAlgebra Effect.

Set Implicit Arguments.
Set Contextual Implicit.

(* [St]: State type ([S] is already used by [nat].) *)
Variant output (E : Effect) (R : Type) (St : Type) : Type :=
| Ret : R -> output E R St
| Tau : St -> output E R St
| Vis : forall e : E, (reaction e -> St) -> output E R St
.

Arguments Ret {E R St}.
Arguments Tau {E R St}.
Arguments Vis {E R St}.

Module Output.

(* Change the output state type using [f : St1 -> St2], and if
   the output is a [Ret q] for some [q : Q], get the output of
   the continuation [k q : output E R St2]. *)
Definition bind {St1 St2 E Q R}
           (f : St1 -> St2)
           (o : output E Q St1)
           (k : Q -> output E R St2) : output E R St2 :=
  match o with
  | Ret q => k q
  | Tau s => Tau (f s)
  | Vis e h => Vis e (fun x => f (h x))
  end.

(* Change the output state type. *)
Definition map {St1 St2 E R}
           (f : St1 -> St2)
           (o : output E R St1) : output E R St2 :=
  bind f o Ret.

(* Equivalence of outputs, lifting equivalence of states. *)
Inductive eq {E : Effect} {R : Type} (St1 St2 : Type)
          (eq_St : St1 -> St2 -> Prop) :
  output E R St1 -> output E R St2 -> Prop :=
| eq_Ret : forall r, eq eq_St (Ret r) (Ret r)
| eq_Tau : forall s1 s2,
    eq_St s1 s2 ->
    eq eq_St (Tau s1) (Tau s2)
| eq_Vis : forall e k1 k2,
    (forall x : reaction e, eq_St (k1 x) (k2 x)) ->
    eq eq_St (Vis e k1) (Vis e k2)
.

Global Instance Functor_output {E R} : Functor (output E R) := {|
  fmap _ _ := map;
|}.

End Output.

(* Alternative to [itrees]. *)
Definition machine (E : Effect) (R : Type) : Type := nu (output E R).

Module Machine.

(* Two machines are equivalent if they simulate each other
   (produce the same outputs). *)
Definition eq {E R} : machine E R -> machine E R -> Prop :=
  Nu.eq Output.eq.

(* The state type of a machine. *)
Definition type {E R} : machine E R -> Type :=
  Nu.type.

(* The initial state of a machine. *)
Definition state {E R} (m : machine E R) : Machine.type m :=
  Nu.state m.

(* The step function of a machine. *)
Definition step {E R} (m : machine E R) :
  Machine.type m -> output E R (Machine.type m) :=
  Nu.step m.

(* Run the first step of a machine. *)
Definition step_once {E R} (m : machine E R) :
  output E R (Machine.type m) :=
  Nu.step_once m.

Lemma step_state {E R} (m : machine E R) :
  step m (state m) = step_once m.
Proof. apply Nu.step_state. Qed.

(* Can't write [machine E R -> output E R (machine E R)] because
   of universe inconsistency... *)
Definition run {E R} :
  nu (output E R) -> output E R (nu (output E R)) :=
  Nu.run.

(*
Definition run2 {E R} :
  nu (output E R) -> output E R (machine E R) :=
  Nu.run.
*)

Definition ret {E R} (r : R) : machine E R :=
  Nu tt (fun _ => Ret r).

Definition bind {E Q R}
           (m : machine E Q) (k : Q -> machine E R) :=
  let mtype :=
      (Machine.type m + { q : Q & Machine.type (k q) })%type in
  let mstate := inl (Machine.state m) in
  let wrap_sk (q : Q) (s : Machine.type (k q)) : mtype :=
      inr (existT _ q s) in
  let mstep (s : mtype) :=
      match s with
      | inl sm => Output.bind inl
          (Machine.step m sm)
          (fun q => Output.map (wrap_sk q) (Machine.step_once (k q)))
      | inr (existT _ q sk) =>
        Output.map (wrap_sk q) (Machine.step (k q) sk)
      end in
  Nu mstate mstep.

Global Instance Monad_machine {E} : Monad (machine E) := {|
  Monad.ret _ := ret;
  Monad.bind _ _ := bind;
|}.

End Machine.
