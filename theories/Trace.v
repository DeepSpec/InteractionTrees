Require Import List.
Import ListNotations.

Require Import ITree.ITree.

Inductive event (E : Effect) : Type :=
| Event : forall e : E, reaction e -> event E.

Arguments Event {E}.

Definition trace (E : Effect) : Type := list (event E).

Inductive is_trace {E : Effect} {R : Type} :
  itree E R -> trace E -> option R -> Prop :=
| TraceEmpty : forall t, is_trace t [] None
| TraceRet : forall r, is_trace (Ret r) [] (Some r)
| TraceTau : forall t tr r_,
  is_trace t tr r_ ->
  is_trace (Tau t) tr r_
| TraceVis : forall (e : E) (x : reaction e) k tr r_,
  is_trace (k x) tr r_ ->
  is_trace (Vis e k) (Event e x :: tr) r_
.

Definition trace_incl {E : Effect} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr r_, is_trace t1 tr r_ -> is_trace t2 tr r_.

(* [step_ ev t' t] if [t] steps to [t'] (read right to left!)
   with visible event [ev]. *) 
Inductive step_ {E : Effect} {R : Type}
          (ev : event E) (t' : itree E R) :
  itree E R -> Prop :=
| StepTau : forall t, step_ ev t' t -> step_ ev t' (Tau t)
| StepVis : forall (e : E) (x : reaction e) k,
    ev = Event e x ->
    t' = k x ->
    step_ ev t' (Vis e k)
.

Definition step {E : Effect} {R : Type}
           (ev : event E) (t t' : itree E R) : Prop :=
  step_ ev t' t.

CoInductive simulates {E : Effect} {R : Type} :
  itree E R -> itree E R -> Prop :=
| SimStep : forall t1 t2,
    (forall ev t1', step ev t1 t1' ->
     exists    t2', step ev t2 t2' /\ simulates t1' t2') ->
    simulates t1 t2.

Theorem simulates_trace_incl {E : Effect} {R : Type} :
  forall t1 t2 : itree E R,
    simulates t1 t2 -> trace_incl t1 t2.
Proof.
Abort.

(* Set-of-traces monad *)
Definition traces (E : Effect) (R : Type) : Type :=
  trace E -> option R -> Prop.

Definition bind_traces {E : Effect} {R S : Type}
           (ts : traces E R) (kts : R -> traces E S) : traces E S :=
  fun tr s_ =>
    (s_ = None /\ ts tr None) \/
    (exists r tr1 tr2,
        tr = tr1 ++ tr2 /\
        ts tr1 (Some r) /\
        kts r tr s_).

Definition ret_traces {E : Effect} {R : Type} :
  R -> traces E R :=
  fun r tr r_ =>
    tr = [] /\ (r_ = None \/ r_ = Some r).
