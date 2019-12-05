From ITree Require Import
     ITree
     ITreeDefinition
     Interp.Traces.

From Coq Require Import
     Lists.List
     Arith.EqNat
     Arith.PeanoNat
     Program.Equality
     List.

(** * Modeling Concurrency with ITrees (CCS)

    We want to reason about concurrency with ITrees.

    For modeling concurrency, we use Milner's calculus of communicating systems(#)
    (CCS), a predecessor to π-calculus. In CCS, participating processes of a
    concurrent system have indivisible communications that can be composed in
    parallel.

    The primitive in the calculus is a _process_ that can have input and output
    _actions_ in which processes can communicate. Each action has a corresponding
    label, and can act as either an input or output (but not both).
    Processes can only communicate through complementary actions with the same
    label (i.e. same labels with actions of opposing polarity, such that process
    with input action `a` can communicate with a process with output action `a`).


    (#) Milner, R., Communication and Concurrency, 1989.
*)

Import ListNotations.
Set Implicit Arguments.

  (** CCS Operators:

      P := ∅          Empty Process
         | A = P1     Process Identifier *** (TODO)
         | a.P1       Action
         | P1 + P2    Choice (Sum type)
         | P1 ∥ P2    Parallel Composition
         | P1 ∖ a     Restriction *** (TODO)

      * Empty Process
      * Process Identifier: Identifier A refers to process P1. Allows
                            recursive definitions.
      * Action: Process P1 performs an action a. This could be a send or
                receive, depending on the polarity of the action a.
      * Choice : either P1 or P2 will be processed.
      * Parallel Composition: Processes P1 and P2 exist simultaneously
      * Restriction: Hides port a in process P1.
  *)


(** *Denotation of CCS with ITrees *)

Section ccs.

(* We need a decidable equality on labels for the Restriction and Parallel
   Composition operator. *)

Variable A : Type.
Variable A_dec_eq : forall x y: A, {x = y} + {x <> y}.
Variable A_beq : A -> A -> bool. (* Requires A to have a decidable equality *)

Variant Label : Type :=
| In (l : A) : Label
| Out (l : A) : Label.

Theorem label_dec_eq :
  forall x y : Label, {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

(* Denotation of CCS Operators as ITree events. *)
Variant ccsE : Type -> Type :=
| Or (n : nat): ccsE nat (* Note: choices are zero-indexed. *)
| Act : Label -> ccsE unit
| Sync : A -> ccsE unit
| Fail : ccsE void.

Definition ccs := itree ccsE unit.

(** Denotation of basic operations in CCS.
    For now, we reason about finitary ITrees. *)

(* The empty process. *)
Definition zero : ccs := Ret tt.

Definition fail : ccs := Vis Fail (fun x : void => match x with end).

(* Action operators, where l denotes the label. *)
Definition send (l : A) (k : ccs) : ccs := Vis (Act (In l)) (fun _ => k).

Definition recv (l : A) (k : ccs) : ccs := Vis (Act (Out l)) (fun _ => k).

(* Choose operator, where n is the number of choices. *)
Definition pick (n: nat) (k : nat -> ccs) : ccs := Vis (Or n) k.

(* Parallel composition operator (#).

   (#) Follows denotation of CCS parallel composition operator from
       Section 5 Rule IV. (p. 269) of:
       M. Henessy & G. Plotkin, A Term Model for CCS, 1980. *)
(* TODO: Invariant on atomic processes. *)
CoFixpoint par (p1 p2 : ccs) : ccs :=
  let par_left (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | (Vis (Act x) k), _ => Vis (Act x) (fun _ => par (k tt) p2)
    | Vis (Sync a) t1, _ => Vis (Sync a) (fun _ => par (t1 tt) p2)
    | Ret _, _ => p2
    | _, _ => fail
    end
  in let par_right (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | _, (Vis (Act x) k) => Vis (Act x) (fun _ => par p1 (k tt))
    | _, Vis (Sync a) t1 => Vis (Sync a) (fun _ => par p1 (t1 tt))
    | _, Ret _ => p1
    | _, _ => fail
    end
  in let par_comm (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | (Vis (Act (In l1)) k1), (Vis (Act (Out l2)) k2) =>
      if A_beq l1 l2 then Vis (Sync l1) (fun _ => par (k1 tt) (k2 tt)) else fail
    | (Vis (Act (Out l1)) k1), (Vis (Act (In l2)) k2) =>
      if A_beq l1 l2 then Vis (Sync l1) (fun _ => par (k1 tt) (k2 tt)) else fail
    | _, _ => fail
    end
  in
  match p1, p2 with
  | (Vis (Or n1) k1), (Vis (Or n2) k2) =>
      Vis (Or 3) (fun n0 : nat =>
        if beq_nat n0 0 then Vis (Or n1) (fun n11 : nat => par_left (k1 n11) p2)
        else if beq_nat n0 1 then Vis (Or n2) (fun n21 : nat => par_right p1 (k2 n21))
        else Vis (Or (n1 * n2))
                 (fun m => par_comm (k1 (m mod n2)) (k2 (m / n1))))
  | _, _ => fail
  end
.

(* TODO Exercise : State invariant as a coinductive predicate,
and preservation by par. *)

(* To show correctness of our denotation of CCS, we compare
   the trace semantics between this denotation and the
   operational semantics for CCS. *)

(** *Operational Semantics for CCS *)

Section ccs_op.

Inductive ccs_o : Type :=
| Done : ccs_o
| Action : Label -> ccs_o -> ccs_o
| Choice : ccs_o -> ccs_o -> ccs_o
| Par : ccs_o -> ccs_o -> ccs_o
.

(* General transition rules for the Labelled Transition System. *)
Inductive step {l : A} : option Label -> ccs_o -> ccs_o -> Prop :=
| step_Send t :
    step (Some (In l)) (Action (In l) t) t
| step_Recv t :
    step (Some (Out l)) (Action (Out l) t) t
| step_Choice_L u v u' (A' : option Label) :
    step A' u u' -> step A' (Choice u v) u'
| step_Choice_R u v v' (A' : option Label) :
    step A' v v' -> step A' (Choice u v) v'
| step_Par_L u v u' (A' : option Label) :
    step A' u u' -> step A' (Par u v) (Par u' v)
| step_Par_R u v v' (A' : option Label) :
    step A' v v' -> step A' (Par u v) (Par u v')
| step_Par_Comm1 u v u' v' :
    step (Some (In l)) u u' -> step (Some (Out l)) v v' ->
    step None u' v'
| step_Par_Comm2 u v u' v' :
    step (Some (Out l)) u u' -> step (Some (In l)) v v' ->
    step None u' v'
.

End ccs_op.

(* TODO: Change to synchronous version of the LTS.
   obs := Sync (n).
   P -> (a ext) Q is not observed by the trace.
 *)
(** *Synchronous Model of Operational CCS

   In order to get a trace semantics, we need to limit our operational
   semantics to a _synchronous_ model. A synchronous model is where
   the observable events are only on the synchronous actions of the
   transition system. This is desirable because we need a set of
   sequentially observable events which agree to our denotation
   of the CCS. Note that our `par` definition follows a synchronous
   version of the CCS. (i.e. a.b.0 <> b.a.0. In asynchronous CCS,
   a.b.0 = b.a.0, since it needs to consider all the possible interleavings
   of actions.) This motivates our want for a synchronous CCS, where
   traces of operations only contain synchronous events. This is nice also
   because it provides a more stable basis for our future direction of
   extend our denotation to message passing models of concurrency
   (e.g. π-calculus).
*)

(* Trace Semantics. *)

Inductive trace_ob : Type :=
| TNil : trace_ob
| TLabel : Label -> trace_ob -> trace_ob.

(* TODO *)
Inductive is_subtree_ob : ccs_o -> ccs_o -> Prop :=
| SubDone : is_subtree_ob Done Done.

Inductive is_trace_ob : ccs_o -> trace_ob -> Prop :=
| TraceDone :  is_trace_ob (Done) TNil
| TraceAction : forall A c tr, is_trace_ob (Action A c) (TLabel A tr)
| TraceChoice : forall c1 c2 sc1 sc2 tr,
    is_subtree_ob sc1 c1 -> is_subtree_ob sc2 c2 ->
    is_trace_ob sc1 tr -> is_trace_ob sc2 tr ->
    is_trace_ob (Choice c1 c2) tr
| TracePar : forall c1 c2 sc1 sc2 tr,
    is_subtree_ob sc1 c1 -> is_subtree_ob sc2 c2 ->
    is_trace_ob sc1 tr \/ is_trace_ob sc2 tr ->
    is_trace_ob (Par c1 c2) tr
.

(** *Equivalence on Traces

    We defined the trace semantics for our operational semantics above, and
    there is a trace semantics defined for ITrees (in theories.Interp.Traces).

    To show equivalence between these traces, we need to first show
    an equivalence relation between our varying notion of traces.
*)

Arguments trace _ _.
Inductive equiv_traces : trace_ob -> trace -> Prop :=
| TEqNil : equiv_traces TNil TEnd
| TEqRet : forall x, equiv_traces TNil (TRet x)
| TEqEvEnd : forall l,
    equiv_traces (TLabel l TNil) (TEventEnd (Act l))
| TEqEvResp : forall l tro trd,
    equiv_traces tro trd ->
    equiv_traces (TLabel l tro) (@TEventResponse ccsE unit unit (Act l) tt trd)
.

(* Now we can prove trace equivalence between the semantic models. *)
Theorem trace_eq_ob_den :
  (forall td trd, is_trace td trd -> exists to tro, is_trace_ob to tro /\ equiv_traces tro trd)
  /\ (forall to tro, is_trace_ob to tro -> exists td trd, is_trace td trd /\ equiv_traces tro trd).
Proof.
  split.
  - intros td trd H. induction H.
    + exists Done. exists TNil. repeat constructor.
    + exists Done. exists TNil. repeat constructor.
    + remember (observe t) as t'.
      exists
      * inversion H.
  - intros. admit.
Admitted.
