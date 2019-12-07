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

From Paco Require Import paco.

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

Definition A_beq (a1 a2 : A): bool := true. (* TODO *)

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
(* TODO: State invariant on atomic processes? *)
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

Coercion is_true : bool >-> Sortclass.

Notation ccs' := (itreeF ccsE unit ccs).

(** *Shape Invariant

   The tree should alternate in depth starting with a (Vis (Or _) _)
   node, then a non-(Vis (Or _) _) node, and keep alternating until
   it finds a leaf.

   The equational properties of CCS structural congruences state that
   any level of the tree can be defined as a sum. This shape invariant
   is necessary for our parallel composition operator, and we define this
   shape as the canonical shape for our denotation of CCS with ITrees.
 *)

(* Functorial definition of shape invariant.
   The definition takes two parameters :
   - [b] is a boolean flag indicating whether or not it is currently
     at an [Or] event level of the tree.
   - [inv] is the currently built coinductive relation.
 *)
Inductive shape_invF (b : bool) (inv : bool -> ccs -> Prop) : bool -> ccs' -> Prop :=
| ShapeRet (CHECK: not b):
    shape_invF b inv b (RetF tt)
| ShapeOr k
          (CHECK : b)
          (n1 n2 : nat)
          (H : n1 <= n2)
          (REL : inv (negb b) (k n1)):
    shape_invF b inv (negb b) (VisF (Or n2) k)
| ShapeAct a k
           (CHECK : not b)
           (REL : inv (negb b) (k tt)):
    shape_invF b inv (negb b) (VisF (Act a) k)
| ShapeSync a k
            (CHECK : not b)
            (REL : inv (negb b) (k tt)):
    shape_invF b inv (negb b) (VisF (Sync a) k)
| ShapeTau p
           (REL : inv (negb b) p):
    shape_invF b inv b (TauF p)
| ShapeTauSkip p
               (REL : inv b p):
    shape_invF b inv b (TauF p)
.

Hint Constructors shape_invF.

Definition shape_inv_ b1 inv : bool -> ccs -> Prop :=
  fun b2 p => shape_invF b1 inv b2 (observe p).

(* Proving monotonicity properties for [paco]. *)

Lemma shape_invF_mono b1 inv inv' b2 p1
      (IN: shape_invF b1 inv b2 p1)
      (LE: inv <2= inv'):
  shape_invF b1 inv' b2 p1.
Proof.
  intros. induction IN; eauto.
Qed.

Lemma shape_inv__mono b1 : monotone2 (shape_inv_ b1).
Proof. do 2 red. intros. eapply shape_invF_mono; eauto. Qed.

Hint Resolve shape_inv__mono : paco.

Definition shape_inv (p : ccs) : Prop := paco2 (shape_inv_ true) bot2 true p.

Theorem par_preserves_shape :
  forall p1 p2, shape_inv p1 -> shape_inv p2 -> shape_inv (par p1 p2).
Proof.
  unfold shape_inv.
  pcofix CIH. pstep.
  intros. punfold H0. punfold H1.
Admitted.

(* To show correctness of our denotation of CCS, we compare
   the trace semantics between this denotation and the
   operational semantics for CCS. *)

(** *Operational Semantics for CCS. *)

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

Inductive aux_step {l : A} : option Label -> ccs_o -> ccs_o -> Prop :=
| aux_step_Send t :
    aux_step (Some (In l)) (Action (In l) t) t
| aux_step_Recv t :
    aux_step (Some (Out l)) (Action (Out l) t) t
.

Inductive sync_step {l : A} : option Label -> ccs_o -> ccs_o -> Prop :=
| sync_step_Choice_L u v u' (A' : option Label) :
    sync_step A' u u' -> sync_step A' (Choice u v) u'
| sync_step_Choice_R u v v' (A' : option Label) :
    sync_step A' v v' -> sync_step A' (Choice u v) v'
| sync_step_Par_L u v u' (A' : option Label) :
    sync_step A' u u' -> sync_step A' (Par u v) (Par u' v)
| sync_step_Par_R u v v' (A' : option Label) :
    sync_step A' v v' -> sync_step A' (Par u v) (Par u v')
| sync_step_Par_Comm1 u v u' v' :
    @aux_step l (Some (In l)) u u' ->
    @aux_step l (Some (Out l)) v v' ->
    sync_step None u' v'
| sync_step_Par_Comm2 u v u' v' :
    @aux_step l (Some (Out l)) u u' ->
    @aux_step l (Some (In l)) v v' ->
    sync_step None u' v'
.

End ccs_op.

(* Trace Semantics. The observed events by the trace should be
   only on the synchronous steps, so
      obs := Sync (n).
*)

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
