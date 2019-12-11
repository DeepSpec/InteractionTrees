From ITree Require Import
     ITree
     ITreeDefinition
     Interp.Traces
     Eq
     .

From Coq Require Import
     Lists.List
     Arith.EqNat
     Arith.PeanoNat
     Program.Equality
     List
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

Require Import ITree.Eq.EqAxiom.

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
Set Contextual Implicit.
Set Primitive Projections.

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

Notation ccs' := (itree' ccsE unit).

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
CoFixpoint par' (p1 p2 : ccs) : ccs :=
  let par_left (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | (Vis (Act x) k), _ => Vis (Act x) (fun _ => par' (k tt) p2)
    | Vis (Sync a) t1, _ => Vis (Sync a) (fun _ => par' (t1 tt) p2)
    | Ret _, _ => Tau (par' p2 p2)
    | _, _ => fail
    end
  in let par_right (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | _, (Vis (Act x) k) => Vis (Act x) (fun _ => par' p1 (k tt))
    | _, Vis (Sync a) t1 => Vis (Sync a) (fun _ => par' p1 (t1 tt))
    | _, Ret _ => Tau (par' p1 p1)
    | _, _ => fail
    end
  in let par_comm (p1 p2 : ccs) : ccs :=
    match p1, p2 with
    | (Vis (Act (In l1)) k1), (Vis (Act (Out l2)) k2) =>
      if A_beq l1 l2
      then Vis (Sync l1) (fun _ => par' (k1 tt) (k2 tt))
      else fail
    | (Vis (Act (Out l1)) k1), (Vis (Act (In l2)) k2) =>
      if A_beq l1 l2
      then Vis (Sync l1) (fun _ => par' (k1 tt) (k2 tt))
      else fail
    | _, _ => fail
    end
  in
  match (observe p1), (observe p2) with
  | (VisF (Or n1) k1), (VisF (Or n2) k2) =>
      Vis (Or (n1 + n2 + (n1 * n2))) (fun n0 : nat =>
                    if beq_nat n0 n1
                    then par_left (k1 n0) p2
                    else if beq_nat n0 (n2 + n2)
                         then par_right p1 (k2 (n0 - n1))
                         else par_comm (k1 ((n0 - n1 - n2) mod n2)) (k2 ((n0 - n1 - n2) / n1)))
  | _, _ => fail
  end
.

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
Inductive shape_invF (inv : bool -> ccs -> Prop) : bool -> ccs' -> Prop :=
| ShapeRet :
    shape_invF inv false (RetF tt)
| ShapeOr k
          (n1 n2 : nat)
          (REL : forall n1, inv false (k n1)):
    shape_invF inv true (VisF (Or n2) k)
| ShapeAct a k
           (REL : inv true (k tt)):
    shape_invF inv false (VisF (Act a) k)
| ShapeSync a k
            (REL : inv true (k tt)):
    shape_invF inv false (VisF (Sync a) k)
| ShapeFail k:
    shape_invF inv false (VisF Fail k)
| ShapeTau p
           (REL : inv true p):
    shape_invF inv false (TauF p)
| ShapeTauSkip p
               (REL : inv true p):
    shape_invF inv false (TauF p)
.

Hint Constructors shape_invF.

Definition shape_inv_ inv : bool -> ccs -> Prop :=
  fun b p => shape_invF inv b (observe p).

(* Proving monotonicity properties for [paco]. *)

Lemma shape_invF_mono inv inv' b p1
      (IN: shape_invF inv b p1)
      (LE: inv <2= inv'):
  shape_invF inv' b p1.
Proof.
  intros. induction IN; eauto.
Qed.

Lemma shape_inv__mono : monotone2 (shape_inv_).
Proof. do 2 red. intros. eapply shape_invF_mono; eauto. Qed.

Hint Resolve shape_inv__mono : paco.

Definition shape_inv (p : ccs) : Prop := paco2 shape_inv_ bot2 true p.

Instance proper_par'_eqit : Proper (eq_itree eq ==> eq_itree eq ==> eq_itree eq) par'. Admitted.

Instance shape_inv_par'_eqit : Proper (eq_itree eq ==> iff) shape_inv.
Admitted.

Ltac bubble_types :=
  repeat (match goal with
          | h: ?T |- _ =>
            lazymatch type of h with
            | nat => fail
            | _ => revert h
            end
          end).
Ltac bubble_types2 :=
  repeat (match goal with
          | h: ?T |- _ =>
            lazymatch type of h with
            | nat -> itree ccsE unit => fail
            | _ => revert h
            end
          end)
.

Theorem par'_preserves_shape :
  forall (p1 p2 : ccs),
    shape_inv p1 -> shape_inv p2 -> shape_inv (par' p1 p2).
Proof.
  intros p1 p2.
  setoid_rewrite (itree_eta p1).
  setoid_rewrite (itree_eta p2).
  generalize dependent p1. generalize dependent p2.
  pcofix CIH. unfold shape_inv in CIH.
  pstep.
  unfold shape_inv_ in *. intros p2 p1.
  destruct (observe p1); intros H H0;
    punfold H; punfold H0.
  - (* Ret *)
    destruct (observe p2); inversion H; subst.
  - (* Tau *)
    destruct (observe p2); inversion H; subst.
  - (* Vis *)
    destruct (observe p2); inversion H;
      inversion H0.
    (* par (Vis e k, Vis e0 k0) *)
    dependent destruction H2.
    dependent destruction H6.
    dependent destruction H7.
    bubble_types; intros. bubble_types2; intros.
    cbn; econstructor; eauto; left; pstep.
    simpl.
    destruct (n4 =? n2).
    + (* Left *)
      match goal with
        |- shape_invF _ _ (?cont) => remember cont as k2
      end.
      destruct k2 eqn: Hk2.
      * (* RetF *)
        destruct r0; constructor.
      * (* TauF *)
        destruct (_observe (k n4)) eqn:?;
          setoid_rewrite Heqi in Heqk2; try inversion Heqk2.
        -- constructor. right.
           setoid_rewrite (itree_eta_ (Vis (Or n3) k0)).
           apply CIH; pstep; simpl; eapply H0.
        -- destruct e; inversion Heqk2.
      * (* VisF *)
        destruct (_observe (k n4)) eqn:Heqi;
        setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
        rewrite Heqk2.
        -- constructor.
        -- destruct e0 eqn: He0; try constructor;
            try (right; setoid_rewrite (itree_eta_ (k3 tt));
                 setoid_rewrite (itree_eta_ (Vis (Or n3) k0))).
          ++ subst. inversion Heqk2. apply CIH;
             dependent destruction H5; try (pstep; apply H0).
             destruct (REL n4).
             ** punfold H1. unfold shape_inv_ in H1.
                unfold observe in H1.
                rewrite Heqi in H1. inversion H1.
                dependent destruction H5.
                setoid_rewrite <- (itree_eta_ (k3 tt)).
                destruct REL1. apply H3.
                inversion H3.
             ** inversion H1.
          ++ apply CIH; try (pstep; eapply H0).
             destruct (REL n4).
             ** punfold H1. unfold shape_inv_ in H1.
                unfold observe in H1.
                rewrite Heqi in H1. inversion H1.
                dependent destruction H5.
                setoid_rewrite <- (itree_eta_ (k3 tt)).
                destruct REL1. apply H3.
                inversion H3.
             ** inversion H1.
    + (* Right & Comm *)
      destruct (n4 =? n3 + n3).
      * (* Right. This proof is symmetric with Left. *)
        match goal with
          |- shape_invF _ _ (?cont) => remember cont as k2
        end.
        destruct k2 eqn: Hk2.
        -- (* RetF *)
          destruct r0; constructor.
        -- (* TauF *)
          destruct (_observe (k0 (n4 - n2))) eqn:?;
                   setoid_rewrite Heqi in Heqk2; try inversion Heqk2.
          ++ constructor. right.
             setoid_rewrite (itree_eta_ (Vis (Or n2) k)).
             apply CIH; pstep; simpl; eapply H.
          ++ destruct e; inversion Heqk2.
        -- (* VisF *)
          destruct (_observe (k0 (n4 - n2))) eqn: Heqi;
            setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
              rewrite Heqk2.
          ++ constructor.
          ++ destruct e0 eqn: He0; try constructor;
               try (right; setoid_rewrite (itree_eta_ (k3 tt));
                    setoid_rewrite (itree_eta_ (Vis (Or n2) k)));
               apply CIH.
             ** pstep. apply H.
             ** destruct (REL0 (n4 - n2)).
                --- punfold H1. unfold shape_inv_ in H1.
                    unfold observe in H1.
                    rewrite Heqi in H1. inversion H1.
                    dependent destruction H5.
                    setoid_rewrite <- (itree_eta_ (k3 tt)).
                    destruct REL1. apply H3.
                    inversion H3.
                --- inversion H1.
             ** pstep. apply H.
             ** destruct (REL0 (n4 - n2)).
                --- punfold H1. unfold shape_inv_ in H1.
                    unfold observe in H1.
                    rewrite Heqi in H1. inversion H1.
                    dependent destruction H5.
                    setoid_rewrite <- (itree_eta_ (k3 tt)).
                    destruct REL1. apply H3.
                    inversion H3.
                --- inversion H1.
      * (* Comm *)
        match goal with
          |- shape_invF _ _ (?cont) => remember cont as k2
        end.
        destruct k2 eqn: Hk2.
        -- destruct r0; constructor.
        -- destruct (_observe (k ((n4 - n2 - n3) mod n3))) eqn:?;
             setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
             rewrite Heqk2.
           destruct e; try inversion H2. clear H2. clear H3.
           destruct l;
           destruct (_observe (k0 ((n4 - n2 - n3) / n2))) eqn:?;
            setoid_rewrite Heqi0 in Heqk2; try inversion Heqk2;
            rewrite Heqk2;
              destruct e; try inversion H2; clear H2; clear H3;
              destruct l0; try inversion Heqk2.
        -- destruct (_observe (k ((n4 - n2 - n3) mod n3))) eqn:?;
             setoid_rewrite Heqi in Heqk2; try inversion Heqk2;
             rewrite Heqk2.
           ++ destruct r0; constructor.
           ++ constructor.
           ++ clear H2. destruct e0.
              ** constructor.
              ** destruct l.
                 --- destruct (_observe (k0 ((n4 - n2 - n3) / n2))) eqn:?;
                     setoid_rewrite Heqi0 in Heqk2; setoid_rewrite Heqi0.
                     +++ constructor.
                     +++ constructor.
                     +++ destruct e0; try constructor. destruct l0.
                         *** constructor.
                         *** simpl. constructor. right.
                             setoid_rewrite (itree_eta_ (k3 tt)).
                             setoid_rewrite (itree_eta_ (k4 tt)).
                             apply CIH.
                             ---- destruct (REL ((n4 - n2 - n3) mod n3)).
                                  ++++ punfold H1. unfold shape_inv_ in H1.
                                       unfold observe in H1.
                                       rewrite Heqi in H1. inversion H1.
                                       dependent destruction H4.
                                       setoid_rewrite <- (itree_eta_ (k3 tt)).
                                       destruct REL1. apply H2. inversion H2.
                                  ++++ inversion H1.
                             ---- destruct (REL0 ((n4 - n2 - n3) / n2)).
                                  ++++ punfold H1. unfold shape_inv_ in H1.
                                       unfold observe in H1.
                                       rewrite Heqi0 in H1. inversion H1.
                                       dependent destruction H4.
                                       setoid_rewrite <- (itree_eta_ (k4 tt)).
                                       destruct REL1. apply H2. inversion H2.
                                  ++++ inversion H1.
                 --- destruct (_observe (k0 ((n4 - n2 - n3) / n2))) eqn:?;
                     setoid_rewrite Heqi0 in Heqk2; setoid_rewrite Heqi0.
                     +++ constructor.
                     +++ constructor.
                     +++ destruct e0; try constructor. destruct l0.
                         *** constructor. right.
                             setoid_rewrite (itree_eta_ (k3 tt)).
                             setoid_rewrite (itree_eta_ (k4 tt)).
                             apply CIH.
                             ---- destruct (REL ((n4 - n2 - n3) mod n3)).
                                  ++++ punfold H1. unfold shape_inv_ in H1.
                                       unfold observe in H1.
                                       rewrite Heqi in H1. inversion H1.
                                       dependent destruction H4.
                                       setoid_rewrite <- (itree_eta_ (k3 tt)).
                                       destruct REL1. apply H2. inversion H2.
                                  ++++ inversion H1.
                             ---- destruct (REL0 ((n4 - n2 - n3) / n2)).
                                  ++++ punfold H1. unfold shape_inv_ in H1.
                                       unfold observe in H1.
                                       rewrite Heqi0 in H1. inversion H1.
                                       dependent destruction H4.
                                       setoid_rewrite <- (itree_eta_ (k4 tt)).
                                       destruct REL1. apply H2. inversion H2.
                                  ++++ inversion H1.
                         *** constructor.
              ** constructor.
              ** constructor.
Qed.

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
