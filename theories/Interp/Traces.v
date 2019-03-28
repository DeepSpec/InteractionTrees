From Coq Require Import
     List.

Import ListNotations.

From ITree Require Import
     Core.ITreeDefinition
     Eq.UpToTausEquivalence
     Eq.SimUpToTaus
     Eq.Shallow.

Local Open Scope itree.

From Paco Require Import
     paco.

Inductive trace {E : Type -> Type} {R : Type} : Type :=
| TEnd : trace
| TRet : R -> trace
| TEventEnd : forall {X}, E X -> trace
| TEventResponse : forall {X}, E X -> X -> trace -> trace
.

(* Append two traces, ignoring the end of the first trace. *)
Fixpoint app_trace {E R S} (tr1 : @trace E R) (tr2 : @trace E S) : @trace E S :=
  match tr1 with
  | TEventResponse e x tr => TEventResponse e x (app_trace tr tr2)
  | _ => tr2
  end.

(* Get the value in the TRet at the end of the trace, if it exists. *)
Fixpoint trace_ret {E R} (tr : @trace E R) : option R :=
  match tr with
  | TRet r => (Some r)
  | TEventResponse _ _ tr => trace_ret tr
  | _ => None
  end.

Inductive is_traceF {E : Type -> Type} {R : Type} :
  itreeF E R (itree E R) -> @trace E R -> Prop :=
| TraceEmpty : forall t, is_traceF t TEnd
| TraceRet : forall r, is_traceF (RetF r) (TRet r)
| TraceTau : forall t tr,
    is_traceF (observe t) tr ->
    is_traceF (TauF t) tr
| TraceVisEnd : forall X (e : E X) k,
    is_traceF (VisF e k) (TEventEnd e)
| TraceVisContinue : forall X (e : E X) (x : X) k tr,
    is_traceF (observe (k x)) tr ->
    is_traceF (VisF e k) (TEventResponse e x tr)
.

Definition is_trace {E : Type -> Type} {R : Type} (t : itree E R) :=
  is_traceF (observe t).

(* t1 ⊑ t2 *)
Definition trace_incl {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr, is_trace t1 tr -> is_trace t2 tr.

(* t1 ≡ t2 *)
Definition trace_eq {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    trace_incl t1 t2 /\ trace_incl t2 t1.

(* (* A trace is still valid after removing taus *) *)
(* Lemma is_traceF_unalltaus_remove: forall {E R} (t1 t2 : itreeF E R (itree E R)) tr, *)
(*     unalltausF t1 t2 -> *)
(*     is_traceF t1 tr -> *)
(*     is_traceF t2 tr. *)
(* Proof. *)
(*   intros. inv H. induction H1; subst; auto. *)
(*   apply IHuntausF; auto. inversion H0; subst; auto; constructor. *)
(* Qed. *)
(* Lemma is_trace_unalltaus_remove: forall {E R} (t1 t2 : itree E R) tr, *)
(*     unalltausF (observe t1) (observe t2) -> *)
(*     is_trace t1 tr -> *)
(*     is_trace t2 tr. *)
(* Proof. intros. eapply is_traceF_unalltaus_remove; eauto. Qed. *)

(* (* A trace is still valid after adding taus *) *)
(* Lemma is_traceF_unalltaus_add: forall {E R} (t1 t2 : itreeF E R (itree E R)) tr, *)
(*     unalltausF t1 t2 -> *)
(*     is_traceF t2 tr -> *)
(*     is_traceF t1 tr. *)
(* Proof. *)
(*   intros. inv H. *)
(*   induction H1; auto. *)
(*   rewrite <- OBS. constructor. auto. *)
(* Qed. *)
(* Lemma is_trace_unalltaus_add: forall {E R} (t1 t2 : itree E R) tr, *)
(*     unalltausF (observe t1) (observe t2) -> *)
(*     is_trace t2 tr -> *)
(*     is_trace t1 tr. *)
(* Proof. intros. eapply is_traceF_unalltaus_add; eauto. Qed. *)

Lemma is_traceF_tau : forall {E R} (t : itree E R) tr,
    is_traceF (observe t) tr <->
    is_traceF (TauF t) tr.
Proof.
  intros. split; intros.
  - constructor. remember (observe t).
    generalize dependent t.
    induction H; intros; subst; constructor; eapply IHis_traceF; auto.
  - inversion H; subst; try constructor; auto.
Qed.

Lemma sutt_trace_incl : forall {E R} (t1 t2 : itree E R),
    sutt eq t1 t2 -> trace_incl t1 t2.
Proof.
  red. intros. red in H0. remember (observe t1).
  generalize dependent t1. generalize dependent t2.
  induction H0; intros; try solve [constructor].
  - uunfold H. rewrite <- Heqi in H.
    remember (RetF _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0; red; rewrite <- Heqi1; constructor.
    eapply IHsuttF; eauto.
  - apply IHis_traceF with (t1:=t); auto.
    apply sutt_elim_tau_left. red. red in H. rewrite <- Heqi in H. auto.
  - uunfold H. rewrite <- Heqi in H.
    remember (VisF _ _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0.
    + auto_inj_pair2. subst. red. rewrite <- Heqi1. constructor.
    + red. rewrite <- Heqi1. constructor. eapply IHsuttF; eauto.
  - uunfold H. rewrite <- Heqi in H.
    remember (VisF _ _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0.
    + auto_inj_pair2. subst. red. rewrite <- Heqi1. constructor.
      eapply IHis_traceF; auto.
    + red. rewrite <- Heqi1. constructor. apply IHsuttF; auto.
Qed.

Lemma eutt_trace_eq : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 -> trace_eq t1 t2.
Proof.
  split.
  - apply sutt_trace_incl; apply eutt_sutt; auto.
  - symmetry in H. apply sutt_trace_incl; apply eutt_sutt; auto.
Qed.

Lemma trace_incl_sutt : forall {E R} (t1 t2 : itree E R),
    trace_incl t1 t2 -> sutt eq t1 t2.
Proof.
  intros E R. ucofix CIH. intros t1 t2 Hincl.
  unfold trace_incl in *. unfold is_trace in *.
  destruct (observe t1).
  - assert (H : is_traceF (RetF r0 : itreeF E R (itree E R)) (TRet r0)) by constructor.
    apply Hincl in H. clear Hincl. destruct (observe t2); inv H.
    + constructor. auto.
    + constructor.
      remember (observe t). remember (TRet _).
      generalize dependent t.
      induction H1; intros; try inv Heqt0; auto.
      constructor. eapply IHis_traceF; eauto.
  - constructor. ubase. apply CIH. intros. apply Hincl. constructor. auto.
  - assert (H: is_traceF (VisF e k) (TEventEnd e)) by constructor.
    apply Hincl in H. destruct (observe t2); inv H.
    + constructor.
      assert (forall tr, is_traceF (VisF e k) tr -> is_traceF (observe t) tr).
      {
        intros. rewrite is_traceF_tau. apply Hincl; auto.
      }
      clear Hincl. rename H into Hincl.
      remember (observe t). remember (TEventEnd _).
      generalize dependent t.
      induction H1; intros; try inv Heqt0; auto.
      * constructor. eapply IHis_traceF; eauto.
        intros. rewrite is_traceF_tau. apply Hincl; auto.
      * auto_inj_pair2. subst. constructor. intro. ubase. apply CIH. intros.
        assert (is_traceF (VisF e k) (TEventResponse e x tr)) by (constructor; auto).
        apply Hincl in H0. inv H0. auto_inj_pair2. subst. auto.
    + auto_inj_pair2. subst. constructor. intro. ubase. apply CIH. intros.
      assert (is_traceF (VisF e k) (TEventResponse e x tr)) by (constructor; auto).
      apply Hincl in H0. inv H0. auto_inj_pair2. subst. auto.
Qed.

Theorem trace_incl_iff_sutt : forall {E R} (t1 t2 : itree E R),
    sutt eq t1 t2 <-> trace_incl t1 t2.
Proof.
  split.
  - apply sutt_trace_incl.
  - apply trace_incl_sutt.
Qed.

Lemma trace_eq_eutt : forall {E R} (t1 t2 : itree E R),
    trace_eq t1 t2 -> t1 ≈ t2.
Proof.
  intros E R t1 t2 [? ?]. apply sutt_eutt.
  - apply trace_incl_sutt; auto.
  - apply trace_incl_sutt in H0. clear H.
    generalize dependent t1. generalize dependent t2. ucofix CIH; intros.
    uunfold H0. induction H0; constructor; try red; eauto with paco.
    ubase. destruct ot2.
    * replace (RetF r0) with (observe (Ret r0) : itree' E R); eauto with paco.
    * replace (TauF t) with (observe (Tau t) : itree' E R); eauto with paco.
    * replace (VisF e k) with (observe (Vis e k) : itree' E R); eauto with paco.
Qed.

Theorem trace_eq_iff_eutt : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 <-> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_eq.
  - apply trace_eq_eutt.
Qed.

Inductive event (E : Type -> Type) : Type :=
| Event : forall {X}, E X -> X -> event E
.

(* [step_ ev t' t] if [t] steps to [t'] (read right to left!)
   with visible event [ev]. *)
Inductive step_ {E : Type -> Type} {R : Type}
          (ev : event E) (t' : itree E R) :
  itree E R -> Prop :=
| StepTau : forall t, step_ ev t' t -> step_ ev t' (Tau t)
| StepVis : forall X (e : E X) (x : X) k,
    ev = Event _ e x ->
    t' = k x ->
    step_ ev t' (Vis e k)
.

Definition step {E : Type -> Type} {R : Type}
           (ev : event E) (t t' : itree E R) : Prop :=
  step_ ev t' t.

CoInductive simulates {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
| SimStep : forall t1 t2,
    (forall ev t1',
        step ev t1 t1' ->
        exists t2', step ev t2 t2' /\ simulates t1' t2') ->
    simulates t1 t2.

Theorem simulates_trace_incl {E : Type -> Type} {R : Type} :
  forall t1 t2 : itree E R,
    simulates t1 t2 -> trace_incl t1 t2.
Proof.
Abort.

(* Set-of-traces monad *)
Definition traces (E : Type -> Type) (R : Type) : Type :=
  @trace E R -> Prop.

Definition bind_traces {E : Type -> Type} {R S : Type}
           (ts : traces E R) (kts : R -> traces E S) : traces E S :=
  fun tr =>
    (tr = TEnd /\ ts TEnd) \/
    (exists X (e : E X), tr = TEventEnd e /\ ts (TEventEnd e)) \/
    (exists r tr1 tr2,
        tr = app_trace tr1 tr2 /\
        trace_ret tr1 = Some r /\
        ts tr1 /\
        kts r tr).

Definition ret_traces {E : Type -> Type} {R : Type} :
  R -> traces E R :=
  fun r tr =>
    tr = TEnd \/ tr = TRet r.
