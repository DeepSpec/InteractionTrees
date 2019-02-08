Require Import List.
Import ListNotations.

From ITree Require Import
     Core
     Eq.Eq
     Eq.UpToTaus.

From Paco Require Import
     paco.

Inductive event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E
| OutputEvent : forall X, E X -> event E
.

Arguments Event {E X}.
Arguments OutputEvent {E X}.

Definition trace (E : Type -> Type) : Type := list (event E).

Inductive is_traceF {E : Type -> Type} {R : Type} :
  itreeF E R (itree E R) -> trace E -> option R -> Prop :=
| TraceEmpty : forall t, is_traceF t [] None
| TraceRet : forall r,
    is_traceF (RetF r) [] (Some r)
| TraceTau : forall t tr r_,
    is_traceF (observe t) tr r_ ->
    is_traceF (TauF t) tr r_
| TraceVis : forall X (e : E X) (x : X) k tr r_,
    is_traceF (observe (k x)) tr r_ ->
    is_traceF (VisF e k) (Event e x :: tr) r_
| TraceUninhab : forall X (e : E X) k,
    is_traceF (VisF e k) [OutputEvent e] None
.

Definition is_trace {E R} (t : itree E R) := is_traceF (observe t).

(* t1 ⊑ t2 *)
Definition trace_incl {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr r_, is_trace t1 tr r_ -> is_trace t2 tr r_.

(* t1 ≡ t2 *)
Definition trace_eq {E R} : itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    trace_incl t1 t2 /\ trace_incl t2 t1.

Require Import ProofIrrelevance.

Ltac invert_existTs :=
  repeat match goal with
         | [ H : existT ?P ?p _ = existT ?P ?p _ |- _ ] => apply inj_pair2 in H
         end; subst.

(* A trace is still valid after removing taus *)
Lemma is_trace_unalltaus: forall {E R} (t1 t2 : itree E R) tr r,
    unalltausF (observe t1) (observe t2) ->
    is_trace t1 tr r ->
    is_trace t2 tr r.
Proof.
  intros. induction H0; intros; subst; try solve [constructor].
  - inv H; subst. inv H0; subst.
    + red. rewrite <- H3. constructor.
    + inversion OBS.
  - apply IHis_traceF. eapply unalltaus_tau; eauto.
  - red. destruct (observe t2).
    + inv H. inv H1. inv OBS.
    + inv H. inv H2.
    + inv H. inv H1.
      * invert_existTs. constructor; auto.
      * inv OBS.
  - red. destruct (observe t2).
    + inv H. inv H0. inv OBS.
    + inv H. inv H1.
    + inv H. inv H0.
      * invert_existTs. constructor.
      * inv OBS.
Qed.

(* A trace is still valid after adding taus *)
Lemma is_trace_unalltaus': forall {E R} (t1 t2 : itree E R) tr r,
    unalltausF (observe t1) (observe t2) ->
    is_trace t2 tr r ->
    is_trace t1 tr r.
Proof.
  intros. inversion H. remember (observe t1). remember (observe t2).
  generalize dependent t1. generalize dependent t2. induction H1; intros; subst.
  - red. rewrite <- Heqi. assumption.
  - red. rewrite <- Heqi. constructor. eapply IHuntausF; auto.
Qed.

Lemma euttF_tau_add {E R} r (t1 t2 t1' : itree E R)
    (OBS: TauF t1' = observe t1)
    (REL: eutt_ r t1' t2):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite finite_taus_tau; eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
    inversion UNTAUS2. constructor; auto. econstructor; eauto.
Qed.

Lemma euttF_tau_remove {E R} r (t1 t2 t1' : itree E R)
    (OBS: TauF t1 = observe t1')
    (REL: eutt_ r t1' t2):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite <- FIN. symmetry. rewrite finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS1. constructor; auto.
    econstructor; eauto.
Qed.

Lemma euttF_tau_remove' {E R} r (t1 t2 t2' : itree E R)
    (OBS: TauF t2 = observe t2')
    (REL: eutt_ r t1 t2'):
  eutt_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite FIN. rewrite finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS2. constructor; auto.
    econstructor; eauto.
Qed.

Lemma eutt_trace_incl : forall {E R} (t1 t2 : itree E R),
    t1 ~~ t2 -> trace_incl t1 t2.
Proof.
  red. intros. red in H0. remember (observe t1).
  generalize dependent t1. generalize dependent t2.
  induction H0; intros; try solve [constructor].
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (RetF r)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H0). inv EQV. red.
    eapply is_trace_unalltaus'.
    + simpobs. auto.
    + red. rewrite <- Heqi. constructor.
  - apply IHis_traceF with (t1:=t); auto.
    rewrite <- H. symmetry. apply tauF_eutt. assumption.
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (VisF e k)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H1). inv EQV.
    invert_existTs. inv H1. specialize (H6 x).

    red. remember (VisF _ _) in H2. remember (observe t2).
    generalize dependent t2.
    induction H2; intros; subst.
    + constructor. apply IHis_traceF with (t1:=k x); auto.
      pfold. inversion H6.
      pinversion H1. inversion H1.
    + constructor. eapply IHuntausF; auto.
      * rewrite FIN. apply finite_taus_tau; auto.
      * eapply euttF_tau_remove'; eauto.
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (VisF e k)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H0). inv EQV.
    invert_existTs. inv H0.

    red. remember (VisF _ _) in H1. remember (observe t2).
    generalize dependent t2.
    induction H1; intros; subst; constructor.
    eapply IHuntausF; auto.
    + rewrite FIN. apply finite_taus_tau; auto.
    + eapply euttF_tau_remove'; eauto.
Qed.

Lemma eutt_trace_eq : forall {E R} (t1 t2 : itree E R),
    t1 ~~ t2 -> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_incl; auto.
  - symmetry in H. apply eutt_trace_incl; auto.
Qed.

Lemma trace_eq_eutt : forall {E R} (t1 t2 : itree E R),
    trace_eq t1 t2 -> t1 ~~ t2.
Proof.
Admitted.

Theorem trace_eq_iff_eutt : forall {E R} (t1 t2 : itree E R),
    t1 ~~ t2 <-> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_eq.
  - apply trace_eq_eutt.
Qed.

(* [step_ ev t' t] if [t] steps to [t'] (read right to left!)
   with visible event [ev]. *)
Inductive step_ {E : Type -> Type} {R : Type}
          (ev : event E) (t' : itree E R) :
  itree E R -> Prop :=
| StepTau : forall t, step_ ev t' t -> step_ ev t' (Tau t)
| StepVis : forall X (e : E X) (x : X) k,
    ev = Event e x ->
    t' = k x ->
    step_ ev t' (Vis e k)
.

Definition step {E : Type -> Type} {R : Type}
           (ev : event E) (t t' : itree E R) : Prop :=
  step_ ev t' t.

CoInductive simulates {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
| SimStep : forall t1 t2,
    (forall ev t1', step ev t1 t1' ->
     exists    t2', step ev t2 t2' /\ simulates t1' t2') ->
    simulates t1 t2.

Theorem simulates_trace_incl {E : Type -> Type} {R : Type} :
  forall t1 t2 : itree E R,
    simulates t1 t2 -> trace_incl t1 t2.
Proof.
Abort.

(* Set-of-traces monad *)
Definition traces (E : Type -> Type) (R : Type) : Type :=
  trace E -> option R -> Prop.

Definition bind_traces {E : Type -> Type} {R S : Type}
           (ts : traces E R) (kts : R -> traces E S) : traces E S :=
  fun tr s_ =>
    (s_ = None /\ ts tr None) \/
    (exists r tr1 tr2,
        tr = tr1 ++ tr2 /\
        ts tr1 (Some r) /\
        kts r tr s_).

Definition ret_traces {E : Type -> Type} {R : Type} :
  R -> traces E R :=
  fun r tr r_ =>
    tr = [] /\ (r_ = None \/ r_ = Some r).
