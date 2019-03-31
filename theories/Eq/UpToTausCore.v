(** * Simple facts about equivalence up to taus *)

(** This module proves simple facts about the [eutt] relation defined in
    [UpToTaus]. *)

(* begin hide *)
From Coq Require Import
     Program (* [revert_until] *)
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Shallow
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt0 eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt0 RR eutt).
Proof.
  ucofix CIH. intros.
  uunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  ucofix CIH. red. ucofix CIH'. intros.
  uunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt0_param `{Reflexive _ RR} eutt
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (cpn2 (eutt0_ RR eutt) r).
Proof.
  ucofix CIH. red. intros. repeat red.
  destruct (observe x); eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt_param `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (cpn2 (eutt0 RR) r).
Proof.
  ucofix CIH. red. ucofix CIH'. intros. repeat red.
  destruct (observe x); eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt0_guard `{Reflexive _ RR}
       r (r' : relation (itree E R)) :
  Reflexive (gcpn2 (eutt0_ RR r) r').
Proof.
  repeat intro. assert (X := Reflexive_eutt0_param r bot2 x). uunfold X.
  eauto 7 using euttF_mon, cpn2_mon_bot with paco.
Qed.

Global Instance Reflexive_eutt_guard `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eutt0 RR) r).
Proof.
  ustep. intros. apply Reflexive_eutt0_guard.
Qed.

End EUTT_homo.

Section EUTT_hetero.

Context {E : Type -> Type}.

Lemma Symmetric_euttF_hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop) (r'1 : _ -> _ -> Prop) (r'2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (SYM_r' : forall i j, r'1 i j -> r'2 j i) :
  forall (ot1 : itree' E R1) (ot2 : itree' E R2),
    euttF RR1 r1 r'1 ot1 ot2 -> euttF RR2 r2 r'2 ot2 ot1.
Proof.
  intros. induction H; eauto 7.
  econstructor; intros. edestruct EUTTK; eauto 7.
Qed.

Lemma Symmetric_eutt_hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR1 t1 t2 -> eutt RR2 t2 t1.
Proof.
  ucofix CIH. red. ucofix CIH'. intros.
  do 2 uunfold H0.
  repeat red in H0 |- *.
  induction H0; eauto 7 with paco.
  econstructor; intros.
  edestruct EUTTK as [TMP | TMP]; [eauto 7 with paco|].
  left. ubase. apply CIH. ustep. eauto.
Qed.

Lemma euttF_elim_tau_left {R1 R2} (RR: R1 -> R2 -> Prop) r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (cpn2 (eutt0_ RR r) bot2) (Tau t1) t2) :
  eutt0_ RR r (cpn2 (eutt0_ RR r) bot2) t1 t2.
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t1) as ott1.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott1; eauto.
  uunfold EQTAUS. eauto.
Qed.

Lemma euttF_elim_tau_right {R1 R2} (RR: R1 -> R2 -> Prop) r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (cpn2 (eutt0_ RR r) bot2) t1 (Tau t2)) :
  eutt0_ RR r (cpn2 (eutt0_ RR r) bot2) t1 t2.
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t2) as ott2.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott2; eauto.
  uunfold EQTAUS. eauto.
Qed.

Definition isb_tau {E R} (ot: itree' E R) : bool :=
  match ot with | TauF _ => true | _ => false end.

Lemma eutt_Ret {R1 R2} (RR: R1 -> R2 -> Prop) x y :
  RR x y -> @eutt E R1 R2 RR (Ret x) (Ret y).
Proof.
  intros; ustep. ustep. econstructor. eauto.
Qed.

Lemma eutt_Vis {R1 R2 U} RR (e: E U) k k' :
  (forall x: U, @eutt E R1 R2 RR (k x) (k' x)) ->
  eutt RR (Vis e k) (Vis e k').
Proof.
  intros. ustep. ustep. econstructor.
  intros. left. apply H.
Qed.

End EUTT_hetero.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance subrelation_observing_eutt:
  @subrelation (itree E R) (observing eq) eutt.
Proof.
  repeat intro. eapply subrelation_eq_eutt, observing_eq_itree_eq. eauto.
Qed.

Global Instance Reflexive_eutt: Reflexive eutt.
Proof. apply Reflexive_eutt_param; eauto. Qed.

Global Instance Symmetric_eutt: Symmetric eutt.
Proof.
  repeat intro. eapply Symmetric_eutt_hetero, H.
  intros; subst. eauto.
Qed.

Global Instance eutt_cong_go : Proper (going eutt ==> eutt) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance eutt_cong_observe : Proper (eutt ==> going eutt) observe.
Proof.
  constructor. do 2 ustep. do 2 uunfold H. auto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. do 2 ustep. econstructor. uunfold H. eauto.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof.
  constructor. ustep. ustep. econstructor.
  intros. specialize (H x0). uunfold H. eauto.
Qed.

End EUTT_eq.

Lemma eutt_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros. ustep. ustep. econstructor. uunfold H. eauto.
Qed.

Lemma eutt_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eutt RR (k1 u) (k2 u)) <->
  eutt RR (Vis e k1) (Vis e k2).
Proof.
  split.
  - intros. ustep; ustep; econstructor.
    intros x; specialize (H x). uunfold H. eauto.
  - intros H x.
    uunfold H; uunfold H; inversion H; auto_inj_pair2; subst.
    edestruct EUTTK; eauto with paco.
Qed.

Lemma eutt_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  @eutt E R1 R2 RR (Ret r1) (Ret r2) <-> RR r1 r2.
Proof.
  split.
  - intros H. uunfold H; uunfold H; inversion H; auto.
  - intros. ustep; ustep; econstructor. auto.
Qed.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  ustep. ustep. econstructor. apply Reflexive_eutt0_guard. auto.
Qed.

(** ** Tactics *)

(** Remove all taus from the left hand side of the goal
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps :=
  repeat (
      (* Only rewrite the LHS, even if it also occurs in the RHS *)
      rewrite itree_eta at 1;
      cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] =>
        (* Cancel [itree_eta] if no progress was made. *)
        fail 1
      | _ => try rewrite tau_eutt
      end).
