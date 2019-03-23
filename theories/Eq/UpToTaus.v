(** * Equivalence up to taus *)
(** We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(* begin hide *)
Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Basics.CategoryOps
     Basics.Function
     Core.ITree.

From ITree Require Export
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttF 
              (eutt: itree E R1 -> itree E R2 -> Prop)
              (eutt0: itree E R1 -> itree E R2 -> Prop)
  : itree' E R1 -> itree' E R2 -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF eutt eutt0 (RetF r1) (RetF r2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, eutt (k1 x) (k2 x) \/ eutt0 (k1 x) (k2 x)):
    euttF eutt eutt0 (VisF e k1) (VisF e k2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt0 t1 t2):
    euttF eutt eutt0 (TauF t1) (TauF t2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF eutt eutt0 (observe t1) ot2):
    euttF eutt eutt0 (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF eutt eutt0 ot1 (observe t2)):
    euttF eutt eutt0 ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt0_ eutt eutt0 t1 t2 := euttF eutt eutt0 (observe t1) (observe t2).
Hint Unfold eutt0_.

Definition eutt0 eutt t1 t2 := wcpn2 (eutt0_ eutt) bot2 bot2 t1 t2.
Hint Unfold eutt0.

Lemma euttF_mon r r' s s' x y
    (EUTT: euttF r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF r' s' x y.
Proof.
  induction EUTT; eauto.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Lemma monotone_eutt0_ eutt : monotone2 (eutt0_ eutt).
Proof. repeat intro. eauto using euttF_mon. Qed.
Hint Resolve monotone_eutt0_ : paco.

Lemma monotone_eutt0 : monotone2 eutt0.
Proof. red. intros. eapply wcpn2_mon_bot; eauto using euttF_mon. Qed.
Hint Resolve monotone_eutt0 : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : itree E R1 -> itree E R2 -> Prop := wcpn2 eutt0 bot2 bot2.
Hint Unfold eutt.

Lemma eutt_fold :
  eutt <2= wcpn2 eutt0 bot2 bot2.
Proof. intros. apply PR. Qed.
Hint Resolve eutt_fold.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors euttF.
Hint Unfold eutt0_.
Hint Unfold eutt0.
Hint Resolve monotone_eutt0_ : paco.
Hint Resolve monotone_eutt0 : paco.
Hint Unfold eutt.
Hint Resolve eutt_fold.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt0 eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt0 RR eutt).
Proof.
  wcofix CIH; wstep. intros.
  wunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  wcofix CIH; wstep. wcofix CIH'; wstep. intros.
  wunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt0_param `{Reflexive _ RR} eutt
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (wcpn2 (eutt0_ RR eutt) r rg).
Proof.
  repeat intro.
  eapply wcpn2_mon with (r:=bot2) (rg:=bot2); eauto with paco; try contradiction.
  revert x. wcofix CIH; wstep. red; intros.
  destruct (observe x); eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt_param `{Reflexive _ RR}
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (wcpn2 (eutt0 RR) r rg).
Proof.
  repeat intro.
  eapply wcpn2_mon with (r:=bot2) (rg:=bot2); eauto with paco; try contradiction.
  revert x. wcofix CIH; wstep. wcofix CIH'; wstep. intros. repeat red.
  destruct (observe x); eauto 7 with paco.
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
  wcofix CIH; wstep. wcofix CIH'; wstep. intros.
  do 2 wunfold H0.
  repeat red in H0 |- *.
  induction H0; eauto 7 with paco.
  econstructor; intros.
  edestruct EUTTK as [TMP | TMP]; [eauto 7 with paco|].
  left. wbase. apply CIH. wstep. eauto.
Qed.

Lemma euttF_elim_tau_left {R1 R2} (RR: R1 -> R2 -> Prop) r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (wcpn2 (eutt0_ RR r) bot2 bot2) (Tau t1) t2) :
  eutt0_ RR r (wcpn2 (eutt0_ RR r) bot2 bot2) t1 t2.
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t1) as ott1.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott1; eauto.
  wunfold EQTAUS. eauto.
Qed.

Lemma euttF_elim_tau_right {R1 R2} (RR: R1 -> R2 -> Prop) r (t1: itree E R1) (t2: itree E R2)
    (REL : eutt0_ RR r (wcpn2 (eutt0_ RR r) bot2 bot2) t1 (Tau t2)) :
  eutt0_ RR r (wcpn2 (eutt0_ RR r) bot2 bot2) t1 t2.
Proof.
  repeat red in REL |- *. simpl in *.
  remember (TauF t2) as ott2.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott2; eauto.
  wunfold EQTAUS. eauto.
Qed.

Definition isb_tau {E R} (ot: itree' E R) : bool :=
  match ot with | TauF _ => true | _ => false end.

Lemma eutt_Ret {R1 R2} (RR: R1 -> R2 -> Prop) x y :
  RR x y -> @eutt E R1 R2 RR (Ret x) (Ret y).
Proof.
  intros; wstep. wstep. econstructor. eauto.
Qed.

Lemma eutt_Vis {R1 R2 U} RR (e: E U) k k' :
  (forall x: U, @eutt E R1 R2 RR (k x) (k' x)) ->
  eutt RR (Vis e k) (Vis e k').
Proof.
  intros. wstep. wstep. econstructor.
  intros. left. apply H.
Qed.

End EUTT_hetero.

Section UptoClosures.
  
Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive clo_bind (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| clo_bind_intro U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (k1 v1) (k2 v2))
  : clo_bind r (ITree.bind t1 k1) (ITree.bind t2 k2)
.

Inductive clo_trans_eutt_left (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| clo_trans_eutt_intro t1 t2 t3
      (EQV: t1 ≈ t2)
      (REL: r t2 t3)
  : clo_trans_eutt_left r t1 t3
.

Inductive clo_trans_eutt_right (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| clo_trans_eutt_right_intro t1 t2 t3
      (EQV: t3 ≈ t2)
      (REL: r t1 t2)
  : clo_trans_eutt_right r t1 t3
.

Inductive clo_trans_eq (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| clo_trans_eq_intro t1 t2 t3 t4
      (EQVl: t1 ≅ t2)
      (EQVr: t4 ≅ t3)
      (REL: r t2 t3)
  : clo_trans_eq r t1 t4
.

End UptoClosures.

Hint Constructors clo_bind.
Hint Constructors clo_trans_eutt_left.
Hint Constructors clo_trans_eutt_right.
Hint Constructors clo_trans_eq.

Section EUTT_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Lemma eutt_clo_trans_left : clo_trans_eutt_left <3= cpn2 (@eutt0 E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. wcofix CIH; wstep. intros.
  wunfold REL. do 2 wunfold EQV. repeat red in EQV, REL |- *.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - eauto 9 using euttF_mon, wcpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot3) eqn: ISTAU.
    + destruct ot3; inv ISTAU.
      econstructor. wbase. eapply CIH. eauto with paco.
      wstep. rewrite (itree_eta' (TauF t)) in REL.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. wunfold EQTAUS. repeat red in EQTAUS. genobs_clear t2 ot.
      move REL before CIH. revert_until REL.
      induction REL; intros; inv H0.
      * genobs_clear t1 ot1. remember (RetF r1) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
      * genobs_clear t1 ot1. remember (VisF e k1) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
        econstructor. intros.
        edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
      * eapply IHREL; eauto.
        eapply euttF_elim_tau_right in EQTAUS. eauto.
  - eauto 8 using euttF_mon with rclo paco.
  - remember (TauF t2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7 with paco.
    wunfold EQTAUS. eauto.
Qed.

Lemma eutt_clo_trans_right : clo_trans_eutt_right <3= cpn2 (@eutt0 E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. wcofix CIH; wstep. intros.
  wunfold REL. do 2 wunfold EQV. repeat red in EQV, REL |- *.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - eauto 9 using euttF_mon, wcpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot1) eqn: ISTAU.
    + destruct ot1; inv ISTAU.
      econstructor. wbase. eapply CIH. eauto with paco.
      wstep. rewrite (itree_eta' (TauF t2)) in REL.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. wunfold EQTAUS. repeat red in EQTAUS. genobs_clear t2 ot.
      move REL before CIH. revert_until REL.
      induction REL; intros; inv H0.
      * genobs_clear t1 ot1. remember (RetF r2) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
      * genobs_clear t1 ot1. remember (VisF e k2) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
        econstructor. intros.
        edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
      * eapply IHREL; eauto.
        eapply euttF_elim_tau_right in EQTAUS. eauto.
  - eauto 8 using euttF_mon with rclo paco.
  - remember (TauF t2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7 with paco.
    wunfold EQTAUS. eauto.
Qed.

Lemma eutt_clo_bind : clo_bind <3= cpn2 (@eutt0 E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. wcofix CIH; wstep. intros.
  do 2 wunfold EQV. repeat red in EQV |- *.
  rewrite !unfold_bind.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - specialize (REL _ _ RBASE). wunfold REL.
    eauto 9 using euttF_mon, wcpn2_mon_bot with rclo paco.
  - econstructor. intros.
    edestruct EUTTK; eauto 7 with rclo paco.
  - simpl. eauto 8 with paco.
  - econstructor. rewrite unfold_bind. eapply IHEQV. eauto.
  - econstructor. rewrite unfold_bind. eapply IHEQV. eauto.
Qed.

Global Instance eutt_cong_wcpn (r rg: itree E R1 -> itree E R2 -> Prop) :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (wcpn2 (@eutt0 E R1 R2 RR) r rg).
Proof.
  repeat intro.
  wclo eutt_clo_trans_left. econstructor; eauto.
  wclo eutt_clo_trans_right. econstructor; eauto.
Qed.

Global Instance eutt_eq_under_rr_impl :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> flip impl) (eutt RR).
Proof.
  repeat red. intros. rewrite H, H0. eauto with paco.
Qed.

End EUTT_upto.

Arguments eutt_clo_trans_left : clear implicits.

Arguments eutt_clo_trans_right : clear implicits.

Arguments eutt_clo_bind : clear implicits.

Global Instance eutt_bind {E U R} :
  Proper (pointwise_relation _ (eutt eq) ==>
          eutt eq ==>
          eutt eq) (@ITree.bind' E U R).
Proof.
  wclo eutt_clo_bind. econstructor; eauto.
  intros. subst. eauto with paco.
Qed.

Section EUTT0_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma eutt0_clo_trans r rg:
  clo_trans_eq <3= cpn2 (@eutt0_ E R1 R2 RR (wcpn2 (eutt0 RR) r rg)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  wunfold EQVl. wunfold EQVr. repeat red in EQVl, EQVr. repeat red in REL |- *.
  move REL before r0. revert_until REL.
  induction REL; intros; subst; 
    try (dependent destruction EQVl; dependent destruction EQVr; []); simpobs.
  - eauto.
  - econstructor. intros.
    edestruct EUTTK.
    + left. rewrite REL, REL0. eauto.
    + right. eapply rclo2_clo. econstructor; eauto with rclo.
  - econstructor. eapply rclo2_clo. econstructor; eauto with rclo.
  - dependent destruction EQVl. wunfold REL0. simpobs. eauto.
  - dependent destruction EQVr. wunfold REL0. simpobs. eauto.
Qed.

Global Instance eq_cong_eutt0 r rg r0 rg0 :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (wcpn2 (@eutt0_ E R1 R2 RR (wcpn2 (eutt0 RR) r rg)) r0 rg0).
Proof.
  repeat intro.
  wclo eutt0_clo_trans. econstructor; eauto.
Qed.

Lemma eutt0_clo_bind r rg:
  clo_bind <3= cpn2 (@eutt0_ E R1 R2 RR (wcpn2 (eutt0 RR) r rg)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  do 2 wunfold EQV. repeat red in REL |- *. repeat red in EQV.
  rewrite !unfold_bind.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  move EQV before RU. revert_until EQV.
  induction EQV; intros; subst.
  - eauto using euttF_mon, upaco2_mon_bot with rclo.
  - econstructor. intros.
    edestruct EUTTK; right; eapply rclo2_clo; eauto 8 using euttF_mon with rclo paco.
  - simpl. econstructor. eapply rclo2_clo; eauto 8 with rclo paco.
  - econstructor. rewrite unfold_bind. eauto.
  - econstructor. rewrite unfold_bind. eauto.
Qed.

End EUTT0_upto.

Arguments eutt0_clo_trans : clear implicits.

Arguments eutt0_clo_bind : clear implicits.

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

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  repeat intro. rewrite H, H0. reflexivity.
Qed.

(* We can now rewrite with [eutt] equalities. *)
Global Instance Equivalence_eutt : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

Global Instance eutt_cong_go : Proper (going eutt ==> eutt) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance eutt_cong_observe : Proper (eutt ==> going eutt) observe.
Proof.
  constructor. rewrite <- !itree_eta. eauto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. wstep. wstep. econstructor. wunfold H. eauto.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof. 
  constructor. wstep. wstep. econstructor.
  intros. specialize (H x0). wunfold H. eauto.
Qed.

End EUTT_eq.

(**)

Lemma eutt_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros. wstep. wstep. econstructor. wunfold H. eauto.
Qed.

Lemma eutt_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eutt RR (k1 u) (k2 u)) <->
  eutt RR (Vis e k1) (Vis e k2).
Proof.
  split.
  - intros. wstep; wstep; econstructor.
    intros x; specialize (H x). wunfold H. eauto.
  - intros H x.
    wunfold H; wunfold H; inversion H; auto_inj_pair2; subst.
    edestruct EUTTK; eauto with paco.
Qed.

Lemma eutt_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  @eutt E R1 R2 RR (Ret r1) (Ret r2) <-> RR r1 r2.
Proof.
  split.
  - intros H. wunfold H; wunfold H; inversion H; auto.
  - intros. wstep; wstep; econstructor. auto.
Qed.

Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  wstep. wstep. econstructor.
  destruct (observe t); eauto with paco.
  - constructor. apply reflexivity.
  - constructor. intros. left. apply reflexivity.
Qed.

Lemma eutt0_tau_left {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) r rg r0 rg0 (x: itree E _) y: 
  wcpn2 (eutt0_ RR (wcpn2 (eutt0 RR) r rg)) r0 rg0 x y ->
  wcpn2 (eutt0_ RR (wcpn2 (eutt0 RR) r rg)) r0 rg0 (Tau x) y.
Proof.
  intros.
  rewrite <- (bind_ret_ () (fun _ => y)), <- (bind_ret_ () (fun _ => x)), <- bind_tau_.
  wclo eutt0_clo_bind. econstructor.
  - rewrite tau_eutt. reflexivity.
  - intros; subst. eauto.
Qed.

Lemma eutt0_tau_right {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) r rg r0 rg0 (x: itree E _) y:
  wcpn2 (eutt0_ RR (wcpn2 (eutt0 RR) r rg)) r0 rg0 x y ->
  wcpn2 (eutt0_ RR (wcpn2 (eutt0 RR) r rg)) r0 rg0 x (Tau y).
Proof.
  intros.
  rewrite <- (bind_ret_ () (fun _ => y)), <- (bind_ret_ () (fun _ => x)), <- bind_tau_.
  wclo eutt0_clo_bind. econstructor.
  - rewrite tau_eutt. reflexivity.
  - intros; subst. eauto.
Qed.

Global Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt eq ==> eutt eq) (@ITree.map E R S).
Proof.
  unfold ITree.map. do 3 red. intros.
  rewrite H0. setoid_rewrite H. reflexivity.
Qed.

Global Instance eutt_forever {E R S} :
  Proper (eutt eq ==> eutt eq) (@ITree.forever E R S).
Proof.
  wcofix CIH; wstep. wcofix CIH'. intros.
  rewrite (unfold_forever x), (unfold_forever y).
  wclo eutt0_clo_bind. econstructor; eauto.
  intros. subst. wstep. econstructor. eauto with paco.
Qed.

Global Instance eutt_when {E} (b : bool) :
  Proper (eutt eq ==> eutt eq) (@ITree.when E b).
Proof.
  repeat intro. destruct b; simpl; eauto. reflexivity.
Qed.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    eutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
                  @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  wclo eutt_clo_bind. eauto 7 with paco.
Qed.

Lemma unfold_aloop' {E A B} (f : A -> itree E A + B) (x : A) :
  observing eq
    (ITree.aloop f x)
    (ITree._aloop (fun t => Tau t) (ITree.aloop f) (f x)).
Proof.
  constructor; reflexivity.
Qed.

Lemma unfold_aloop {E A B} (f : A -> itree E A + B) (x : A) :
    ITree.aloop f x
  ≈ ITree._aloop id (ITree.aloop f) (f x).
Proof.
  rewrite unfold_aloop'; unfold ITree._aloop.
  destruct f.
  - rewrite tau_eutt; reflexivity.
  - reflexivity.
Qed.

Lemma bind_aloop {E A B C} (f : A -> itree E A + B) (g : B -> itree E B + C): forall x,
    (ITree.aloop f x >>= ITree.aloop g)
  ≈ ITree.aloop (fun ab =>
       match ab with
       | inl a => inl (ITree._aloop id (fun a => Ret (inl a))
                                    (bimap (id_ _) inr (f a)))
       | inr b => bimap (ITree.map inr) (id_ _) (g b)
       end) (inl x).
Proof.
  wcofix CIH; wstep. wcofix CIH'. intros.
  rewrite !unfold_aloop'. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite bind_tau. wstep. constructor.
    rewrite !bind_bind.
    wclo eutt0_clo_bind. econstructor.
    { reflexivity. }
    intros ? _ [].
    rewrite bind_ret.
    eauto with paco.
  - rewrite bind_ret_. apply eutt0_tau_right.
    rewrite bind_ret_.
    revert b. wcofix CIH''; [contradiction|]. intros.
    rewrite !unfold_aloop'. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn.
    + rewrite map_bind. wstep. constructor.
      wclo eutt0_clo_bind. econstructor; [reflexivity|].
      intros. subst. eauto with paco.
    + wstep. econstructor. reflexivity.
Qed.

(** ** Tactics *)

(** Remove all taus from the left hand side of the goal
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps :=
  repeat (
      rewrite itree_eta at 1; cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] => fail 1
      | _ => try rewrite tau_eutt
      end).
