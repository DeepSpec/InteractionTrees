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
              (eutt_taus: itree' E R1 -> itree' E R2 -> Prop)
  : itree' E R1 -> itree' E R2 -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF eutt eutt_taus (RetF r1) (RetF r2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, eutt (k1 x) (k2 x) \/ eutt_taus (observe (k1 x)) (observe (k2 x))):
    euttF eutt eutt_taus (VisF e k1) (VisF e k2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt_taus (observe t1) (observe t2)):
    euttF eutt eutt_taus (TauF t1) (TauF t2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF eutt eutt_taus (observe t1) ot2):
    euttF eutt eutt_taus (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF eutt eutt_taus ot1 (observe t2)):
    euttF eutt eutt_taus ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt_ eutt t1 t2 := cpn2 (euttF eutt) bot2 (observe t1) (observe t2).
Hint Unfold eutt_.

Lemma euttF_mon r r' s s' x y
    (EUTT: euttF r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF r' s' x y.
Proof.
  induction EUTT; eauto.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Lemma monotone_euttF eutt : monotone2 (euttF eutt).
Proof. repeat intro. eauto using euttF_mon. Qed.
Hint Resolve monotone_euttF : paco.

Lemma monotone_eutt_ : monotone2 eutt_.
Proof. red. intros. eapply cpn2_mon_bot; eauto using euttF_mon. Qed.
Hint Resolve monotone_eutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : itree E R1 -> itree E R2 -> Prop := cpn2 eutt_ bot2.
Hint Unfold eutt.

Lemma eutt_fold :
  eutt <2= cpn2 eutt_ bot2.
Proof. intros. apply PR. Qed.
Hint Resolve eutt_fold.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors euttF.
Hint Unfold eutt_.
Hint Resolve monotone_euttF : paco.
Hint Resolve monotone_eutt_ : paco.
Hint Unfold eutt.
Hint Resolve eutt_fold.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  ucofix CIH. intros. ustep. revert_until CIH. ucofix CIH'. intros.
  uunfold H0. inv H0; eauto 8 with paco.
Qed.

Global Instance Reflexive_eutt_gen `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (cpn2 (eutt_ RR) r).
Proof.
  ucofix CIH. intros. ustep. revert x. ucofix CIH'. intros.
  genobs_clear x ox. destruct ox; eauto 7 with paco.
Qed.

Global Instance Reflexive_euttF_gen `{Reflexive _ RR}
       (r : relation (itree E R)) (r' : relation (itree' E R)) :
  Reflexive (euttF RR (cpn2 (eutt_ RR) r) (cpn2 (euttF RR (cpn2 (eutt_ RR) r)) r')).
Proof.
  repeat intro. assert (X := Reflexive_eutt_gen bot2 (go x)). do 2 uunfold X.
  eauto 7 using euttF_mon, cpn2_mon_bot with paco.
Qed.

Global Instance Reflexive_eutt_gen_guard `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eutt_ RR) r).
Proof.
  ustep. intros. apply Reflexive_euttF_gen.
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

Lemma Symmetric_eutt__hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1) :
  forall (ot1 : itree' E R1) (ot2 : itree' E R2),
    cpn2 (euttF RR1 bot2) bot2 ot1 ot2 ->
    cpn2 (euttF RR2 bot2) bot2 ot2 ot1.
Proof.
  ucofix CIH. intros. uunfold H0.
  induction H0; eauto 7 with paco.
  econstructor. intros. edestruct EUTTK; [contradiction|]; eauto with paco.
Qed.

Lemma Symmetric_eutt_hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    cpn2 (eutt_ RR1) bot2 t1 t2 -> cpn2 (eutt_ RR2) bot2 t2 t1.
Proof.
  ucofix CIH. red. ucofix CIH'. intros.
  do 2 uunfold H0.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  induction H0; eauto 7 with paco.
  econstructor; intros.
  edestruct EUTTK as [TMP | TMP]; [eauto 7 with paco|].
  left. ubase. apply CIH. ustep. eauto.
Qed.

Lemma euttF_elim_tau_left {R1 R2} (RR: R1 -> R2 -> Prop) r (t1: itree E R1) (ot2: itree' E R2)
    (REL : euttF RR r (cpn2 (euttF RR r) bot2) (TauF t1) ot2) :
  euttF RR r (cpn2 (euttF RR r) bot2) (observe t1) ot2.
Proof.
  remember (TauF t1) as ott1.
  move REL before r. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott1; eauto.
  uunfold EQTAUS. eauto.
Qed.

Lemma euttF_elim_tau_right {R1 R2} (RR: R1 -> R2 -> Prop) r (ot1: itree' E R1) (t2: itree E R2)
    (REL : euttF RR r (cpn2 (euttF RR r) bot2) ot1 (TauF t2)) :
  euttF RR r (cpn2 (euttF RR r) bot2) ot1 (observe t2).
Proof.
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

Section EUTT_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive eutt_trans_left_clo (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| eutt_trans_left_clo_intro t1 t2 t3
      (EQV: t1 ≈ t2)
      (REL: r t2 t3)
  : eutt_trans_left_clo r t1 t3
.
Hint Constructors eutt_trans_left_clo.

Lemma eutt_clo_trans_left : eutt_trans_left_clo <3= cpn2 (@eutt_ E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. ucofix CIH. intros.
  uunfold REL. do 2 uunfold EQV.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV. repeat red.
  induction EQV; intros; subst.
  - eauto 8 using euttF_mon, cpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot3) eqn: ISTAU.
    + destruct ot3; inv ISTAU.
      econstructor. ubase. eapply CIH. eauto with paco.
      ustep.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. genobs_clear t2 ot.
      move REL before CIH. revert_until REL.
      induction REL; intros; inv H0.
      * uunfold EQTAUS.
        genobs_clear t1 ot1. remember (RetF r1) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
      * uunfold EQTAUS.
        genobs_clear t1 ot1. remember (VisF e k1) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
        econstructor. intros.
        edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
      * eapply IHREL; eauto.
        uunfold EQTAUS. ustep.
        eapply euttF_elim_tau_right in EQTAUS. eauto.
  - eauto 8 using euttF_mon, cpn2_mon_bot with rclo paco.
  - remember (TauF t2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7 with paco.
    uunfold EQTAUS. eauto.
Qed.

Inductive eutt_trans_right_clo (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| eutt_trans_right_clo_intro t1 t2 t3
      (EQV: t3 ≈ t2)
      (REL: r t1 t2)
  : eutt_trans_right_clo r t1 t3
.
Hint Constructors eutt_trans_right_clo.

Lemma eutt_clo_trans_right : eutt_trans_right_clo <3= cpn2 (@eutt_ E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. ucofix CIH. intros.
  uunfold REL. do 2 uunfold EQV.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV. repeat red.
  induction EQV; intros; subst.
  - eauto 8 using euttF_mon, cpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot1) eqn: ISTAU.
    + destruct ot1; inv ISTAU.
      econstructor. ubase. eapply CIH. eauto with paco.
      ustep.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. genobs_clear t2 ot.
      move REL before CIH. revert_until REL.
      induction REL; intros; inv H0.
      * uunfold EQTAUS.
        genobs_clear t1 ot1. remember (RetF r2) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
      * uunfold EQTAUS.
        genobs_clear t1 ot1. remember (VisF e k2) as o.
        move EQTAUS before CIH. revert_until EQTAUS.
        induction EQTAUS; intros; subst; try dependent destruction Heqo; eauto 7.
        econstructor. intros.
        edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
      * eapply IHREL; eauto.
        uunfold EQTAUS. ustep.
        eapply euttF_elim_tau_right in EQTAUS. eauto.
  - eauto 8 using euttF_mon, cpn2_mon_bot with rclo paco.
  - remember (TauF t2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7 with paco.
    uunfold EQTAUS. eauto.
Qed.

Inductive eutt_bind_clo {E R1 R2} (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| eutt_bind_clo_intro U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (k1 v1) (k2 v2))
  : @eutt_bind_clo E R1 R2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
    (* TODO: 8.8 doesn't like the implicit arguments *)
.
Hint Constructors eutt_bind_clo.

Lemma eutt_clo_bind : eutt_bind_clo <3= cpn2 (@eutt_ E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  assert (RELk: forall v1 v2, RU v1 v2 -> eutt_ RR r (k1 v1) (k2 v2)) by eauto.
  revert_until r. ucofix CIH. intros.
  do 2 uunfold EQV.
  rewrite !unfold_bind.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - specialize (RELk _ _ RBASE). uunfold RELk.
    eauto 8 using euttF_mon, cpn2_mon_bot with rclo paco.
  - econstructor. intros.
    edestruct EUTTK; eauto 7 with rclo paco.
  - simpl. eauto 8 with paco.
  - econstructor. rewrite unfold_bind. gcpn_fold. eauto.
  - econstructor. rewrite unfold_bind. gcpn_fold. eauto.
Qed.

Global Instance eutt_cong_cpn r :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (cpn2 (@eutt_ E R1 R2 RR) r).
Proof.
  repeat intro.
  uclo eutt_clo_trans_left. econstructor; eauto.
  uclo eutt_clo_trans_right. econstructor; eauto.
Qed.

Global Instance eutt_cong_gcpn r :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gcpn2 (@eutt_ E R1 R2 RR) r).
Proof.
  repeat intro.
  uclo eutt_clo_trans_left. econstructor; eauto.
  uclo eutt_clo_trans_right. econstructor; eauto.
Qed.

Global Instance eutt_eq_under_rr_impl :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> flip impl) (eutt RR).
Proof.
  repeat red. intros. rewrite H, H0. eauto with paco.
Qed.

End EUTT_upto.

Arguments eutt_clo_trans_left : clear implicits.
Hint Constructors eutt_trans_left_clo.

Arguments eutt_clo_trans_right : clear implicits.
Hint Constructors eutt_trans_right_clo.

Arguments eutt_clo_bind : clear implicits.
Hint Constructors eutt_bind_clo.

Global Instance eutt_bind {E U R} :
  Proper (pointwise_relation _ (eutt eq) ==>
          eutt eq ==>
          eutt eq) (@ITree.bind' E U R).
Proof.
  uclo eutt_clo_bind. econstructor; eauto.
  intros. subst. eauto with paco.
Qed.

Section EUTT_nested.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive eutt_nested_trans_clo (r: itree' E R1 -> itree' E R2 -> Prop) :
  itree' E R1 -> itree' E R2 -> Prop :=
| eutt_nested_trans_clo_intro ot1 ot2 ot3 ot4
      (EQVl: go ot1 ≅ go ot2)
      (EQVr: go ot4 ≅ go ot3)
      (REL: r ot2 ot3)
  : eutt_nested_trans_clo r ot1 ot4
.
Hint Constructors eutt_nested_trans_clo.

Lemma eutt_nested_clo_trans r :
  eutt_nested_trans_clo <3= cpn2 (euttF RR (cpn2 (eutt_ RR) r)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  uunfold EQVl; red in EQVl. uunfold EQVr; red in EQVr. simpl in *.
  move REL before r0. revert_until REL.
  induction REL; intros; subst; repeat red in EQVl; repeat red in EQVr; simpl in *;
    try (dependent destruction EQVl; dependent destruction EQVr; []).
  - eauto.
  - econstructor. intros.
    edestruct EUTTK.
    + left. rewrite REL, REL0. eauto.
    + right. eapply rclo2_clo.
      econstructor.
      * instantiate (1:= observe(k1 x)). rewrite <- !itree_eta. eauto.
      * instantiate (1:= observe(k2 x)). rewrite <- !itree_eta. eauto.
      * eauto with rclo.
  - econstructor. eapply rclo2_clo. econstructor.
    + rewrite REL. reflexivity.
    + rewrite REL0. reflexivity.
    + eauto with rclo.
  - dependent destruction EQVl. uunfold REL0. eauto.
  - dependent destruction EQVr. uunfold REL0. eauto.
Qed.

Global Instance eq_cong_nested_cpn r r0 :
  Proper (going (eq_itree eq) ==> going (eq_itree eq) ==> flip impl)
         (cpn2 (@euttF E R1 R2 RR (cpn2 (eutt_ RR) r)) r0).
Proof.
  repeat intro. destruct H, H0.
  uclo eutt_nested_clo_trans. econstructor; eauto.
Qed.

Global Instance eq_cong_nested_gcpn r r0 :
  Proper (going (eq_itree eq) ==> going (eq_itree eq) ==> flip impl)
         (gcpn2 (@euttF E R1 R2 RR (cpn2 (eutt_ RR) r)) r0).
Proof.
  repeat intro. destruct H, H0.
  uclo eutt_nested_clo_trans. econstructor; eauto.
Qed.

Inductive eutt_nested_bind_clo (r: itree' E R1 -> itree' E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=
| eutt_nested_bind_clo_intro U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (observe (k1 v1)) (observe (k2 v2)))
  : eutt_nested_bind_clo r (observe (ITree.bind t1 k1)) (observe (ITree.bind t2 k2))
.
Hint Constructors eutt_nested_bind_clo.

Lemma eutt_nested_clo_bind r :
  eutt_nested_bind_clo <3= cpn2 (euttF RR (cpn2 (eutt_ RR) r)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  assert (RELk: forall v1 v2, RU v1 v2 -> euttF RR (cpn2 (eutt_ RR) r) r0 (observe (k1 v1)) (observe (k2 v2))) by eauto.
  do 2 uunfold EQV.
  rewrite !unfold_bind.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  move EQV before RU. revert_until EQV.
  induction EQV; intros; subst.
  - specialize (RELk _ _ RBASE). 
    eauto 7 using euttF_mon, upaco2_mon_bot with rclo.
  - econstructor. intros.
    edestruct EUTTK; right; eapply rclo2_clo; eauto 7 using euttF_mon with rclo paco.
  - simpl. econstructor. eapply rclo2_clo; eauto 7 with rclo paco.
  - econstructor. rewrite unfold_bind. eauto.
  - econstructor. rewrite unfold_bind. eauto.
Qed.

End EUTT_nested.

Arguments eutt_nested_clo_trans : clear implicits.
Hint Constructors eutt_nested_trans_clo.

Arguments eutt_nested_clo_bind : clear implicits.
Hint Constructors eutt_nested_bind_clo.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance subrelation_observing_eutt:
  @subrelation (itree E R) (observing eq) eutt.
Proof.
  repeat intro. eapply subrelation_eq_eutt, observing_eq_itree_eq. eauto.
Qed.

Global Instance Reflexive_eutt: Reflexive eutt.
Proof. apply Reflexive_eutt_gen; eauto. Qed.

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
  constructor. uunfold H. ustep. destruct H. econstructor; eauto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. ustep. ustep. econstructor. uunfold H. eauto.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof. 
  constructor. ustep. ustep. econstructor.
  intros. specialize (H x0). uunfold H. eauto.
Qed.

End EUTT_eq.

(**)

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

Global Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt eq ==> eutt eq) (@ITree.map E R S).
Proof.
  unfold ITree.map. do 3 red. intros.
  rewrite H0. setoid_rewrite H. reflexivity.
Qed.

Global Instance eutt_forever {E R S} :
  Proper (eutt eq ==> eutt eq) (@ITree.forever E R S).
Proof.
  ucofix CIH. red. ucofix CIH'. intros.
  rewrite (unfold_forever x), (unfold_forever y).
  uclo eutt_nested_clo_bind. econstructor; eauto.
  intros. subst. simpl. eauto 7 with paco.
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

 
Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  ustep. ustep. econstructor. reflexivity.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    eutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
                  @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  uclo eutt_clo_bind. eauto 7 with paco.
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
  ucofix CIH. red. ucofix CIH'. intros.
  rewrite !unfold_aloop'. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite 2 bind_bind.
    constructor.
    uclo eutt_nested_clo_bind. econstructor.
    { reflexivity. }
    intros ? _ [].
    rewrite bind_ret.
    eauto with paco.
  - rewrite bind_ret.
    constructor. gcpn_fold.
    rewrite bind_ret.
    revert b. ucofix CIH''. intros.
    rewrite !unfold_aloop'. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn.
    + rewrite map_bind. constructor.
      uclo eutt_nested_clo_bind. econstructor; [reflexivity|].
      intros. subst. eauto with paco.
    + eauto with paco.
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
