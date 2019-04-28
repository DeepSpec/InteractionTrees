(** * Equivalence up to taus *)

(** Abbreviated as [eutt]. *)

(** We consider [Tau] as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many [Tau]s between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** A rewrite hint database named [itree] is available via the tactic
    [autorewrite with itree] as a custom simplifier of expressions using
    mainly [Ret], [Tau], [Vis], [ITree.bind] and [ITree.Interp.Interp.interp].
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eq.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)

(** Splitting things this way makes the library easier to build in parallel.
 *)

(* begin hide *)
Require Import Paco.paco Program Setoid Morphisms RelationClasses.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition transU := @eqit_trans_clo E R1 R2 true true true true.
Definition transD := @eqit_trans_clo E R1 R2 true true false false.
Definition bindC := @eqit_bind_clo E R1 R2 true true.

Definition euttVC gH r :=
  transU (gupaco2 (eqit_ RR true true id) (eqitC true true) (transU (r \2/ gH))).

Variant euttG rH rL gL gH t1 t2 : Prop :=
| euttG_intro
    (IN: gpaco2 (@eqit_ E R1 R2 RR true true (euttVC gH))
                (eqitC true true)
                (transU rH \2/ transD rL)
                (transU rH \2/ transD rL \2/ transD gL) t1 t2)
.

Hint Unfold transU transD bindC euttVC.
Hint Constructors euttG.

Lemma transD_mon r1 r2 t1 t2
      (IN: transD r1 t1 t2)
      (LE: r1 <2= r2):
  transD r2 t1 t2.
Proof. eapply eqitC_mon, LE; eauto. Qed.

Lemma transU_mon r1 r2 t1 t2
      (IN: transU r1 t1 t2)
      (LE: r1 <2= r2):
  transU r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Lemma transDleU: transD <3= transU.
Proof.
  intros. destruct PR. econstructor; eauto using eqit_mon.
Qed.

Lemma transD_compose:
  compose transD transD <3= transD.
Proof.
  intros. destruct PR. destruct REL.
  econstructor; cycle -1; eauto; eapply eqit_trans; eauto using eqit_mon.
Qed.

Lemma transU_compose:
  compose transU transU <3= transU.
Proof.
  intros. destruct PR. destruct REL.
  econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon.
Qed.

Hint Resolve transD_mon transU_mon : paco.

Lemma euttVC_mon gH:
  monotone2 (euttVC gH).
Proof.
  red; intros. eapply transU_mon; eauto. intros.
  eapply gupaco2_mon; eauto. intros.
  eapply transU_mon; eauto. intros.
  destruct PR1; eauto.
Qed.
Hint Resolve euttVC_mon : paco.

Lemma euttVC_compat gH:
  compose (eqitC true true) (euttVC gH) <3= compose (euttVC gH) (eqitC true true).
Proof.
  intros. apply transU_compose. apply transDleU.
  eapply transD_mon; eauto. intros.
  eapply transU_mon; eauto. intros.
  eapply gupaco2_mon; eauto; intros.
  eapply transU_mon; eauto. intros.
  destruct PR3; eauto.
  left. econstructor; eauto; reflexivity.
Qed.
Hint Resolve euttVC_compat : paco.

Lemma euttVC_id gH:
  id <3= euttVC gH.
Proof.
  intros. econstructor; try reflexivity. gbase. econstructor; eauto; reflexivity.
Qed.
Hint Resolve euttVC_id : paco.

Global Instance euttG_cong_euttge rH rL gL gH:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. econstructor. destruct H1. guclo eqit_clo_trans.
Qed.
Global Instance euttG_cong_eq rH rL gL gH:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. eapply euttG_cong_euttge; eauto; apply eq_sub_eqit; eauto.
Qed.

Global Instance geuttG_cong_euttge gH r g:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (eqit_ RR true true (euttVC gH)) (eqitC true true) r g).
Proof.
  repeat intro. guclo eqit_clo_trans. 
Qed.
Global Instance geuttG_cong_eq gH r g:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (eqit_ RR true true (euttVC gH)) (eqitC true true) r g).
Proof.
  repeat intro. eapply geuttG_cong_euttge; eauto using eqit_mon.
Qed.

End EUTTG.

Hint Unfold transU transD bindC euttVC.
Hint Constructors euttG.
Hint Resolve transD_mon transU_mon : paco.
Hint Resolve euttVC_mon : paco.
Hint Resolve euttVC_compat : paco.
Hint Resolve euttVC_id : paco.

Section EUTTG_Properties1.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma rclo_transD r:
  rclo2 transD r <2= @transD E R1 R2 r.
Proof.
  intros. induction PR.
  - econstructor; eauto; reflexivity.
  - destruct IN. apply H in REL. destruct REL.
    econstructor; cycle -1; eauto using eqit_trans.
Qed.

Lemma rclo_flip clo (r: itree E R1 -> itree E R2 -> Prop)
      (MON: monotone2 clo):
  flip (rclo2 (fun x : itree E R2 -> itree E R1 -> Prop => flip (clo (flip x))) (flip r)) <2= rclo2 clo r.
Proof.
  intros. induction PR; eauto with paco.
  apply rclo2_clo; eauto.
Qed.

Lemma transD_flip r:
  flip (transD (flip r)) <2= @transD E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma transU_flip r:
  flip (transU (flip r)) <2= @transU E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma eqitC_flip r:
  flip (eqitC true true (flip r)) <2= @eqitC E R1 R2 true true r.
Proof. eapply transD_flip. Qed.

Lemma euttVC_flip gH r:
  flip (euttVC (flip RR) (flip gH) (flip r)) <2= @euttVC E R1 R2 RR gH r.
Proof.
  intros. eapply transU_flip. eapply transU_mon; eauto.
  gcofix CIH. intros. gunfold PR0. econstructor.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto using eqitC_flip. intros.
  destruct PR1; eauto using transU_flip.
  left. pstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco. intros.
  apply rclo2_base. right. left. eapply CIH.
  eapply gupaco2_mon; eauto. intros.
  destruct PR1; eauto. destruct PR2; eauto.
Qed.

Lemma euttG_flip gH r:
  flip (gupaco2 (eqit_ (flip RR) true true (euttVC (flip RR) (flip gH))) (eqitC true true) (flip r)) <2=
  gupaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (eqitC true true) r.
Proof.
  gcofix CIH; intros.
  destruct PR. econstructor.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto using eqitC_flip. intros.
  destruct PR; eauto.
  left. punfold H. pstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco; intros.
  - eapply euttVC_flip. apply PR.
  - apply rclo_flip; eauto with paco.
    eapply rclo2_mon_gen; eauto using eqitC_flip with paco.
    intros. right. left. destruct PR0.
    + eapply CIH. red. eauto with paco.
    + apply CIH0. destruct H0; eauto.
Qed.

Lemma eqit_ret_gen {R} t1 v
      (IN: @eqit E R R eq true true t1 (Ret v)):
  eqit eq true false t1 (Ret v).
Proof.
  punfold IN. pstep. red in IN |- *. simpl in *.
  remember (RetF v) as ot.
  hinduction IN before R; intros; subst; eauto; inv Heqot.
Qed.

Lemma euttG_transU_auxL gH r t1 t2 t'
      (CLOR: transU r <2= r)
      (EQ: t1 ≈ t')
      (REL: gupaco2 (@eqit_ E _ _ RR true true (euttVC RR gH)) (eqitC true true) r t' t2):
  gupaco2 (eqit_ RR true true (euttVC RR gH)) (eqitC true true) r t1 t2.
Proof.
  apply gpaco2_dist in REL; eauto with paco. destruct REL; cycle 1.
  { apply rclo_transD in H.
    gbase. apply CLOR. apply transU_compose.
    econstructor; eauto using transDleU; reflexivity.
  }
  assert (REL: paco2 (eqit_ RR true true (euttVC RR gH)) r t' t2).
  { eapply paco2_mon; eauto. intros.
    apply rclo_transD in PR. apply CLOR.
    destruct PR, REL; econstructor; eauto using eqit_mon.
  }
  clear H.
  revert t1 t2 t' EQ REL. gcofix CIH. intros.
  punfold EQ. red in EQ. punfold REL. red in REL. genobs t1 ot1. genobs t' ot'.
  hinduction EQ before CIH; intros; subst.
  - remember (RetF r2) as ot. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst; try inv Heqot.
    + gstep. red. simpobs. eauto.
    + rewrite (simpobs Heqot1), (simpobs Heqot2), tau_eutt. eauto.
  - pclearbot. apply eqit_tauR in REL. rewrite Heqot' in REL, REL0. clear m2 Heqot'.
    genobs t' ot'. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst.
    + apply eqit_ret_gen in REL0.
      rewrite (simpobs Heqot1), (simpobs Heqot2), tau_eutt, REL0.
      gstep. econstructor. eauto.
    + gstep. red. simpobs. econstructor. gbase.
      destruct REL.
      * eapply CIH; cycle -1; eauto using paco2_mon.
        rewrite REL0, tau_eutt. reflexivity.
      * eapply CIH0. eapply CLOR.
        econstructor; cycle -1; eauto; try reflexivity.
        rewrite REL0, tau_eutt. reflexivity.
    + punfold REL0. red in REL0. simpl in *.
      remember (VisF e k1) as ot. genobs m1 om1.
      hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot.
      * gstep. red. simpobs. econstructor; eauto. simpobs. econstructor. intros.
        pclearbot. apply transU_compose. econstructor; eauto; try reflexivity.
        eapply transU_mon. apply REL0. intros.
        eapply gupaco2_mon; eauto. intros.
        eapply transU_mon; eauto. intros.
        destruct PR1; eauto.
        left. gfinal. destruct H; eauto.
        right. eapply paco2_mon; eauto.
      * rewrite (simpobs Heqot1), tau_eutt. eauto.
    + eapply IHREL0; eauto.
      rewrite REL, <-itree_eta, tau_eutt. reflexivity.
    + rewrite (simpobs Heqot2), tau_eutt. eauto.
  - remember (VisF e k2) as ot. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot.
    + gstep. red. simpobs. econstructor.
      intros. pclearbot.
      apply transU_compose. econstructor; eauto; try reflexivity.
      eapply transU_mon. apply REL. intros.
      eapply gupaco2_mon. eauto. intros.
      eapply transU_mon. eauto. intros.
      destruct PR; eauto.
      destruct PR1; eauto.
      left. gfinal. destruct H; eauto.
      right. eapply paco2_mon; eauto.
    + rewrite (simpobs Heqot2), tau_eutt. eauto.
  - rewrite (simpobs Heqot1), tau_eutt. eauto.
  - clear t' Heqot'. remember (TauF t2) as ot. genobs t0 ot0.
    hinduction REL before EQ; intros; subst; try inv Heqot; eauto.
    + destruct REL; cycle 1.
      * gbase. apply CLOR. econstructor; cycle -1; eauto.
        rewrite (simpobs Heqot0), tau_eutt. reflexivity.
      * eapply IHEQ; eauto.
        simpobs. econstructor; eauto.
        pstep_reverse.
    + rewrite (simpobs Heqot0), tau_eutt. eauto.
Qed.

End EUTTG_Properties1.

Section EUTTG_Properties2.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma euttG_transU_auxR gH r t1 t2 t'
      (CLOR: transU r <2= r)
      (EQ: t' ≈ t2)
      (REL: gupaco2 (@eqit_ E _ _ RR true true (euttVC RR gH)) (eqitC true true) r t1 t'):
  gupaco2 (eqit_ RR true true (euttVC RR gH)) (eqitC true true) r t1 t2.
Proof.
  symmetry in EQ. apply euttG_flip.
  eapply euttG_transU_auxL; eauto using transU_flip.
  apply euttG_flip. eauto.
Qed.

Lemma euttG_transU_aux gH r
      (CLOR: transU r <2= r):
  transU (gupaco2 (eqit_ RR true true (euttVC RR gH)) (eqitC true true) r) <2= 
  gupaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (eqitC true true) r.
Proof.
  intros. destruct PR. symmetry in EQVr.
  eapply euttG_transU_auxL; eauto.
  eapply euttG_transU_auxR; eauto.
Qed.

Lemma euttVC_gen gH r:
  transU (gupaco2 (eqit_ RR true true (euttVC RR gH)) (eqitC true true) (transU (r \2/ gH)))
  <2= @euttVC E R1 R2 RR gH r.
Proof.
  econstructor; try reflexivity.
  revert x0 x1 PR. gcofix CIH. intros.
  eapply euttG_transU_aux in PR; eauto using transU_compose.
  gunfold PR. econstructor.
  eapply rclo2_mon; eauto. intros.
  destruct PR0; eauto.
  left. pstep. repeat red. red in H. induction H; eauto.
  - econstructor. apply rclo2_base. right. left. eapply CIH.
    econstructor; try reflexivity.
    eapply gupaco2_mon; eauto.
    intros. destruct PR0; eauto.
  - econstructor. intros. apply rclo2_base. right. left. eapply CIH.
    eapply transU_mon. apply REL. intros.
    gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
    + eapply eqitF_mono; eauto with paco.
    + eapply euttG_transU_aux; eauto using transU_compose.
      eapply transU_mon. apply PR1. intros.
      destruct PR2; cycle 1.
      * gbase. econstructor; try reflexivity; eauto.
      * eapply gupaco2_mon; eauto. intros.
        destruct PR2; eauto.
Qed.

Lemma euttG_cofix_aux: forall rH rL gL gH x,
    (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).
Proof.
  econstructor. revert x0 x1 PR. gcofix CIH.
  intros. apply H in PR. destruct PR.
  revert_until CIH. gcofix CIH. intros.
  apply gpaco2_dist in IN; eauto with paco.
  destruct IN; cycle 1.
  { gbase. apply rclo2_dist in H0; eauto with paco.
    destruct H0; apply rclo_transD in H0;
      eauto using transU_compose, transD_compose, transDleU.
  }
  punfold H0. gstep. red in H0 |- *.
  induction H0; eauto.
  - econstructor. destruct REL.
    + gbase. apply CIH1. gfinal. right.
      eapply paco2_mon; eauto. intros.
      repeat (apply rclo2_dist in PR; eauto with paco; destruct PR as [PR|PR]);
        apply rclo_transD in PR; eauto 7 using transDleU, transU_compose, transD_compose.
    + repeat (apply rclo2_dist in H0; eauto with paco; destruct H0 as [H0|H0]);
        apply rclo_transD in H0; eauto 8 using transDleU, transU_compose, transD_compose with paco.
      apply transD_compose in H0. gclo. eapply transD_mon; eauto. intros.
      destruct PR; eauto with paco.
      gbase. apply CIH0. right. econstructor; eauto; reflexivity.
  - econstructor. intros.
    eapply transU_mon. apply REL. intros.
    eapply gupaco2_mon; eauto. intros.
    eapply transU_mon; eauto. intros.
    destruct PR1; [|destruct H0; eauto with paco].
    destruct H0.
    + left. gbase. apply CIH1. gfinal. right.
      eapply paco2_mon; eauto. intros.
      repeat (apply rclo2_dist in PR1; eauto with paco; destruct PR1 as [PR1|PR1]);
        apply rclo_transD in PR1; eauto 7 using transDleU, transU_compose, transD_compose.
    + left.
      repeat (apply rclo2_dist in H0; eauto with paco; destruct H0 as [H0|H0]);
        apply rclo_transD in H0; eauto 8 using transDleU, transU_compose, transD_compose with paco.
      apply transD_compose in H0. gclo. eapply transD_mon; eauto. intros.
      destruct PR; eauto with paco.
      gbase. destruct PR1; eauto.
      apply CIH0. right. econstructor; eauto; reflexivity.
Qed.

End EUTTG_Properties2.

Require Import Paco.pacotac_internal.

Section EUTTG_principles.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

(* Make new hypotheses *)

Lemma euttG_cofix rH rL gL gH x
      (OBG: forall gL' (INCL: gL <2= gL') (CIHL: x <2= gL') gH' (INCH: gH <2= gH') (CIHH: x <2= gH'), x <2= euttG rH rL gL' gH'):
    x <2= euttG rH rL gL gH.
Proof.
  eapply euttG_cofix_aux; intros.
  eapply OBG; eauto.
Qed.

(* Process itrees *)

Lemma euttG_ret: forall rH rL gL gH v1 v2,
  RR v1 v2 -> euttG rH rL gL gH (Ret v1) (Ret v2).
Proof.
  econstructor. gstep. econstructor. eauto.
Qed.

Lemma euttG_bind: forall rH rL gL gH t1 t2,
  bindC (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. guclo eqit_clo_bind.
  destruct H. econstructor; eauto.
  intros. edestruct REL; eauto.
Qed.

Lemma euttG_transD: forall rH rL gL gH t1 t2,
  transD (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. guclo eqit_clo_trans.
  destruct H. econstructor; eauto.
  edestruct REL; eauto.
Qed.

(* Lose weak hypotheses after general rewriting *)

Lemma euttG_transU rH rL gL gH t1 t2:
  transU (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros.
  cut (gupaco2 (eqit_ RR true true (euttVC RR gH)) (eqitC true true) (transU rH) t1 t2).
  { intros. econstructor. eauto using gpaco2_mon. }
  eapply euttG_transU_aux; eauto using transU_compose.
  eapply transU_mon; eauto. intros. destruct PR.
  eapply gpaco2_mon; eauto; intros;
    repeat destruct PR as [PR|PR]; eauto using transDleU.
Qed.

(* Make a weakly guarded progress *)

Lemma euttG_tau: forall rH rL gL gH t1 t2,
  euttG rH gL gL gH t1 t2 -> euttG rH rL gL gH (Tau t1) (Tau t2).
Proof.
  intros. destruct H. econstructor.
  gstep. econstructor.
  eapply gpaco2_mon; eauto; intros; repeat destruct PR as [PR|PR]; eauto.
Qed.

(* Make a strongly guarded progress *)

Lemma euttG_vis: forall rH rL gL gH u (e: E u) k1 k2,
  (forall v, euttG gH gH gH gH (k1 v) (k2 v)) -> euttG rH rL gL gH (Vis e k1) (Vis e k2).
Proof.
  econstructor. gstep. econstructor. intros.
  specialize (H v). destruct H.
  apply euttVC_gen. econstructor; try reflexivity.
  eapply gpaco2_mon_gen; eauto; intros; repeat destruct PR as [PR|PR];
    eauto using gpaco2_clo, transDleU, transU_mon with paco.
Qed.

(* Use available hypotheses *)

Lemma euttG_base: forall rH rL gL gH t1 t2,
  rH t1 t2 \/ rL t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros. econstructor. gbase.
  destruct H; [left|right]; econstructor; eauto; reflexivity.
Qed.

(**
   Correctness
 **)

Lemma euttG_le_eutt:
  euttG bot2 bot2 bot2 bot2 <2= eutt RR.
Proof.
  intros. destruct PR.
  assert(paco2 (eqit_ RR true true (euttVC RR bot2)) bot2 x0 x1).
  { eapply gpaco2_init; eauto with paco.
    eapply gpaco2_mon; eauto; intros;
      repeat destruct PR as [PR|PR]; destruct PR; contradiction.
  }
  clear IN.
  revert x0 x1 H. pcofix CIH. intros.
  punfold H0. pstep. unfold_eqit.
  induction H0; pclearbot; eauto.
  econstructor; intros. specialize (REL v).
  right. apply CIH.
  ginit. apply euttG_transU_aux.
  { intros. destruct PR; contradiction. }
  eapply transU_mon. apply REL. intros.
  gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
  - eapply eqitF_mono; eauto with paco.
  - apply euttG_transU_aux.
    { intros. destruct PR1; contradiction. }
    eapply transU_mon; eauto. intros.
    pclearbot. gfinal. eauto.
Qed.

Lemma eutt_le_euttG rH rL gL gH:
  eutt RR <2= euttG rH rL gL gH.
Proof.
  intros. econstructor. econstructor. apply rclo2_base. left.
  eapply paco2_mon_bot; eauto; intros.
  eapply eqitF_mono; eauto with paco.
Qed.

End EUTTG_principles.

Tactic Notation "ecofix" ident(CIH) "with" ident(gL) ident(gH) :=
  repeat red;
  paco_pre2; eapply euttG_cofix;
  paco_post2 CIH with gL;
  let INC := fresh "_paco_inc_" in
  paco_post_match2 INC ltac:(paco_ren_r gH) paco_ren_pr;
  let CIH := fresh CIH in intro CIH; paco_simp_hyp CIH;
  let CIH' := fresh CIH in try rename INC into CIH'.

Tactic Notation "ecofix" ident(CIH) := ecofix CIH with gL gH.

Ltac eret := under_forall ltac:(eapply euttG_ret; eauto with paco).
Ltac ebind := under_forall ltac:(eapply euttG_bind; eauto with paco).
Ltac etransD := under_forall ltac:(eapply euttG_transD; eauto with paco).
Ltac etransU := under_forall ltac:(eapply euttG_transU; eauto with paco).
Ltac etau := under_forall ltac:(eapply euttG_tau; eauto with paco).
Ltac evis := under_forall ltac:(eapply euttG_vis; eauto with paco).
Ltac ebase := under_forall ltac:(eapply euttG_base; eauto with paco).
Ltac einit := under_forall ltac:(eapply euttG_le_eutt; eauto with paco).
Ltac efinal := under_forall ltac:(eapply eutt_le_euttG; eauto with paco).

Hint Resolve euttG_ret : paco.
Hint Resolve euttG_tau : paco.
Hint Resolve euttG_vis : paco.
Hint Resolve euttG_base : paco.
Hint Resolve euttG_le_eutt: paco.
