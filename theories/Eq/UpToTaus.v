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

Hint Unfold flip.

Lemma simpobs {E R} {ot} {t: itree E R} (EQ: ot = observe t): t ≅ go ot.
Proof.
  pstep. repeat red. simpobs. simpl. subst. pstep_reverse. apply Reflexive_eqit.
Qed.

Lemma eqit_trans {E R} b (t1 t2 t3: itree E R)
      (REL1: eqit eq b false t1 t2)
      (REL2: eqit eq b false t2 t3):
  eqit eq b false t1 t3.
Proof.
  ginit. guclo eqit_clo_trans; eauto.
  econstructor; eauto with paco. reflexivity.
Qed.

(* Lemma *)
(*     paco2 (eqit_ RR true true (eqit_trans_clo true true true true r) *)
(*     (euttGC RR bot2 (upaco2 (eqit_ RR true true (euttGC RR bot2)) bot2)) t1 t2 *)



Lemma eutt_trans {E R} (t1 t2 t3: itree E R)
      (REL1: t1 ≈ t2)
      (REL2: t2 ≈ t3):
  t1 ≈ t3.
Proof.
  revert_until R. pcofix CIH; intros.
  punfold REL1. red in REL1. punfold REL2. red in REL2. pstep. red.
  hinduction REL1 before CIH; clear t1 t2; intros; subst.
  - remember (RetF r2) as ot.
    hinduction REL2 before CIH; intros; subst; try inv Heqot; eauto.
  - remember (TauF m2) as ot.
    hinduction REL2 before CIH; intros; subst; try inv Heqot; pclearbot; eauto.
    econstructor; eauto.
    rewrite (itree_eta' ot2) in REL2. punfold_reverse REL2.
    rewrite (itree_eta' ot2). pstep_reverse.
Admitted.

Instance eutt_gpaco {E R}:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (@eqit E R R eq true true).
Proof.
  repeat intro. eapply eutt_trans; eauto.
  eapply eutt_trans; eauto. symmetry.  eauto.
Qed.

Instance euttge_gpaco {E R}:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (@eqit E R R eq true true).
Proof.
  repeat intro. eapply eutt_gpaco; eauto; apply eqit_sub_eutt; eauto.
Qed.

Instance eq_gpaco {E R}:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R R eq true true).
Proof.
  repeat intro. eapply euttge_gpaco; eauto; apply eq_sub_eqit; eauto.
Qed.

Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition transH := @eqit_trans_clo E R1 R2 true true true true.
Definition transL := @eqit_trans_clo E R1 R2 true true false false.

Definition euttGC gH r := gupaco2 (eqit_ RR true true id) transH (r \2/ gH).

Variant euttG rH rL gL gH t1 t2 : Prop :=
| euttG_intro
    (IN: gpaco2 (@eqit_ E R1 R2 RR true true (euttGC gH))
                (eqitC true true)
                (transH rH \2/ transL rL)
                (transH rH \2/ transL rL \2/ transL gL) t1 t2)
.
Hint Constructors euttG.
Hint Unfold transH transL.

Lemma euttGC_mon gH:
  monotone2 (euttGC gH).
Proof.
  red; intros. eapply gupaco2_mon; eauto. intros.
  destruct PR; eauto.
Qed.

Hint Resolve euttGC_mon : paco.

Lemma euttGC_compat gH:
  compose (eqitC true true) (euttGC gH) <3= compose (euttGC gH) (eqitC true true).
Proof.
  intros. destruct PR. red in REL.
  gclo. econstructor; eauto using eqit_mon.
  eapply gupaco2_mon; eauto. intros.
  destruct PR; eauto.
  left. econstructor; eauto; reflexivity.
Qed.
Hint Resolve euttGC_compat : paco.

Lemma euttGC_id gH:
  id <3= euttGC gH.
Proof.
  intros. gbase. eauto.
Qed.
Hint Resolve euttGC_id : paco.

Global Instance euttge_euttG rH rL gL gH:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. econstructor. destruct H1. guclo eqit_clo_trans.
Qed.

Global Instance eq_euttG rH rL gL gH:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. eapply euttge_euttG; eauto; apply eq_sub_eqit; eauto.
Qed.

Global Instance euttge_euttG_ gH r g:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (eqit_ RR true true (euttGC gH)) (eqitC true true) r g).
Proof.
  repeat intro. guclo eqit_clo_trans. 
Qed.

Global Instance eq_euttG_ gH r g:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (eqit_ RR true true (euttGC gH)) (eqitC true true) r g).
Proof.
  repeat intro. eapply euttge_euttG_; eauto; apply eq_sub_eqit; eauto.
Qed.

Lemma euttGC_gen gH r:
  gupaco2 (eqit_ RR true true (euttGC gH)) transH (r \2/ gH) <2= euttGC gH r.
Proof.
  gcofix CIH. intros. gunfold PR. econstructor.
  eapply rclo2_mon; eauto. intros.
  destruct PR0; eauto.
  left. pstep. repeat red. red in H. induction H; eauto.
  - econstructor. apply rclo2_base. right. left. eapply CIH.
    eapply gupaco2_mon; eauto.
    intros. destruct PR0; eauto.
  - econstructor. intros. apply rclo2_base. right. left. eapply CIH. 
    gupaco. eapply gupaco2_mon_gen; try apply REL; eauto with paco.
    + intros. eapply eqitF_mono; eauto with paco.
    + intros. destruct PR0; eauto with paco.
      eapply gupaco2_mon; eauto. intros.
      destruct PR0; eauto.
Qed.

End EUTTG.

Hint Constructors euttG.
Hint Unfold transH transL.
Hint Resolve euttGC_mon : paco.
Hint Resolve euttGC_compat : paco.
Hint Resolve euttGC_id : paco.

Section Lemmas.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma rclo_transL r:
  rclo2 transL r <2= @transL E R1 R2 r.
Proof.
  intros. induction PR.
  - econstructor; eauto; reflexivity.
  - destruct IN. apply H in REL. destruct REL.
    econstructor; cycle -1; eauto using eqit_trans.
Qed.

Lemma rclo_transH r:
  rclo2 transH r <2= @transH E R1 R2 r.
Proof.
  intros. induction PR.
  - econstructor; eauto; reflexivity.
  - destruct IN. apply H in REL. destruct REL.
    econstructor; cycle -1; eauto; eapply eutt_trans; eauto.
Qed.

Lemma rclo_flip clo (r: itree E R1 -> itree E R2 -> Prop)
      (MON: monotone2 clo):
  flip (rclo2 (fun x : itree E R2 -> itree E R1 -> Prop => flip (clo (flip x))) (flip r)) <2= rclo2 clo r.
Proof.
  intros. induction PR; eauto with paco.
  apply rclo2_clo; eauto.
Qed.

Lemma transL_transH: transL <3= @transH E R1 R2.
Proof.
  intros. destruct PR. econstructor; eauto using eqit_mon.
Qed.

Lemma transH_transL_merge rH t1 t2:
  (transH rH \2/ transL rH) t1 t2 <-> @transH E R1 R2 rH t1 t2.
Proof.
  split; intros; eauto.
  destruct H; eauto using transL_transH.
Qed.

Lemma transH_transH_merge rH t1 t2:
  (transH rH \2/ transH rH) t1 t2 <-> @transH E R1 R2 rH t1 t2.
Proof.
  split; intros; eauto.
  destruct H; eauto.
Qed.

Lemma transL_compose:
  compose transL transL <3= @transL E R1 R2.
Proof.
  intros. destruct PR. destruct REL.
  econstructor; cycle -1; eauto; eapply eqit_trans; eauto using eqit_mon.
Qed.

Lemma transH_compose:
  compose transH transH <3= @transH E R1 R2.
Proof.
  intros. destruct PR. destruct REL.
  econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon.
Qed.

Lemma transL_mon r1 r2 t1 t2
      (IN: @transL E R1 R2 r1 t1 t2)
      (LE: r1 <2= r2):
  transL r2 t1 t2.
Proof. eapply eqitC_mon, LE; eauto. Qed.

Lemma transH_mon r1 r2 t1 t2
      (IN: @transH E R1 R2 r1 t1 t2)
      (LE: r1 <2= r2):
  transH r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve transL_mon transH_mon : paco.

Lemma transL_flip r:
  flip (transL (flip r)) <2= @transL E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma transH_flip r:
  flip (transH (flip r)) <2= @transH E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma eqitC_flip r:
  flip (eqitC true true (flip r)) <2= @eqitC E R1 R2 true true r.
Proof. eapply transL_flip. Qed.

Lemma euttGC_flip gH r:
  flip (euttGC (flip RR) (flip gH) (flip r)) <2= @euttGC E R1 R2 RR gH r.
Proof.
  gcofix CIH. intros. gunfold PR. econstructor.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto using transH_flip. intros.
  destruct PR0; eauto.
  left. pstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco. intros.
  apply rclo2_base. right. left. eapply CIH.
  eapply gupaco2_mon; eauto. intros.
  destruct PR1; eauto.
Qed.

End Lemmas.

Hint Resolve transL_mon transH_mon : paco.

Lemma euttG_flip {E R1 R2 RR} gH r:
  flip (gupaco2 (eqit_ (flip RR) true true (euttGC (flip RR) (flip gH))) (eqitC true true) (flip r)) <2=
  gupaco2 (@eqit_ E R1 R2 RR true true (euttGC RR gH)) (eqitC true true) r.
Proof.
  gcofix CIH; intros.
  destruct PR. econstructor.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto using eqitC_flip. intros.
  destruct PR; eauto.
  left. punfold H. pstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco; intros.
  - eapply euttGC_flip. apply PR.
  - apply rclo_flip; eauto with paco.
    eapply rclo2_mon_gen; eauto using eqitC_flip with paco.
    intros. right. left. destruct PR0.
    + eapply CIH. red. eauto with paco.
    + apply CIH0. destruct H0; eauto.
Qed.

Lemma eqit_ret_gen {E R} t1 v
      (IN: @eqit E R R eq true true t1 (Ret v)):
  eqit eq true false t1 (Ret v).
Proof.
  punfold IN. pstep. red in IN |- *. simpl in *.
  remember (RetF v) as ot.
  hinduction IN before R; intros; subst; eauto; inv Heqot.
Qed.

Section EUTTG_Properties.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma euttG_transH_auxL gH r t1 t2 t'
      (CLOR: transH r <2= r)
      (EQ: t1 ≈ t')
      (REL: gupaco2 (@eqit_ E _ _ RR true true (euttGC RR gH)) (eqitC true true) r t' t2):
  gupaco2 (eqit_ RR true true (euttGC RR gH)) (eqitC true true) r t1 t2.
Proof.
  apply gpaco2_dist in REL; eauto with paco. destruct REL; cycle 1.
  { apply rclo_transL in H.
    gbase. apply CLOR. apply transH_compose.
    econstructor; eauto using transL_transH; reflexivity.
  }
  assert (REL: paco2 (eqit_ RR true true (euttGC RR gH)) r t' t2).
  { eapply paco2_mon; eauto. intros.
    apply rclo_transL in PR. apply CLOR.
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
        pclearbot. gclo. econstructor; eauto; try reflexivity.
        eapply gupaco2_mon. apply REL0. intros.
        destruct PR; eauto.
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
      gclo. econstructor; eauto; try reflexivity.
      eapply gupaco2_mon. apply REL. intros.
      destruct PR; eauto.
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

End EUTTG_Properties.

Section EUTTG_Properties2.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma euttG_transH_auxR gH r t1 t2 t'
      (CLOR: transH r <2= r)
      (EQ: t' ≈ t2)
      (REL: gupaco2 (@eqit_ E _ _ RR true true (euttGC RR gH)) (eqitC true true) r t1 t'):
  gupaco2 (eqit_ RR true true (euttGC RR gH)) (eqitC true true) r t1 t2.
Proof.
  symmetry in EQ. apply euttG_flip.
  eapply euttG_transH_auxL; eauto using transH_flip.
  apply euttG_flip. eauto.
Qed.

Lemma euttG_transH_aux gH r
      (CLOR: transH r <2= r):
  transH (gupaco2 (eqit_ RR true true (euttGC RR gH)) (eqitC true true) r) <2= 
  gupaco2 (@eqit_ E R1 R2 RR true true (euttGC RR gH)) (eqitC true true) r.
Proof.
  intros. destruct PR. symmetry in EQVr.
  eapply euttG_transH_auxL; eauto.
  eapply euttG_transH_auxR; eauto.
Qed.

(* Make new hypotheses *)

Lemma euttG_coind: forall rH rL gL gH x,
    (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).
Proof.
  econstructor. revert x0 x1 PR. gcofix CIH.
  intros. apply H in PR. destruct PR.
  revert_until CIH. gcofix CIH. intros.
  apply gpaco2_dist in IN; eauto with paco.
  destruct IN; cycle 1.
  { gbase. apply rclo2_dist in H0; eauto with paco.
    destruct H0; apply rclo_transL in H0;
      eauto using transH_compose, transL_compose, transL_transH.
  }
  punfold H0. gstep. red in H0 |- *.
  induction H0; eauto.
  - econstructor. destruct REL.
    + gbase. apply CIH1. gfinal. right.
      eapply paco2_mon; eauto. intros.
      repeat (apply rclo2_dist in PR; eauto with paco; destruct PR as [PR|PR]);
        apply rclo_transL in PR; eauto 7 using transL_transH, transH_compose, transL_compose.
    + repeat (apply rclo2_dist in H0; eauto with paco; destruct H0 as [H0|H0]);
        apply rclo_transL in H0; eauto 8 using transL_transH, transH_compose, transL_compose with paco.
      apply transL_compose in H0. gclo. eapply transL_mon; eauto. intros.
      destruct PR; eauto with paco.
      gbase. apply CIH0. right. econstructor; eauto; reflexivity.
  - econstructor. intros.
    eapply gupaco2_mon; try apply REL. intros.
    destruct PR; [|destruct H0; eauto with paco].
    destruct H0.
    + left. gbase. apply CIH1. gfinal. right.
      eapply paco2_mon; eauto. intros.
      repeat (apply rclo2_dist in PR; eauto with paco; destruct PR as [PR|PR]);
        apply rclo_transL in PR; eauto 7 using transL_transH, transH_compose, transL_compose.
    + left.
      repeat (apply rclo2_dist in H0; eauto with paco; destruct H0 as [H0|H0]);
        apply rclo_transL in H0; eauto 8 using transL_transH, transH_compose, transL_compose with paco.
      apply transL_compose in H0. gclo. eapply transL_mon; eauto. intros.
      destruct PR; eauto with paco.
      gbase. apply CIH0. right. econstructor; eauto; reflexivity.
Qed.

(* Process itrees *)

Lemma euttG_ret: forall rH rL gL gH v1 v2,
  RR v1 v2 -> euttG rH rL gL gH (Ret v1) (Ret v2).
Proof.
  econstructor. gstep. econstructor. eauto.
Qed.

Lemma euttG_bind: forall rH rL gL gH t1 t2,
  eqit_bind_clo true true (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. guclo eqit_clo_bind.
  destruct H. econstructor; eauto.
  intros. edestruct REL; eauto.
Qed.

Lemma euttG_transL: forall rH rL gL gH t1 t2,
  transL (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. guclo eqit_clo_trans.
  destruct H. econstructor; eauto.
  edestruct REL; eauto.
Qed.

(* Lose weak hypotheses after general rewriting *)

Lemma euttG_transH rH rL gL gH t1 t2:
  transH (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros.
  cut (gupaco2 (eqit_ RR true true (euttGC RR gH)) (eqitC true true) (transH rH) t1 t2).
  { intros. econstructor. eauto using gpaco2_mon. }
  eapply euttG_transH_aux; eauto using transH_compose.
  eapply transH_mon; eauto. intros. destruct PR.
  eapply gpaco2_mon; eauto; intros;
    repeat destruct PR as [PR|PR]; eauto using transL_transH.
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
  apply euttGC_gen. gupaco.
  eapply gpaco2_mon_gen; eauto; intros; repeat destruct PR as [PR|PR];
    eauto using gpaco2_clo, transL_transH, transH_mon with paco.
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

(* Lemma euttG_le_eutt_aux *)
(*       (REL : gupaco2 (eqit_ RR true true id) transH *)
(*           (upaco2 (eqit_ RR true true (euttGC RR bot2)) bot2 \2/ bot2)  *)
(*           (k1 v) (k2 v) *)
(*   ============================ *)
(*   paco2 (eqit_ RR true true (euttGC RR bot2)) bot2 (k1 v) (k2 v) *)

(* Lemma euttG_le_eutt_aux: *)
(*   gpaco2 (@eqit_ E R1 R2 RR true true (euttGC RR bot2)) transH bot2 bot2 <2= *)
(*   gpaco2 (eqit_ RR true true (euttGC RR bot2)) (eqitC true true) bot2 bot2. *)
(* Proof. *)
  

  
  
(*   gcofix CIH. intros. *)
(*   gunfold PR. apply rclo_transH in PR. *)
(*   eapply gpaco2_mon; eauto. clear CIH r. *)
(*   cut (euttG bot2 bot2 bot2 (gpaco2 (eqit_ RR true true (euttGC RR bot2)) transH bot2 bot2) x2 x3). *)
(*   { intros. destruct H. eapply gpaco2_mon_gen; eauto with paco; intros. *)
(*     - eapply eqitF_mono; eauto with paco. *)
(*       intros. apply euttGC_gen. *)
(*       gupaco. eapply gupaco2_mon_gen; try apply PR1; eauto using eqitF_mono with paco; intros. *)
(*       destruct PR2; eauto using gpaco2_mon_bot with paco. *)
(*     - destruct PR0, H; contradiction. *)
(*     - destruct PR0; repeat destruct H; contradiction. *)
(*   } *)
(*   apply euttG_transH. eapply transH_mon; eauto. intros. pclearbot. *)
(*   econstructor. revert x0 x1 PR0. gcofix CIH; intros. *)
(*   gstep. eapply eqitF_mono; eauto with paco; intros. *)
(*   - eapply gupaco2_mon_gen; eauto with paco. intros. *)
(*     destruct PR2; eauto; contradiction. *)
(*   - gbase. apply CIH. red. *)
(*     gunfold PR1. apply rclo_transH in PR1. *)
(*     destruct PR1. pclearbot. *)
  
(*   pclearbot. econstructor. gstep. *)
(*   eapply eqitF_mono; eauto with paco; intros. *)
(*   - eapply gpaco2_mon_gen; eauto with paco; intros; destruct PR2; eauto; contradiction. *)
(*   -  *)
    
    

(*     apply euttGC_gen in PR1. *)
(*     red in PR1. red in PR1. *)
    
(*     eapply gpaco2_mon_gen; eauto using eqitF_mono with paco; intros. *)
(*     +  *)

    
    


(*     eapply gpaco2_mon_gen; eauto with paco; intros. *)
(*     + eapply eqitF_mono; eauto with paco. intros. *)
(*       eapply gpaco2_mon_gen; eauto with paco; intros; destruct PR4; eauto; contradiction. *)
(*     + red. *)

      
(*   unfold_eqit. *)
(*   induction PR0; eauto. *)
(*   - econstructor. gbase. *)
  

  

(*   destruct PR. pclearbot. *)
(*   red in REL. genobs t1' ot1'. genobs t2' ot2'. *)
(*   hinduction REL before CIH; intros; subst. *)
(*   -  *)
  

(*   gstep. eapply eqit__mono.  *)
  
(* Qed. *)

Lemma foo:
  transH (paco2 (eqit_ RR true true (euttGC RR bot2)) bot2) <2=
  paco2 (@eqit_ E R1 R2 RR true true (euttGC RR bot2)) bot2.
Proof.
  intros. ginit. cut (euttG bot2 bot2 bot2 bot2 x0 x1).
  { intros. destruct H.
    eapply gpaco2_mon; eauto; intros;
      repeat destruct PR0 as [PR0|PR0]; destruct PR0; contradiction.
  }
  apply euttG_transH. eapply transH_mon; eauto. intros.
  econstructor. gfinal. right.
  eapply paco2_mon_bot; eauto.
Qed.

Lemma euttG_le_eutt:
  euttG bot2 bot2 bot2 bot2 <2= eutt RR.
Proof.
  intros. destruct PR.
  assert(paco2 (eqit_ RR true true (euttGC RR bot2)) bot2 x0 x1).
  { eapply gpaco2_init; eauto with paco.
    eapply gpaco2_mon; eauto; intros;
      repeat destruct PR as [PR|PR]; destruct PR; contradiction.
  }
  clear IN.
  revert x0 x1 H. pcofix CIH. intros.
  punfold H0. pstep. unfold_eqit.
  induction H0; pclearbot; eauto.
  econstructor; intros. specialize (REL v). red.
  right. apply CIH. revert REL.
  generalize (k1 v) as t1. generalize (k2 v) as t2. clear x2 x3 u e k1 k2 v.
  pcofix CIH. intros.
  gunfold REL. apply rclo_transH in REL. destruct REL. 
  destruct REL as [ | []]; try contradiction; cycle 1.
  { pclearbot. eapply paco2_mon_bot; eauto. apply foo. eauto. }
  eapply paco2_mon; [|intros; eapply CIH0; apply PR].
  cut (gupaco2 (@eqit_ E R1 R2 RR true true (euttGC RR bot2)) transH bot2 t1 t2).
  { intros. apply gpaco2_dist in H0; eauto with paco.
    destruct H0.
    - eapply paco2_mon; eauto. intros.
      apply rclo_transL in PR. destruct PR, REL; contradiction.
    - apply rclo_transL in H0. destruct H0; contradiction.
  }
  eapply euttG_transH_aux.
  { intros. destruct PR; contradiction. }
  econstructor; eauto.
  gstep. red in H |- *.
  induction H; eauto.
  -
    eapply gupaco2_mon; eauto. intros.
    destruct PR; eauto.
  - econstructor. intros. eapply gupaco2_mon. apply REL. intros.
    left. destruct PR; pclearbot; left; eapply paco2_mon_bot; eauto.
Qed.

Lemma eutt_le_euttG:
  eutt RR <2= euttG bot2 bot2 bot2 bot2.
Proof.
  intros. econstructor. econstructor. apply rclo2_base. left.
  eapply paco2_mon_gen; eauto; intros.
  - eapply eqitF_mono; eauto with paco.
  - contradiction.
Qed.






















End EUTTG_Properties.





