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

Definition euttGC gH r := transH (r \2/ gH).

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
  red; intros. destruct IN.
  econstructor; eauto.
  destruct REL; eauto.
Qed.

Hint Resolve euttGC_mon : paco.

Lemma euttGC_compat gH:
  compose (eqitC true true) (euttGC gH) <3= compose (euttGC gH) (eqitC true true).
Proof.
  intros. destruct PR. destruct REL. destruct REL; cycle 1.
  - econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon.
  - econstructor; [..|left; econstructor]; [..|reflexivity|reflexivity|eauto].
    + eapply eutt_trans; eauto using eqit_mon.
    + eapply eutt_trans; eauto using eqit_mon.
Qed.
Hint Resolve euttGC_compat : paco.

Lemma euttGC_id gH:
  id <3= euttGC gH.
Proof.
  intros. econstructor; try reflexivity; eauto.
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

End EUTTG.

Hint Constructors euttG.
Hint Unfold transH transL.
Hint Resolve euttGC_mon : paco.
Hint Resolve euttGC_compat : paco.
Hint Resolve euttGC_id : paco.

Section Lemmas.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Lemma rclo_eqitC r:
  rclo2 (eqitC true true) r <2= @eqitC E R1 R2 true true r.
Proof.
  intros. induction PR.
  - econstructor; eauto; reflexivity.
  - destruct IN. apply H in REL. destruct REL.
    econstructor; cycle -1; eauto using eqit_trans.
Qed.

Lemma transH_transL_merge rH t1 t2:
  (transH rH \2/ transL rH) t1 t2 <-> @transH E R1 R2 rH t1 t2.
Proof.
  split; intros; eauto.
  destruct H; eauto.
  destruct H. econstructor; eauto using eqit_mon.
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

End Lemmas.

Lemma transL_flip {E R1 R2} r:
  flip (transL (flip r)) <2= @transL E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma transH_flip {E R1 R2} r:
  flip (transH (flip r)) <2= @transH E R1 R2 r.
Proof.
  intros. destruct PR. econstructor; cycle -1; eauto.
Qed.

Lemma transL_mon {E R1 R2} r1 r2
      (LE: r1 <2= r2):
  @transL E R1 R2 r1 <2= transL r2.
Proof. apply eqitC_mon, LE. Qed.

Lemma transH_mon {E R1 R2} r1 r2
      (LE: r1 <2= r2):
  @transH E R1 R2 r1 <2= transH r2.
Proof.
  intros. destruct PR. econstructor; eauto.
Qed.

(* Lemma transH_eqitC {E R1 R2} r: *)
(*   rclo2 (eqitC true true) (transH r) <2= @transH E R1 R2 r. *)
(* Proof. *)
(*   intros. apply rclo_eqitC in PR. apply transH_compose. *)
(*   destruct PR; econstructor; eauto using eqit_mon. *)
(* Qed. *)

(* Lemma transL_eqitC {E R1 R2} r: *)
(*   rclo2 (eqitC true true) (transL r) <2= @transL E R1 R2 r. *)
(* Proof. *)
(*   intros. apply rclo_eqitC in PR. apply transL_compose. *)
(*   destruct PR; econstructor; eauto using eqit_mon. *)
(* Qed. *)

Lemma euttG_flip {E R1 R2 RR} rH rL gL gH:
    flip (euttG (flip RR) (flip rH) (flip rL) (flip gL) (flip gH)) <2= @euttG E R1 R2 RR rH rL gL gH.
Proof.
  econstructor. destruct PR. revert x0 x1 IN. gcofix CIH; intros.
  destruct IN. econstructor.
  apply rclo_eqitC in IN. eapply rclo2_clo'; [apply rclo2_base|].
  apply transL_flip.
  eapply eqitC_mon, IN. intros.
  destruct PR; cycle 1.
  { right. destruct H; destruct H; eauto. } 
  left. punfold H. pstep. repeat red in H |- *.
  induction H; eauto.
  + econstructor.
    apply rclo_eqitC in REL. eapply rclo2_clo'; [apply rclo2_base|].
    eapply transL_flip. eapply eqitC_mon, REL. intros.
    right. left. destruct PR; eauto with paco.
    apply CIH0.
    repeat destruct H as [H|H]; eauto using transH_flip, transL_flip.
  + econstructor. intros.
    apply transH_flip.
    eapply transH_mon, REL. intros.
    destruct PR; [left|red; eauto].
    apply rclo_eqitC in H. eapply rclo2_clo'; [apply rclo2_base|].
    eapply transL_flip. eapply eqitC_mon, H. intros.
    right. left. destruct PR; eauto with paco.
    apply CIH0.
    repeat destruct H0 as [H0|H0]; eauto using transH_flip, transL_flip.
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

Lemma euttG_trans_eutt_aux1 rH rL gL gH t1 t' t2
      (EQ: t1 ≈ t')
      (REL: euttG rH rH rH gH t' t2):
  euttG rH rL gL gH t1 t2.
Proof.
  destruct REL. econstructor.
  revert_until gH. gcofix CIH. intros.
  apply gpaco2_dist in IN; eauto with paco.
  destruct IN; cycle 1.
  { gbase. left.
    apply rclo_eqitC in H. destruct H.
    rewrite transH_transL_merge in REL. destruct REL.
    econstructor; cycle -1; eauto; repeat (eapply eutt_trans; eauto using eqit_mon).
  }
  assert (REL: paco2 (eqit_ RR true true (euttGC gH)) (transH rH) t' t2).
  { eapply paco2_mon; eauto. intros.
    apply rclo_eqitC in PR. destruct PR.
    rewrite !transH_transL_merge, !transH_transH_merge in REL. destruct REL.
    econstructor; cycle -1; eauto; repeat (eapply eutt_trans; eauto using eqit_mon).
  }
  clear H.
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
      * eapply CIH.
        { rewrite REL0, tau_eutt. reflexivity. }
        { gfinal. right. eapply paco2_mon; eauto. }
      * eapply CIH0. left. left.
        eapply transH_compose. econstructor; cycle -1; eauto; try reflexivity.
        rewrite REL0, tau_eutt. reflexivity.
    + punfold REL0. red in REL0. simpl in *.
      remember (VisF e k1) as ot. genobs m1 om1.
      hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot.
      * gstep. red. simpobs. econstructor; eauto. simpobs. econstructor. intros.
        pclearbot. apply transH_compose. econstructor; try apply REL; try reflexivity.
        eapply transH_mon, REL0. intros.
        destruct PR; eauto.
        left. gfinal. destruct H; eauto.
        left. eapply CIH; try reflexivity.
        gfinal. right. eapply paco2_mon; eauto.
      * rewrite (simpobs Heqot1), tau_eutt. eauto.
    + eapply IHREL0; eauto.
      rewrite REL, <-itree_eta, tau_eutt. reflexivity.
    + rewrite (simpobs Heqot2), tau_eutt. eauto.
  - remember (VisF e k2) as ot. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot.
    + gstep. red. simpobs. econstructor.
      intros. pclearbot. specialize (REL v). inv REL.
      econstructor.
      * rewrite REL0, EQVl. reflexivity.
      * rewrite EQVr. reflexivity.
      * destruct REL1; eauto.
        destruct H; [|eauto 7 with paco].
        left. gfinal. right. eapply paco2_mon; eauto.
    + rewrite (simpobs Heqot2), tau_eutt. eauto.
  - rewrite (simpobs Heqot1), tau_eutt. eauto.
  - clear t' Heqot'. remember (TauF t2) as ot. genobs t0 ot0.
    hinduction REL before EQ; intros; subst; try inv Heqot; eauto.
    + destruct REL; cycle 1.
      * gbase. left. apply transH_compose. econstructor; cycle -1; eauto.
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

Lemma euttG_trans_eutt_aux2 rH rL gL gH t1 t' t2
      (EQ: t' ≈ t2)
      (REL: euttG rH rH rH gH t1 t'):
  euttG rH rL gL gH t1 t2.
Proof.
  symmetry in EQ.
  apply euttG_flip in REL.
  apply euttG_flip.
  eapply euttG_trans_eutt_aux1; eauto.
Qed.

(* Make new hypotheses *)

Lemma euttG_coind: forall rH rL gL gH x,
    (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).
Proof. Admitted.

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
  intros. destruct H.
  eapply euttG_trans_eutt_aux1; eauto.
  eapply euttG_trans_eutt_aux2; eauto.
  symmetry. eauto.
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
  specialize (H v). destruct H. red.
  apply gpaco2_dist in IN; eauto with paco.


  destruct H. gunfold IN.
  apply rclo_eqitC in IN.
  
  
  eapply gpaco2_mon; eauto; intros; repeat destruct PR as [PR|PR]; eauto.
  
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
  pcofix CIH; intros.
  intros. destruct PR. apply gpaco2_dist in IN; eauto with paco.
  destruct IN; cycle 1.
  - apply rclo_eqitC in H. destruct H, REL, H; contradiction.
  - punfold H. pstep. red in H |- *. induction H; eauto.
    + econstructor. right. apply CIH. destruct REL.
      * econstructor. apply gpaco2_dist_reverse; eauto with paco.
      * apply rclo_eqitC in H. destruct H.
        repeat destruct REL as [REL|REL]; destruct REL; contradiction.
    + econstructor; intros. specialize (REL v); destruct REL. pclearbot.
      right. apply CIH. apply euttG_transH. econstructor; eauto.
      econstructor. apply gpaco2_dist_reverse; eauto with paco.
      destruct REL; eauto.
      apply rclo_eqitC in H. destruct H.
      repeat destruct REL as [REL|REL]; destruct REL; contradiction.
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





