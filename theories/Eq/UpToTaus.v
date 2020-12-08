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


(**** START: taken from Paco-4.0.1 ****)

Lemma gpaco2_gen_guard {T0 T1} gf clo r rg:
  @gpaco2 T0 T1 gf clo r (rg \2/ r) <2= gpaco2 gf clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo2_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco2_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco2_gpaco {T0 T1} gf (gf_mon: @monotone2 T0 T1 gf) clo r rg:
  gpaco2 gf clo (gpaco2 gf clo r rg) (gupaco2 gf clo (rg \2/ r)) <2= gpaco2 gf clo r rg.
Proof.
  intros. apply gpaco2_unfold in PR; eauto.
  econstructor. apply rclo2_rclo. eapply rclo2_mon. apply PR. clear x0 x1 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo2_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 H. intros.
  cut (@gupaco2 T0 T1 gf clo (rg \2/ r) x0 x1).
  { intros. destruct H. eapply rclo2_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco2_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco2_gupaco; eauto. eapply gupaco2_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco2_mon; [apply H|right|left]; intros; apply PR0.
Qed.

(** ** gpaco
*)

Tactic Notation "gpaco_" :=
  match goal with
  | [|- context[gpaco2]] => eapply gpaco2_gpaco; [eauto with paco|]
  end.
Ltac gpaco := repeat red; under_forall ltac:(gpaco_).

(**** END ****)


Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition transU := @eqit_trans_clo E R1 R2 RR true true true true.
Definition transD := @eqit_trans_clo E R1 R2 RR true true false false.
Definition bindC := @eqit_bind_clo E R1 R2 true true.

Definition euttVC gH r :=
  gupaco2 (eqit_ RR true true id) transD (transU (r \2/ gH)).

Variant euttG rH rL gL gH t1 t2 : Prop :=
| euttG_intro
    (IN: gpaco2 (@eqit_ E R1 R2 RR true true (euttVC gH)) transD (transU rH \2/ rL) gL t1 t2)
.

Hint Unfold transU transD bindC euttVC: core.
Hint Constructors euttG: core.

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
  econstructor; try eapply eqit_trans; eauto; auto_ctrans.
Qed.

Lemma transU_compose:
  compose transU transU <3= transU.
Proof.
  intros. destruct PR. destruct REL.
  econstructor; try eapply eqit_trans; eauto; auto_ctrans.
Qed.

Lemma transD_id: id <3= transD.
Proof. intros. econstructor; try reflexivity; auto_ctrans. Qed.

Lemma transU_id: id <3= transU.
Proof. intros. econstructor; try reflexivity; auto_ctrans. Qed.

Hint Resolve transD_mon transU_mon : paco.

Lemma euttVC_mon gH:
  monotone2 (euttVC gH).
Proof.
  red; intros.
  eapply gupaco2_mon; eauto. intros.
  eapply transU_mon; eauto. intros.
  destruct PR0; eauto.
Qed.
Hint Resolve euttVC_mon : paco.

Lemma euttVC_compat gH:
  compose transD (euttVC gH) <3= compose (euttVC gH) transD.
Proof.
  intros. gclo. eapply transD_mon; eauto. intros.
  eapply gupaco2_mon; eauto. intros.
  eapply transU_mon; eauto. intros.
  destruct PR2; eauto.
  left. econstructor; try reflexivity; auto_ctrans.
Qed.
Hint Resolve euttVC_compat : paco.

Lemma euttVC_id gH:
  id <3= euttVC gH.
Proof.
  intros. gbase. econstructor; try reflexivity; auto_ctrans.
Qed.
Hint Resolve euttVC_id : paco.

End EUTTG.

Hint Unfold transU transD bindC euttVC: core.
Hint Constructors euttG: core.
Hint Resolve transD_mon transU_mon : paco.
Hint Resolve euttVC_mon : paco.
Hint Resolve euttVC_compat : paco.
Hint Resolve transD_id transU_id euttVC_id : paco.

Instance geuttG_cong_euttge {E R1 R2 RR} gH r g:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (transD RR) r g).
Proof.
  repeat intro. guclo eqit_clo_trans. econstructor; eauto; auto_ctrans.
Qed.

Instance geuttG_cong_eq {E R1 R2 RR} gH r g:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (transD RR) r g).
Proof.
  repeat intro. eapply geuttG_cong_euttge; eauto using eqit_mon.
Qed.

Lemma eqit_ret_gen {E R1 R2 RR} t v
      (IN: @eqit E R1 R2 RR true true t (Ret v)):
  eqit RR true false t (Ret v).
Proof.
  punfold IN. pstep. red in IN |- *. simpl in *.
  remember (RetF v) as ot.
  hinduction IN before RR; intros; subst; eauto; inv Heqot.
Qed.

Section EUTTG_Properties1.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma rclo_transD r:
  rclo2 (transD RR) r <2= @transD E R1 R2 RR r.
Proof.
  intros. induction PR; eauto with paco.
  destruct IN. apply H in REL. destruct REL.
  econstructor; try apply REL; try eapply eqit_trans; eauto; auto_ctrans.
Qed.

Lemma rclo_flip clo (r: itree E R1 -> itree E R2 -> Prop)
      (MON: monotone2 clo):
  flip (rclo2 (fun x : itree E R2 -> itree E R1 -> Prop => flip (clo (flip x))) (flip r)) <2= rclo2 clo r.
Proof.
  intros. induction PR; eauto with paco.
  apply rclo2_clo; eauto.
Qed.

Lemma transD_flip r:
  flip (transD (flip RR) (flip r)) <2= @transD E _ _ RR r.
Proof.
  unfold flip. intros. destruct PR. econstructor; eauto.
Qed.

Lemma transU_flip r:
  flip (transU (flip RR) (flip r)) <2= @transU E R1 R2 RR r.
Proof.
  unfold flip. intros. destruct PR. econstructor; eauto.
Qed.

Lemma euttVC_flip gH r:
  flip (euttVC (flip RR) (flip gH) (flip r)) <2= @euttVC E R1 R2 RR gH r.
Proof.
  gcofix CIH. intros. gunfold PR.
  gclo. apply rclo_transD.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto; intros.
  { eapply transD_flip. eauto. }
  destruct PR0; cycle 1.
  { gbase. destruct H; eauto using transU_flip. }
  gstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco. intros.
  gbase. eapply CIH.
  eapply gupaco2_mon; eauto. intros.
  destruct PR1; eauto.
Qed.

Lemma euttG_flip gH r:
  flip (gupaco2 (eqit_ (flip RR) true true (euttVC (flip RR) (flip gH))) (transD (flip RR)) (flip r)) <2=
  gupaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (transD RR) r.
Proof.
  gcofix CIH; intros.
  destruct PR. econstructor.
  eapply rclo_flip; eauto with paco.
  eapply rclo2_mon_gen; eauto using transD_flip. intros.
  destruct PR; eauto.
  left. punfold H. pstep. apply eqitF_flip.
  eapply eqitF_mono; eauto with paco; intros.
  - eapply euttVC_flip. apply PR.
  - apply rclo_flip; eauto with paco.
    eapply rclo2_mon_gen; eauto using transD_flip with paco.
    intros. right. left. destruct PR0.
    + eapply CIH. red. eauto with paco.
    + apply CIH0. destruct H0; eauto.
Qed.

Lemma transD_dist:
  forall r1 r2, @transD E R1 R2 RR (r1 \2/ r2) <2= (transD RR r1 \2/ transD RR r2).
Proof. apply eqitC_dist. Qed.

Lemma transU_dist:
  forall r1 r2, @transU E R1 R2 RR (r1 \2/ r2) <2= (transU RR r1 \2/ transU RR r2).
Proof.
  intros. destruct PR. destruct REL; eauto.
Qed.

Lemma transU_dist_rev:
  forall r1 r2, (transU RR r1 \2/ transU RR r2) <2= @transU E R1 R2 RR (r1 \2/ r2).
Proof.
  intros. destruct PR, H; eauto.
Qed.

Variant transL (r: itree E R1 -> itree E R2 -> Prop) (t1: itree E R1) (t2: itree E R2) : Prop :=
| transL_intro t' RR1
               (EQL: eqit RR1 true true t1 t')
               (EQR: r t' t2)
               (LERR: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
  : transL r t1 t2
.
Hint Constructors transL: core.

Lemma transD_transL r:
  transD RR (transL r) <2= transL (transD RR r).
Proof.
  intros. destruct PR, REL.
  econstructor; [|econstructor|]; try apply EQR.
  - eapply eqit_trans.
    + apply euttge_sub_eutt. eauto.
    + eauto.
  - reflexivity.
  - eauto.
  - auto_ctrans.
  - auto_ctrans.
  - auto_ctrans.
Qed.

Lemma transLleU: transL <3= transU RR.
Proof.
  intros. destruct PR. econstructor; eauto. reflexivity. auto_ctrans.
Qed.

Lemma transL_closed vclo r
      (MON: monotone2 vclo)
      (COMP: wcompatible2 (eqit_ RR true true vclo) (transD RR))
      (CLOV: forall r (CLOL: transL r <2= r), transL (vclo r) <2= vclo r)
      (CLOL: transL r <2= r)
      (CLOD: transD RR r <2= r):
  transL (gupaco2 (eqit_ RR true true vclo) (transD RR) r)
  <2= gupaco2 (eqit_ RR true true vclo) (transD RR) r.
Proof.
  gcofix CIH. intros t1 t2 [].
  apply gpaco2_dist in EQR; eauto with paco.
  destruct EQR; cycle 1.
  { gbase. apply rclo_transD in H. destruct H. eauto 7. }
  assert (REL: paco2 (eqit_ RR true true vclo) r t' t2).
  { eapply paco2_mon; eauto. intros.
    apply rclo_transD in PR. apply CLOD.
    eapply transD_mon; eauto. intros. destruct PR0; eauto.
  }
  clear H.

  punfold EQL. red in EQL. punfold REL. red in REL. genobs t1 ot1. genobs t' ot'.
  hinduction EQL before CIH; intros; subst.
  - remember (RetF r2) as ot. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst; try inv Heqot.
    + gstep. red. simpobs. eauto.
    + gclo. econstructor; auto_ctrans_eq.
      * rewrite (simpobs Heqot1). reflexivity.
      * rewrite (simpobs Heqot2), tau_euttge. reflexivity.
  - pclearbot. apply eqit_tauR in REL. rewrite Heqot' in REL, REL0. clear m2 Heqot'.
    genobs t' ot'. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst.
    + apply eqit_ret_gen in REL0.
      gclo. econstructor.
      * eapply eqit_trans; [rewrite (simpobs Heqot1); reflexivity|].
        eapply eqit_trans; [rewrite tau_euttge; reflexivity|].
        eauto.
      * rewrite (simpobs Heqot2). reflexivity.
      * gstep. econstructor. eauto.
      * auto_ctrans.
      * auto_ctrans.
    + gstep. red. simpobs. econstructor. gbase.
      destruct REL.
      * eapply CIH. econstructor; [|eauto using paco2_mon with paco|].
        -- eapply eqit_trans; [apply REL0|]. rewrite tau_eutt. reflexivity.
        -- auto_ctrans.
      * eapply CIH0. apply CLOL. econstructor; [|eauto|].
        -- eapply eqit_trans; [apply REL0|]. rewrite tau_eutt. reflexivity.
        -- auto_ctrans.
    + punfold REL0. red in REL0. simpl in *.
      remember (VisF e k1) as ot. genobs m1 ot2.
      hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot; cycle 1.
      * gclo; econstructor; auto_ctrans_eq; try reflexivity.
        rewrite (simpobs Heqot1), tau_euttge. reflexivity.
      * pclearbot. gstep. red. do 2 (simpobs; econstructor; eauto). intros.
        eapply MON; [|intros; gbase; eapply CIH; eauto].
        eapply CLOV.
        { intros. destruct PR, EQR.
          econstructor; [|eauto|]; eauto using eqit_trans; auto_ctrans. }
        econstructor; eauto.
        eapply MON; eauto. intros.
        econstructor; try reflexivity; auto_ctrans.
        gfinal. destruct PR; eauto.
    + eapply IHREL0; try eapply eqit_trans; auto_ctrans_eq.
      rewrite <-itree_eta, tau_eutt. reflexivity.
    + gclo; econstructor; auto_ctrans_eq; try reflexivity.
      rewrite (simpobs Heqot2), tau_euttge. reflexivity.
  - remember (VisF e k2) as ot. genobs t2 ot2.
    hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot; cycle 1.
    + gclo; econstructor; auto_ctrans_eq; try reflexivity.
      rewrite (simpobs Heqot2), tau_euttge. reflexivity.
    + pclearbot. gstep. red. simpobs. econstructor; eauto. intros.
      eapply MON; [|intros; gbase; eapply CIH; eauto].
      eapply CLOV.
      { intros. destruct PR, EQR.
        econstructor; swap 1 2; eauto using eqit_trans; auto_ctrans. }
      econstructor; eauto.
      eapply MON; eauto. intros.
      econstructor; auto_ctrans_eq; try reflexivity.
      gfinal. destruct PR; eauto.
  - gclo; econstructor; auto_ctrans_eq; try reflexivity.
    rewrite (simpobs Heqot1), tau_euttge. reflexivity.
  - clear t' Heqot'. remember (TauF t2) as ot. genobs t0 ot0.
    hinduction REL before EQL; intros; subst; try inv Heqot; eauto; cycle 1.
    + gclo; econstructor; auto_ctrans_eq; try reflexivity.
      rewrite (simpobs Heqot0), tau_euttge. reflexivity.
    + destruct REL; cycle 1.
      * gbase. apply CLOL. econstructor; eauto.
        apply CLOD. econstructor; auto_ctrans_eq; try reflexivity.
        rewrite (simpobs Heqot0), tau_euttge. reflexivity.
      * eapply IHEQL; eauto.
        simpobs. econstructor; eauto.
        punfold H.
Qed.

Lemma euttVC_transL gH r:
  transL (euttVC RR gH r) <2= euttVC RR gH r.
Proof.
  intros. eapply transL_closed; eauto using transU_compose, transLleU, transDleU with paco.
Qed.

End EUTTG_Properties1.

Section EUTTG_Properties2.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

Lemma euttVC_transU gH r
      (CLOR: transU RR r <2= r):
  transU RR (euttVC RR gH r) <2= @euttVC E _ _ RR gH r.
Proof.
  intros. destruct PR.
  eapply euttVC_transL; eauto using transLleU, transDleU with paco.
  econstructor; eauto.
  eapply euttVC_flip. unfold flip.
  eapply euttVC_transL; eauto using transLleU, transDleU, transU_flip with paco.
  econstructor; eauto.
  apply euttVC_flip. eauto.
Qed.

Lemma euttG_transU_aux gH r
      (CLOR: transU RR r <2= r):
  transU RR (gupaco2 (eqit_ RR true true (euttVC RR gH)) (transD RR) r) <2= 
  gupaco2 (@eqit_ E R1 R2 RR true true (euttVC RR gH)) (transD RR) r.
Proof.
  intros. destruct PR.
  eapply transL_closed; eauto using euttVC_transL, transLleU, transDleU with paco.
  econstructor; eauto.
  apply euttG_flip. unfold flip.
  eapply transL_closed; eauto using euttVC_transL, transLleU, transDleU, transU_flip with paco.
  econstructor; eauto.
  apply euttG_flip. eauto.
Qed.

Lemma euttVC_gen gH r:
  transU RR (gupaco2 (eqit_ RR true true (euttVC RR gH)) (transD RR) (transU RR (r \2/ gH)))
  <2= @euttVC E R1 R2 RR gH r.
Proof.
  intros. eapply euttG_transU_aux in PR; eauto using transU_compose.
  revert x0 x1 PR. gcofix CIH. intros.
  gunfold PR. apply rclo_transD in PR.
  gclo. eapply transD_mon; eauto. intros.
  destruct PR0; eauto with paco.
  gstep. red in H |- *. induction H; eauto.
  - econstructor. gbase. eapply CIH.
    eapply gupaco2_mon; eauto. intros.
    destruct PR0; eauto.
  - econstructor. intros. gbase. eapply CIH.
    red in REL. gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
    + eapply eqitF_mono; eauto with paco.
    + eapply euttG_transU_aux; eauto using transU_compose with paco.
      eapply transU_mon; eauto. intros.
      destruct PR1; [|eauto 7 with paco].
      eapply gupaco2_mon; eauto. intros.
      destruct PR1; eauto.
Qed.

Lemma euttG_gen rH rL gL gH:
  euttG rH rL (gL \2/ (transU RR rH \2/ rL)) gH <2= euttG rH rL gL gH.
Proof.
  intros. destruct PR. econstructor.
  eapply gpaco2_gen_guard. eauto.
Qed.

Lemma euttG_cofix_aux: forall rH rL gL gH x,
    (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).
Proof.
  intros. apply euttG_gen.
  econstructor. revert x0 x1 PR. gcofix CIH.
  intros. apply H in PR. destruct PR.
  revert_until CIH. gcofix CIH. intros.
  apply gpaco2_dist in IN; eauto with paco.
  destruct IN; cycle 1.
  { apply rclo_transD in H0; eauto with paco.
    gclo. eapply transD_mon; eauto with paco.
  }
  assert (LEM: upaco2 (eqit_ RR true true (euttVC RR (gH \2/ x)))
                      (rclo2 (transD RR) ((gL \2/ x) \2/ (transU RR rH \2/ rL)))
               <2= gpaco2 (eqit_ RR true true (euttVC RR gH)) (transD RR) r r).
  { intros m1 m2 [REL|REL].
    - gbase. apply CIH1.
      gpaco. gfinal. right.
      eapply paco2_mon; eauto. intros.
      apply rclo_transD in PR. gclo. eapply transD_mon; eauto. intros. gbase.
      repeat destruct PR0 as [PR0|PR0]; eauto.
    - apply rclo_transD in REL. gclo. eapply transD_mon; eauto. intros. gbase.
      repeat destruct PR as [PR|PR]; eauto.
  }

  punfold H0. gstep. red in H0 |- *.
  induction H0; eauto.
  red in REL. econstructor. intros.
  eapply gupaco2_mon; eauto. intros.
  apply transU_dist in PR. destruct PR; eauto using transU_mon.
  eapply transU_mon; eauto. intros; destruct PR; eauto with paco.
Qed.

End EUTTG_Properties2.

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
  transD RR (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. guclo eqit_clo_trans.
  destruct H. econstructor; eauto.
  edestruct REL; eauto.
Qed.

(* Drop weak hypotheses for general rewriting *)

Lemma euttG_transU rH rL gL gH t1 t2:
  transU RR (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros. apply euttG_gen.
  cut (gupaco2 (eqit_ RR true true (euttVC RR gH)) (transD RR) (transU RR rH) t1 t2).
  { intros. econstructor. eapply gpaco2_mon; eauto. }
  eapply euttG_transU_aux; eauto using transU_compose.
  eapply transU_mon; eauto. intros. destruct PR.
  eapply gpaco2_mon; eauto; intros;
    repeat destruct PR as [PR|PR]; eauto using transU_id.
Qed.

Lemma euttG_drop rH rL gL gH t1 t2:
  euttG rH rH rH gH t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros. apply euttG_gen. destruct H. econstructor.
  eapply gpaco2_mon; intros; eauto; [destruct PR|]; eauto using transU_id. 
Qed.

(* Make a weakly guarded progress *)

Lemma euttG_tau: forall rH rL gL gH t1 t2,
  euttG rH gL gL gH t1 t2 -> euttG rH rL gL gH (Tau t1) (Tau t2).
Proof.
  intros. apply euttG_gen. destruct H. econstructor.
  gstep. econstructor.
  eapply gpaco2_mon; eauto; intros; repeat destruct PR as [PR|PR]; eauto.
Qed.

(* Make a strongly guarded progress *)

Lemma euttG_vis: forall rH rL gL gH u (e: E u) k1 k2,
  (forall v, euttG gH gH gH gH (k1 v) (k2 v)) -> euttG rH rL gL gH (Vis e k1) (Vis e k2).
Proof.
  econstructor. gstep. econstructor. intros.
  specialize (H v). destruct H.
  apply euttVC_gen. econstructor; auto_ctrans_eq; try reflexivity.
  eapply gpaco2_mon_gen; eauto; intros; repeat destruct PR as [PR|PR];
    eauto using gpaco2_clo, transDleU, transU_mon with paco.
Qed.

(* Use available hypotheses *)

Lemma euttG_base: forall rH rL gL gH t1 t2,
  rH t1 t2 \/ rL t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros. econstructor. gbase.
  destruct H; eauto using transU_id.
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
  ginit. gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
  - eapply eqitF_mono; eauto with paco.
  - apply euttG_transU_aux.
    { intros. destruct PR0; contradiction. }
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

Require Import Paco.pacotac_internal.

Tactic Notation "ecofix" ident(CIH) "with" ident(gL) ident(gH) :=
  repeat red;
  paco_pre2;
  eapply euttG_cofix;
  paco_post2 CIH with gL;
  paco_post2 CIH with gH.

Tactic Notation "ecofix" ident(CIH) := ecofix CIH with gL gH.

Ltac einit := repeat red; under_forall ltac:(eapply euttG_le_eutt; eauto with paco).
Ltac efinal := repeat red; under_forall ltac:(eapply eutt_le_euttG; eauto with paco).
Ltac ebase := repeat red; under_forall ltac:(eapply euttG_base; eauto with paco).
Ltac eret := repeat red; under_forall ltac:(eapply euttG_ret; eauto with paco).
Ltac etau := repeat red; under_forall ltac:(eapply euttG_tau; eauto with paco).
Ltac evis := repeat red; under_forall ltac:(eapply euttG_vis; eauto with paco).
Ltac estep := first [eret|etau|evis].
Ltac ebind := repeat red; under_forall ltac:(eapply euttG_bind; eauto with paco).
Ltac edrop := repeat red; under_forall ltac:(eapply euttG_drop; eauto with paco).

Hint Resolve euttG_ret : paco.
Hint Resolve euttG_tau : paco.
Hint Resolve euttG_vis : paco.
Hint Resolve euttG_base : paco.
Hint Resolve euttG_le_eutt: paco.

Global Instance euttG_reflexive {E R} rH rL gL gH:
  Reflexive (@euttG E R R eq rH rL gL gH).
Proof.
  red; intros. efinal. reflexivity.
Qed.

Global Instance euttG_cong_eutt {E R1 R2 RR} rH gH:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (@euttG E R1 R2 RR rH rH rH gH).
Proof.
  repeat intro. eapply euttG_transU. econstructor; auto_ctrans_eq; eauto.
Qed.

Global Instance euttG_cong_euttge {E R1 R2 RR} rH rL gL gH:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (@euttG E R1 R2 RR rH rL gL gH).
Proof.
  repeat intro. eapply euttG_transD. econstructor; auto_ctrans_eq; eauto.
Qed.

Global Instance euttG_cong_eq {E R1 R2 RR} rH rL gL gH:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@euttG E R1 R2 RR rH rL gL gH).
Proof.
  repeat intro. eapply euttG_cong_euttge; eauto; apply eq_sub_euttge; eauto.
Qed.

Global Instance eutt_cong_eutt {E R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (@eqit E R1 R2 RR true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

Global Instance eutt_cong_euttge {E R1 R2 RR}:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (@eqit E R1 R2 RR true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

Global Instance eutt_cong_eq {E R1 R2 RR}:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RR true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

Global Instance eutt_cong_eutt' {E R1 R2 RR} :
  Proper (eutt eq ==> eutt eq ==> flip impl) (@eutt E R1 R2 RR).
Proof.
  apply eutt_cong_eutt.
Qed.

(* Specialization of [eutt_clo_bind] to the recurrent case where [UU := eq]
   in order to avoid having to provide the relation manually everytime *)
Lemma eutt_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eutt RR (k1 u) (k2 u)) -> eutt RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

(* Exposing a version specialized to [eutt] so that users don't have to know about [eqit] *)
Lemma eutt_Ret :
  forall E (R1 R2 : Type) (RR : R1 -> R2 -> Prop) r1 r2, RR r1 r2 <-> eutt (E := E) RR (Ret r1) (Ret r2).
Proof.
  intros; apply eqit_Ret.
Qed.

(* [eutt] can be thought as the elementary block of a relational program logic.
   The following few lemmas give elementary logical rules to compose proofs.
 *)
Lemma eutt_conj {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS  t s ->
    eutt RS' t s ->
    eutt (RS /2\ RS') t s. 
Proof.
  repeat red.
  einit.
  ecofix CIH; intros * EQ EQ'.
  rewrite itree_eta, (itree_eta s).
  punfold EQ; punfold EQ'; red in EQ; red in EQ'.
  genobs t ot; genobs s os.
  hinduction EQ before CIH0; subst; intros; pclearbot; simpl.

  - estep; split; auto.
    inv EQ'; auto.
  - estep; ebase; right; eapply CIH; eauto.
    rewrite <- tau_eutt.
    rewrite <- (tau_eutt m2); auto.
  - estep; ebase; intros ?; right; eapply CIH0; eauto.
    eapply eqit_Vis; eauto.
  - eapply fold_eqitF in EQ'; eauto.
    assert (t ≈ Tau t1) by (rewrite itree_eta, <- Heqot; reflexivity).
    rewrite H in EQ'.
    apply eqit_inv_tauL in EQ'.
    subst; specialize (IHEQ _ _ eq_refl eq_refl).
    punfold EQ'; red in EQ'.
    specialize (IHEQ EQ').
    rewrite eqit_tauL; [|reflexivity].
    rewrite (itree_eta t1).
    eapply IHEQ. 
  - subst; cbn.
    rewrite tau_euttge.
    rewrite (itree_eta t2); eapply IHEQ; eauto.
    eapply fold_eqitF in EQ'; eauto.
    assert (s ≈ Tau t2).
    rewrite (itree_eta s), <- Heqos; reflexivity.
    rewrite tau_eutt in H.
    assert (eutt RS' t t2).
    rewrite <- H; auto.
    punfold H0.
Qed.

Lemma eutt_disj_l {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS t s ->
    eutt (RS \2/ RS') t s. 
Proof.
  intros.
  eapply eqit_mon with (RR := RS); eauto.
Qed.

Lemma eutt_disj_r {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS' t s ->
    eutt (RS \2/ RS') t s. 
Proof.
  intros.
  eapply eqit_mon with (RR := RS'); eauto.
Qed.

Lemma eutt_equiv {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    (HeterogeneousRelations.eq_rel RS RS') ->
    eutt RS t s <-> eutt RS' t s. 
Proof.
  intros * EQ; split; intros EUTT; eapply eqit_mon; try apply EUTT; eauto.
  all:apply EQ.
Qed.

(* Rewriting equivalent simulation relations under [eq_itree] and [eutt] *)
Global Instance eq_itree_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ((@HeterogeneousRelations.eq_rel R1 R2) ==> Logic.eq ==> Logic.eq ==> iff) (@eq_itree E R1 R2).
Proof.
  repeat intro; subst.
  unfold eq_itree; rewrite H; reflexivity.
Qed.

Global Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper  ((@HeterogeneousRelations.eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  repeat intro; subst.
  unfold eutt; rewrite H; reflexivity.
Qed.

