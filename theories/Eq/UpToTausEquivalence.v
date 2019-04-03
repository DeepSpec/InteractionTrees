(* begin hide *)
From Coq Require Import
     Program
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.CategoryOps
     Basics.Function
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Eq
     Eq.UpToTausCore.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

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
  revert_until r. gcofix CIH; gstep. intros.
  gunfold REL. do 2 gunfold EQV. repeat red in EQV, REL |- *.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - eauto 9 using euttF_mon, gcpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot3) eqn: ISTAU.
    + destruct ot3; inv ISTAU.
      econstructor. gbase. eapply CIH. eauto with paco.
      gstep. rewrite (itree_eta' (TauF t)) in REL.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. gunfold EQTAUS. repeat red in EQTAUS. genobs_clear t2 ot.
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
    gunfold EQTAUS. eauto.
Qed.

Lemma eutt_clo_trans_right : clo_trans_eutt_right <3= cpn2 (@eutt0 E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. gcofix CIH; gstep. intros.
  gunfold REL. do 2 gunfold EQV. repeat red in EQV, REL |- *.
  genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - eauto 9 using euttF_mon, gcpn2_mon_bot with rclo paco.
  - remember (VisF e k2) as o.
    move REL before CIH. revert_until REL.
    induction REL; intros; subst; try dependent destruction Heqo; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - destruct (isb_tau ot1) eqn: ISTAU.
    + destruct ot1; inv ISTAU.
      econstructor. gbase. eapply CIH. eauto with paco.
      gstep. rewrite (itree_eta' (TauF t2)) in REL.
      eapply euttF_elim_tau_left in REL.
      eapply euttF_elim_tau_right in REL. eauto.
    + repeat red in REL. dependent destruction REL; simpobs; inv ISTAU.
      econstructor. gunfold EQTAUS. repeat red in EQTAUS. genobs_clear t2 ot.
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
    gunfold EQTAUS. eauto.
Qed.

Lemma eutt_clo_bind : clo_bind <3= cpn2 (@eutt0 E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  revert_until r. gcofix CIH; gstep. intros.
  do 2 gunfold EQV. repeat red in EQV |- *.
  rewrite !unfold_bind.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  move EQV before CIH. revert_until EQV.
  induction EQV; intros; subst.
  - specialize (REL _ _ RBASE). gunfold REL.
    eauto 9 using euttF_mon, gcpn2_mon_bot with rclo paco.
  - econstructor. intros.
    edestruct EUTTK; eauto 7 with rclo paco.
  - simpl. eauto 8 with paco.
  - econstructor. rewrite unfold_bind. eapply IHEQV. eauto.
  - econstructor. rewrite unfold_bind. eapply IHEQV. eauto.
Qed.

Global Instance eutt_cong_gcpn (r rg: itree E R1 -> itree E R2 -> Prop) :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gcpn2 (@eutt0 E R1 R2 RR) r rg).
Proof.
  repeat intro.
  gclo eutt_clo_trans_left. econstructor. eauto.
  gclo eutt_clo_trans_right. econstructor. eauto.
  eauto.
Qed.

Global Instance eutt_eq_under_rr_impl :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> flip impl) (eutt RR).
Proof.
  repeat intro. red. rewrite H, H0. eauto with paco.
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
  gclo eutt_clo_bind. econstructor; eauto.
  intros. subst. eauto with paco.
Qed.

Section EUTT0_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma eutt0_clo_trans r rg:
  clo_trans_eq <3= cpn2 (@eutt0_ E R1 R2 RR (gcpn2 (eutt0 RR) r rg)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  gunfold EQVl. gunfold EQVr. repeat red in EQVl, EQVr. repeat red in REL |- *.
  move REL before r0. revert_until REL.
  induction REL; intros; subst; 
    try (dependent destruction EQVl; dependent destruction EQVr; []); simpobs.
  - eauto.
  - econstructor. intros.
    edestruct EUTTK.
    + left. rewrite REL, REL0. eauto.
    + right. eapply rclo2_clo. econstructor; eauto with rclo.
  - econstructor. eapply rclo2_clo. econstructor; eauto with rclo.
  - dependent destruction EQVl. gunfold REL0. simpobs. eauto.
  - dependent destruction EQVr. gunfold REL0. simpobs. eauto.
Qed.

Global Instance eq_cong_eutt0 r rg r0 rg0 :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gcpn2 (@eutt0_ E R1 R2 RR (gcpn2 (eutt0 RR) r rg)) r0 rg0).
Proof.
  repeat intro.
  gclo eutt0_clo_trans. econstructor; eauto.
Qed.

Lemma eutt0_clo_bind r rg:
  clo_bind <3= cpn2 (@eutt0_ E R1 R2 RR (gcpn2 (eutt0 RR) r rg)).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  do 2 gunfold EQV. repeat red in REL |- *. repeat red in EQV.
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


Section EUTT_eq2.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  repeat intro. rewrite H, H0. reflexivity.
Qed.

(* We can now rewrite with [eutt] equalities. *)
Global Instance Equivalence_eutt : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

End EUTT_eq2.

Lemma eutt0_tau_left {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) r rg r0 rg0 (x: itree E _) y: 
  gcpn2 (eutt0_ RR (gcpn2 (eutt0 RR) r rg)) r0 rg0 x y ->
  gcpn2 (eutt0_ RR (gcpn2 (eutt0 RR) r rg)) r0 rg0 (Tau x) y.
Proof.
  intros.
  rewrite <- (bind_ret_ () (fun _ => y)), <- (bind_ret_ () (fun _ => x)), <- bind_tau_.
  gclo eutt0_clo_bind. econstructor.
  - rewrite tau_eutt. reflexivity.
  - intros; subst. eauto.
Qed.

Lemma eutt0_tau_right {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) r rg r0 rg0 (x: itree E _) y:
  gcpn2 (eutt0_ RR (gcpn2 (eutt0 RR) r rg)) r0 rg0 x y ->
  gcpn2 (eutt0_ RR (gcpn2 (eutt0 RR) r rg)) r0 rg0 x (Tau y).
Proof.
  intros.
  rewrite <- (bind_ret_ () (fun _ => y)), <- (bind_ret_ () (fun _ => x)), <- bind_tau_.
  gclo eutt0_clo_bind. econstructor.
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
  gstep. gcofix CIH'. intros.
  rewrite (unfold_forever x), (unfold_forever y).
  gclo eutt0_clo_bind. econstructor; eauto.
  intros. subst. gstep. econstructor. eauto with paco.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    eutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
                  @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  gclo eutt_clo_bind. eauto 7 with paco.
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
  gstep. gcofix CIH. intros.
  rewrite !unfold_aloop'. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite bind_tau. gstep. constructor.
    rewrite !bind_bind.
    gclo eutt0_clo_bind. econstructor.
    { reflexivity. }
    intros ? _ [].
    rewrite bind_ret.
    eauto with paco.
  - rewrite bind_ret_. apply eutt0_tau_right.
    rewrite bind_ret_.
    revert b. gcofix CIH'. intros.
    rewrite !unfold_aloop'. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn.
    + rewrite map_bind. gstep. constructor.
      gclo eutt0_clo_bind. econstructor; [reflexivity|].
      intros. subst. eauto with paco.
    + gstep. econstructor. reflexivity.
Qed.
