(* Equivalence up to taus *)
(* We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. The main consequence of this
   choice is that equivalence up to taus is an equivalence relation.
 *)

(* TODO:
   - Generalize Reflexivity, Symmetry, Transitivity to heterogeneous
     eutt.
   - Make eutt a notation instead of a definition?
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core.ITree.

From ITree Require Export
     Eq.Eq
     Eq.Untaus
     Eq.UpToTaus.

Local Open Scope itree.

Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(* [euttE_ euttE t1 t2] means that, if [t1] or [t2] ever takes a
   visible step ([Vis] or [Ret]), then the other takes the same
   step, and the subsequent continuations (in the [Vis] case) are
   related by [euttE]. In particular, [(t1 = spin)%eq_itree] if
   and only if [(t2 = spin)%eq_itree]. Note also that in that
   case, the parameter [euttE] is irrelevant.

   This is the relation we will take a fixpoint of. *)
Inductive euttEF (euttE : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itreeF E R1 (itree E R1))
          (ot2 : itreeF E R2 (itree E R2)) : Prop :=
| euttEF_ (FIN: finite_tausF ot1 <-> finite_tausF ot2)
         (EQV: forall ot1' ot2'
                  (UNTAUS1: unalltausF ot1 ot1')
                  (UNTAUS2: unalltausF ot2 ot2'),
               eq_notauF RR euttE ot1' ot2')
.
Hint Constructors euttEF.

Definition euttE_ (euttE : itree E R1 -> itree E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  euttEF euttE (observe t1) (observe t2).
Hint Unfold euttE_.

(* [euttE_] is monotone. *)
Lemma monotone_euttE_ : monotone2 euttE_.
Proof. pmonauto. Qed.
Hint Resolve monotone_euttE_ : paco.

(* We now take the greatest fixpoint of [euttE_]. *)

(* Equivalence Up To Taus.

   [euttE t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition euttE : itree E R1 -> itree E R2 -> Prop := wcpn2 euttE_ bot2 bot2.
Hint Unfold euttE.

Global Arguments euttE t1%itree t2%itree.

(* Lemmas about the auxiliary relations. *)

(* Many have a name [X_Y] to represent an implication
   [X _ -> Y _] (possibly with more arguments on either side). *)

(**)

Lemma euttEF_tau r t1 t2 t1' t2'
    (OBS1: TauF t1' = observe t1)
    (OBS2: TauF t2' = observe t2)
    (REL: euttE_ r t1' t2'):
  euttE_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - simpobs. rewrite !finite_taus_tau. eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Lemma euttEF_tau_left r t1 t2 t1'
    (OBS: TauF t1 = observe t1')
    (REL: euttE_ r t1' t2):
  euttE_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite <- FIN. symmetry. rewrite <- OBS. rewrite <- finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS1. constructor; auto.
    econstructor; eauto.
Qed.

Lemma euttEF_tau_right r t1 t2 t2'
    (OBS: TauF t2 = observe t2')
    (REL: euttE_ r t1 t2'):
  euttE_ r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - rewrite FIN. rewrite <- OBS. rewrite <- finite_taus_tau; eauto. reflexivity.
  - intros. eapply EQV; eauto. rewrite <- OBS. inversion UNTAUS2. constructor; auto.
    econstructor; eauto.
Qed.

Lemma euttEF_vis {u} (r : _ -> _ -> Prop) t1 t2 (e : _ u) k1 k2
    (OBS1: VisF e k1 = observe t1)
    (OBS2: VisF e k2 = observe t2)
    (REL: forall x, r (k1 x) (k2 x)):
  euttE_ r t1 t2.
Proof.
  intros. econstructor.
  - split; intros; eapply notau_finite_taus; eauto.
  - intros.
    apply unalltaus_notau_id in UNTAUS1; eauto.
    apply unalltaus_notau_id in UNTAUS2; eauto.
    simpobs. subst. eauto.
Qed.

(**)

Lemma euttE_Ret x y :
  RR x y -> euttE (Ret x) (Ret y).
Proof.
  intros. wstep.
  constructor.
  split; intros; eapply finite_taus_ret; reflexivity.
  intros.
  apply unalltausF_ret in UNTAUS1.
  apply unalltausF_ret in UNTAUS2.
  subst; constructor; assumption.
Qed.

Lemma euttE_Vis {U} (e: E U) k k' :
  (forall x, euttE (k x) (k' x)) ->
  euttE (Vis e k) (Vis e k').
Proof.
  intros.
  wstep; constructor.
  split; intros; eapply finite_taus_vis; reflexivity.
  intros.
  cbn in *.
  apply unalltausF_vis in UNTAUS1.
  apply unalltausF_vis in UNTAUS2.
  subst; constructor.
  intros x; specialize (H x).
  wunfold H. eauto with paco.
Qed.

End EUTT.

Hint Unfold euttE_.
Hint Unfold euttE.
Hint Constructors euttEF.
Hint Resolve monotone_euttE_ : paco.

Lemma Symmetric_euttEF_ {E R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (ot1 : itree' E R1) (ot2 : itree' E R2) :
  euttEF RR1 r1 ot1 ot2 ->
  euttEF RR2 r2 ot2 ot1.
Proof.
  intros []; split.
  - split; apply FIN.
  - intros. specialize (EQV _ _ UNTAUS2 UNTAUS1).
    eapply Symmetric_eq_notauF_; eauto.
Qed.

Lemma Transitive_euttEF_ {E R1 R2 R3}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (RR3 : R1 -> R3 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop)
      (r3 : _ -> _ -> Prop)
      (TRANS_RR : forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR3 r1 r3)
      (TRANS_r : forall i j k, r1 i j -> r2 j k -> r3 i k)
      (ot1 : itree' E R1) ot2 ot3 :
  euttEF RR1 r1 ot1 ot2 ->
  euttEF RR2 r2 ot2 ot3 ->
  euttEF RR3 r3 ot1 ot3.
Proof.
  intros [] [].
  constructor.
  - etransitivity; eauto.
  - intros t1' t3' H1 H3.
    assert (FIN2 : finite_tausF ot2).
    { apply FIN; eauto. }
    destruct FIN2 as [t2' []].
    eapply Transitive_eq_notauF_; eauto.
Qed.

Lemma Symmetric_euttE_ {E R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    wcpn2 (euttE_ RR1) bot2 bot2 t1 t2 -> wcpn2 (euttE_ RR2) bot2 bot2 t2 t1.
Proof.
  wcofix self; wstep.
  intros t1 t2 H12.
  wunfold H12.
  eapply Symmetric_euttEF_; try eassumption.
  intros. eauto with paco.
Qed.

Lemma Transitive_euttE_ {E R1 R2 R3}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (RR3 : R1 -> R3 -> Prop)
      (TRANS_RR : forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR3 r1 r3) :
  forall (t1 : itree E R1) t2 t3,
    euttE RR1 t1 t2 -> euttE RR2 t2 t3 -> euttE RR3 t1 t3.
Proof.
  wcofix self; wstep.
  intros t1 t2 t3 H12 H23.
  wunfold H12; wunfold H23.
  eapply Transitive_euttEF_; try eassumption.
  eauto with paco.
Qed.

Section EUTT_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Definition subrelation_eq_euttE :
  @subrelation (itree E R) (eq_itree RR) (euttE RR).
Proof.
  wcofix CIH; wstep. intros.
  econstructor.
  { split; [|apply flip_eq_itree in H0]; intros; destruct H as [n [? ?]]; eauto using eq_unalltaus. }

  intros. eapply eq_unalltaus_eqF in H0; eauto. destruct H0 as [s' [UNTAUS' EQV']].
  hexploit @unalltaus_injective; [apply UNTAUS' | apply UNTAUS2 | intro X]; subst.
  inv EQV'; simpobs; eauto with paco.
  eapply unalltaus_notau in UNTAUS1. contradiction.
Qed.

Global Instance Reflexive_euttEF `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive r -> Reflexive (euttEF RR r).
Proof.
  split.
  - reflexivity.
  - intros.
    erewrite (unalltaus_injective _ _ _ UNTAUS1 UNTAUS2).
    apply Reflexive_eq_notauF; eauto.
Qed.

Global Instance Symmetric_euttEF `{Symmetric _ RR}
         (r : itree E R -> itree E R -> Prop) :
  Symmetric r -> Symmetric (euttEF RR r).
Proof.
  intros SYM x y. apply Symmetric_euttEF_; auto.
Qed.

Global Instance Transitive_euttEF `{Transitive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Transitive r -> Transitive (euttEF RR r).
Proof.
  intros TRANS x y z. apply Transitive_euttEF_; auto.
Qed.

Global Instance Symmetric_euttE `{Symmetric _ RR}:
  Symmetric (wcpn2 (@euttE_ E _ _ RR) bot2 bot2).
Proof. red. eapply Symmetric_euttE_. eauto. Qed.

Global Instance Reflexive_euttE `{Reflexive _ RR}
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (wcpn2 (euttE_ RR) r rg).
Proof.
  repeat intro. eapply wcpn2_mon_bot with (gf:=euttE_ RR); eauto with paco.
  revert x. wcofix CIH; wstep.
  intros. apply Reflexive_euttEF; eauto with paco.
Qed.

End EUTT_rel.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Let euttE : itree E R -> itree E R -> Prop := euttE eq.

Global Instance Transitive_euttE : Transitive euttE.
Proof.
  red; eapply Transitive_euttE_; eauto.
  intros; subst; eauto.
Qed.

(**)

(* [euttE] is preserved by removing one [Tau]. *)
Lemma tauF_euttE (t t': itree E R) (OBS: TauF t' = observe t): euttE t t'.
Proof.
  wstep. split.
  - simpobs. rewrite finite_taus_tau. reflexivity.
  - intros t1' t2' H1 H2.
    eapply unalltaus_tau in H1; eauto.
    pose proof (unalltaus_injective _ _ _ H1 H2).
    subst; apply Reflexive_eq_notauF; eauto.
    apply Reflexive_euttE. repeat intro. eauto.
Qed.

Lemma tau_euttE (t: itree E R) : euttE (Tau t) t.
Proof.
  eapply tauF_euttE. eauto.
Qed.

(* [euttE] is preserved by removing all [Tau]. *)
Lemma untaus_euttE (t t' : itree E R) : untausF (observe t) (observe t') -> euttE t t'.
Proof.
  intros H.
  wstep. split.
  - eapply untaus_finite_taus; eauto.
  - induction H; intros.
    + rewrite (unalltaus_injective _ _ _ UNTAUS1 UNTAUS2).
      apply Reflexive_eq_notauF; eauto.
      apply Reflexive_euttE. repeat intro; eauto.
    + eapply unalltaus_tau in UNTAUS1; eauto.
Qed.

(* We can now rewrite with [euttE] equalities. *)
Global Instance Equivalence_euttE : @Equivalence (itree E R) euttE.
Proof.
  constructor; try typeclasses eauto.
  - apply Reflexive_euttE. repeat intro; eauto.
  - eapply Symmetric_euttE. repeat intro; eauto.
Qed.

(**)

Global Instance euttE_go : Proper (going euttE ==> euttE) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance euttE_observe : Proper (euttE ==> going euttE) observe.
Proof.
  constructor. wunfold H. wstep. destruct H. econstructor; eauto.
Qed.

Global Instance euttE_tauF : Proper (euttE ==> going euttE) (fun t => TauF t).
Proof.
  constructor; wstep. wunfold H.
  destruct H. econstructor.
  - split; intros; simpl.
    + rewrite finite_taus_tau, <-FIN, <-finite_taus_tau; eauto.
    + rewrite finite_taus_tau, FIN, <-finite_taus_tau; eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Global Instance euttE_VisF {u} (e: E u) :
  Proper (pointwise_relation _ euttE ==> going euttE) (VisF e).
Proof.
  constructor; wstep. red in H. econstructor.
  - repeat econstructor.
  - intros.
    destruct UNTAUS1 as [UNTAUS1 Hnotau1].
    destruct UNTAUS2 as [UNTAUS2 Hnotau2].
    dependent destruction UNTAUS1.
    dependent destruction UNTAUS2. simpobs.
    econstructor; intros; apply H.
Qed.

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Global Instance euttE_finite_taus :
  Proper (going euttE ==> flip impl) finite_tausF.
Proof.
  intros ? ? [] ?; wunfold H. eapply H. eauto.
Qed.

End EUTT_eq.

(**)

Lemma euttE_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  euttE RR t1 t2 -> euttE RR (Tau t1) (Tau t2).
Proof.
  intros H.
  wstep. eapply euttEF_tau. reflexivity. reflexivity. wunfold H. eauto.
Qed.

(* Lemmas about [bind]. *)

Inductive euttE_bind_clo {E R1 R2} (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| euttE_bind_clo_intro U1 U2 RU t1 t2 k1 k2
      (EQV: @euttE E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (k1 v1) (k2 v2))
  : euttE_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors euttE_bind_clo.

Lemma bind_clo_finite_taus {E U1 U2 RU R1 R2}  t1 t2 k1 k2
    (FT: finite_taus (@ITree.bind' E U1 R1 k1 t1))
    (FTk: forall v1 v2 (RELv: RU v1 v2 : Prop), finite_taus (k1 v1) -> finite_taus (k2 v2))
    (EQV: euttE RU t1 t2):
  finite_taus (@ITree.bind' E U2 R2 k2 t2).
Proof.
  wunfold EQV. destruct EQV as [[FTt _] EQV].
  assert (FT1 := FT). apply finite_taus_bind_fst in FT1.
  assert (FT2 := FT1). apply FTt in FT2.
  destruct FT1 as [a [FT1 NT1]], FT2 as [b [FT2 NT2]].
  rewrite @untaus_finite_taus in FT; [|eapply untaus_bindF, FT1].
  rewrite unfold_bind. genobs t2 ot2. clear Heqot2 t2.
  induction FT2.
  - destruct ot0; inv NT2; simpl; eauto 7.
    hexploit EQV; eauto. intros EQV'. inv EQV'.
    rewrite unfold_bind in FT. eauto.
  - subst. eapply finite_taus_tau; eauto.
    eapply IHFT2; eauto using unalltaus_tau'.
Qed.

Lemma euttE_clo_bind {E R1 R2} RR : euttE_bind_clo <3= cpn2 (@euttE_ E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR. split.
  - assert (EQV':=EQV).
    eapply (Symmetric_euttE_ RU (flip RU)) in EQV'; eauto.
    split; intros; eapply bind_clo_finite_taus; eauto; intros.
    + eapply REL; eauto.
    + eapply REL; eauto.
  - wunfold EQV. destruct EQV.
    intros.
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS1|]. intros [a FT1].
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS2|]. intros [b FT2].
    specialize (EQV _ _ FT1 FT2).
    destruct FT1 as [FT1 Hnotau1]. destruct FT2 as [FT2 Hnotau2].
    hexploit @untaus_bindF; [ eapply FT1 | ]. intros UT1.
    hexploit @untaus_bindF; [ eapply FT2 | ]. intros UT2.
    hexploit @untaus_unalltaus_rev; [apply UT1| |]. eauto. intros UAT1.
    hexploit @untaus_unalltaus_rev; [apply UT2| |]; eauto. intros UAT2.
    inv EQV.
    + rewrite unfold_bind in UAT1. rewrite unfold_bind in UAT2. cbn in *.
      edestruct REL; eauto.
      eapply monotone_eq_notauF; eauto with rclo.
    + rewrite unfold_bind in UAT1. rewrite unfold_bind in UAT2. cbn in *.
      destruct UAT1 as [UAT1 _]. destruct UAT2 as [UAT2 _].
      dependent destruction UAT1. dependent destruction UAT2. simpobs.
      econstructor. intros. specialize (H x). eauto with rclo.
Qed.

Inductive euttE_trans_clo {E R1 R2} (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| euttE_pre_clo_intro t1 t2 t3 t4
      (EQVl: euttE eq t1 t2)
      (EQVr: euttE eq t4 t3)
      (REL: r t2 t3)
  : euttE_trans_clo r t1 t4
.
Hint Constructors euttE_trans_clo.

Lemma euttE_clo_trans {E R1 R2} RR : euttE_trans_clo <3= cpn2 (@euttE_ E R1 R2 RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. inv PR.
  wunfold EQVl. wunfold EQVr. destruct EQVl, EQVr. split.
  { rewrite FIN, FIN0. destruct REL. eauto. }

  intros. apply proj1 in FIN. edestruct FIN as [n'' [t2'' TAUS'']]; [eexists; eauto|].
  hexploit EQV; eauto. intros EUTT1.
  apply proj1 in FIN0. edestruct FIN0 as [n''' [t2''' TAUS''']]; [eexists; eauto|].
  hexploit EQV0; eauto. intros EUTT2.
  destruct REL.
  hexploit EQV1; eauto. intros EUTT3.
  destruct EUTT1; destruct EUTT2;
    try (solve [subst; inversion EUTT3; auto]).
  remember (VisF _ _) as o2 in EUTT3.
  remember (VisF _ _) as o3 in EUTT3.
  inversion EUTT3; subst; try discriminate.
  inversion H2; clear H2; inversion H3; clear H3.
  subst; auto_inj_pair2; subst.
  econstructor. intros.
  specialize (H x); specialize (H0 x); specialize (H1 x).
  eauto with rclo.
Qed.

Arguments euttE_clo_trans : clear implicits.


Section EUTT_eq_EUTTE.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma euttE__impl_eutt_ r t1 t2 :
  @euttE_ E R1 R2 RR r t1 t2 -> eutt0 RR r t1 t2.
Proof.
  revert t1 t2. wcofix CIH'; wstep. intros. destruct H0. repeat red.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  assert (EM: notauF ot1 \/ notauF ot2 \/ ~(notauF ot1 \/ notauF ot2))
    by (destruct ot1, ot2; simpl; tauto).
  destruct EM as [EM|[EM|EM]].
  - destruct FIN as [FIN _].
    hexploit FIN; eauto 7. clear FIN; intro FIN.
    destruct FIN as [ot' [UNTAUS NOTAU]].
    hexploit EQV; eauto. intros EQNT.
    induction UNTAUS; subst.
    { inv EQNT; eauto with paco. }
    hexploit IHUNTAUS; eauto.
    { intros. destruct UNTAUS1.
      dependent destruction H; [|subst; contradiction].
      hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
    }
  - destruct FIN as [_ FIN].
    hexploit FIN; eauto 7. clear FIN; intro FIN.
    destruct FIN as [ot' [UNTAUS NOTAU]].
    hexploit EQV; eauto. intros EQNT.
    induction UNTAUS; subst.
    { inv EQNT; eauto with paco. }
    hexploit IHUNTAUS; eauto.
    { intros. destruct UNTAUS2.
      dependent destruction H; [|subst; contradiction].
      hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
    }
  - destruct ot1, ot2; simpl in *; try tauto.
    econstructor. wbase. apply CIH'.
    econstructor.
    + rewrite !finite_taus_tau in FIN. eauto.
    + eauto using unalltaus_tau'.
Qed.

Lemma euttE_impl_eutt t1 t2 :
  wcpn2 (@euttE_ E R1 R2 RR) bot2 bot2 t1 t2 -> wcpn2 (eutt0 RR) bot2 bot2 t1 t2.
Proof.
  intros. eapply wcpn2_mon_bot; eauto using euttE__impl_eutt_ with paco.
Qed.

Lemma eutt_impl_euttE t1 t2 :
  wcpn2 (@eutt0 E R1 R2 RR) bot2 bot2 t1 t2 -> wcpn2 (euttE_ RR) bot2 bot2 t1 t2.
Proof.
  revert_until RR. wcofix CIH; wstep. intros.
  rename H0 into H. do 2 wunfold H. repeat red in H. econstructor; intros.
  - split; intros.
    + genobs_clear t1 ot1. genobs_clear t2 ot2.
      destruct H0 as [ot' [UNTAUS NOTAU]].
      move UNTAUS before r. revert_until UNTAUS.
      induction UNTAUS; intros.
      * induction H; eauto; try contradiction.
        rewrite finite_taus_tau. eauto.
      * induction H; eauto 7; try inv OBS
        ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
        wunfold EQTAUS. eauto.
    + genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
      destruct H0 as [ot' [UNTAUS NOTAU]].
      move UNTAUS before r. revert_until UNTAUS.
      induction UNTAUS; intros.
      * induction H; eauto; try contradiction.
        rewrite finite_taus_tau. eauto.
      * induction H; eauto 7; try inv OBS
        ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
        wunfold EQTAUS. eauto.
  - genobs_clear t1 ot1. genobs_clear t2 ot2.
    destruct UNTAUS1 as [UNTAUS1 NT1]. destruct UNTAUS2 as [UNTAUS2 NT2].
    move UNTAUS2 before r. move UNTAUS1 before r. revert_until UNTAUS1.
    induction UNTAUS1.
    + induction 1; intros.
      * inv H; try contradiction; eauto.
        econstructor. intros.
        edestruct EUTTK as [TMP | TMP]; eauto with paco; contradiction.
      * subst. inv H; try contradiction. eauto.
    + induction 1; intros; subst.
      * inv H; try contradiction; eauto.
      * inv H; try contradiction; eauto.
        eapply IHUNTAUS1; eauto.
        wunfold EQTAUS. eauto.
Qed.

Lemma eutt_is_euttE t1 t2 :
  wcpn2 (@eutt0 E R1 R2 RR) bot2 bot2 t1 t2 <-> wcpn2 (euttE_ RR) bot2 bot2 t1 t2.
Proof. split; eauto using euttE_impl_eutt, eutt_impl_euttE. Qed.

End EUTT_eq_EUTTE.
