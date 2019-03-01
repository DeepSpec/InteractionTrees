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
     Core.

From ITree Require Export
     Eq.Eq
     Eq.Untaus.

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
Definition euttE : itree E R1 -> itree E R2 -> Prop := paco2 euttE_ bot2.
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

Lemma euttE_strengthen :
  forall r (t1 : itree E R1) (t2 : itree E R2)
     (FIN: finite_taus t1 <-> finite_taus t2)
     (EQV: forall t1' t2'
              (UNT1: unalltaus t1 t1')
              (UNT2: unalltaus t2 t2'),
         paco2 (euttE_ ∘ gres2 euttE_) r t1' t2'),
    paco2 (euttE_ ∘ gres2 euttE_) r t1 t2.
Proof.
  intros. pfold. econstructor; eauto.
  intros.
  hexploit (EQV (go ot1') (go ot2')); eauto.
  intros EQV'. punfold EQV'. destruct EQV'.
  eapply EQV0;
    repeat constructor; eauto.
Qed.

(**)

Lemma euttE_Ret x y :
  RR x y -> euttE (Ret x) (Ret y).
Proof.
  intros; pfold.
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
  pfold; constructor.
  split; intros; eapply finite_taus_vis; reflexivity.
  intros.
  cbn in *.
  apply unalltausF_vis in UNTAUS1.
  apply unalltausF_vis in UNTAUS2.
  subst; constructor.
  intros x; specialize (H x).
  punfold H.
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
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    paco2 (euttE_ RR1) r1 t1 t2 -> paco2 (euttE_ RR2) r2 t2 t1.
Proof.
  pcofix self.
  intros t1 t2 H12.
  punfold H12.
  pfold.
  eapply Symmetric_euttEF_; try eassumption.
  intros ? ? []; auto.
Qed.

Lemma Transitive_euttE_ {E R1 R2 R3}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (RR3 : R1 -> R3 -> Prop)
      (TRANS_RR : forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR3 r1 r3) :
  forall (t1 : itree E R1) t2 t3,
    euttE RR1 t1 t2 -> euttE RR2 t2 t3 -> euttE RR3 t1 t3.
Proof.
  pcofix self.
  intros t1 t2 t3 H12 H23.
  punfold H12; punfold H23; pfold.
  eapply Transitive_euttEF_; try eassumption.
  intros; pclearbot; eauto.
Qed.

Section EUTT_rel.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_euttE :
  @subrelation (itree E R) (eq_itree RR) (euttE RR).
Proof.
  pcofix CIH. intros.
  pfold. econstructor.
  { split; [|apply flip_eq_itree in H0]; intros; destruct H as [n [? ?]]; eauto using eq_unalltaus. }

  intros. eapply eq_unalltaus_eqF in H0; eauto. destruct H0 as [s' [UNTAUS' EQV']].
  hexploit @unalltaus_injective; [apply UNTAUS' | apply UNTAUS2 | intro X]; subst.
  inv EQV'; simpobs; eauto.
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

Global Instance Symmetric_euttE `{Symmetric _ RR}
       (r : itree E R -> itree E R -> Prop)
       (Sr : Symmetric r) :
  Symmetric (paco2 (euttE_ RR) r).
Proof. red; eapply Symmetric_euttE_; eauto. Qed.

Global Instance Reflexive_euttE `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (paco2 (euttE_ RR) r).
Proof.
  pcofix CIH.
  intros. pfold. red. apply Reflexive_euttEF; eauto.
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
  pfold. split.
  - simpobs. rewrite finite_taus_tau. reflexivity.
  - intros t1' t2' H1 H2.
    eapply unalltaus_tau in H1; eauto.
    pose proof (unalltaus_injective _ _ _ H1 H2).
    subst; apply Reflexive_eq_notauF; eauto.
    left. apply reflexivity.
Qed.

Lemma tau_euttE (t: itree E R) : euttE (Tau t) t.
Proof.
  eapply tauF_euttE. eauto.
Qed.

(* [euttE] is preserved by removing all [Tau]. *)
Lemma untaus_euttE (t t' : itree E R) : untausF (observe t) (observe t') -> euttE t t'.
Proof.
  intros H.
  pfold. split.
  - eapply untaus_finite_taus; eauto.
  - induction H; intros.
    + rewrite (unalltaus_injective _ _ _ UNTAUS1 UNTAUS2).
      apply Reflexive_eq_notauF; eauto.
      left; apply reflexivity.
    + eapply unalltaus_tau in UNTAUS1; eauto.
Qed.

(* We can now rewrite with [euttE] equalities. *)
Global Instance Equivalence_euttE : @Equivalence (itree E R) euttE.
Proof. constructor; typeclasses eauto. Qed.

(**)

Global Instance euttE_go : Proper (going euttE ==> euttE) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance euttE_observe : Proper (euttE ==> going euttE) observe.
Proof.
  constructor. punfold H. pfold. destruct H. econstructor; eauto.
Qed.

Global Instance euttE_tauF : Proper (euttE ==> going euttE) (fun t => TauF t).
Proof.
  constructor; pfold. punfold H.
  destruct H. econstructor.
  - split; intros; simpl.
    + rewrite finite_taus_tau, <-FIN, <-finite_taus_tau; eauto.
    + rewrite finite_taus_tau, FIN, <-finite_taus_tau; eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Global Instance euttE_VisF {u} (e: E u) :
  Proper (pointwise_relation _ euttE ==> going euttE) (VisF e).
Proof.
  constructor; pfold. red in H. econstructor.
  - repeat econstructor.
  - intros.
    destruct UNTAUS1 as [UNTAUS1 Hnotau1].
    destruct UNTAUS2 as [UNTAUS2 Hnotau2].
    dependent destruction UNTAUS1.
    dependent destruction UNTAUS2. simpobs.
    econstructor; intros; left; apply H.
Qed.

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Global Instance euttE_finite_taus :
  Proper (going euttE ==> flip impl) finite_tausF.
Proof.
  intros ? ? [] ?; punfold H. eapply H. eauto.
Qed.

End EUTT_eq.

(**)

Lemma euttE_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  euttE RR t1 t2 -> euttE RR (Tau t1) (Tau t2).
Proof.
  intros H.
  pfold. eapply euttEF_tau. reflexivity. reflexivity. punfold H.
Qed.

(* Lemmas about [bind]. *)

Inductive euttE_bind_clo {E R1 R2} (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| euttE_bind_clo_intro U (t1 t2: itree E U) k1 k2
      (EQV: euttE eq t1 t2)
      (REL: forall v, r (k1 v) (k2 v))
  : euttE_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors euttE_bind_clo.

Lemma bind_clo_finite_taus {E U R1 R2}  t1 t2 k1 k2
    (FT: finite_taus (@ITree.bind E U R1 t1 k1))
    (FTk: forall v, finite_taus (k1 v) -> finite_taus (k2 v))
    (EQV: euttE eq t1 t2):
  finite_taus (@ITree.bind E U R2 t2 k2).
Proof.
  punfold EQV. destruct EQV as [[FTt _] EQV].
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

Lemma euttE_clo_bind {E R1 R2} RR : weak_respectful2 (@euttE_ E R1 R2 RR) euttE_bind_clo.
Proof.
  econstructor; [pmonauto|].
  intros. destruct PR. split.
  - assert (EQV':=EQV). symmetry in EQV'.
    split; intros; eapply bind_clo_finite_taus; eauto; intros.
    + edestruct GF; eauto. apply FIN. eauto.
    + edestruct GF; eauto. apply FIN. eauto.
  - punfold EQV. destruct EQV.
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
      eapply GF in REL. destruct REL.
      eapply monotone_eq_notauF; eauto using rclo2.
    + rewrite unfold_bind in UAT1. rewrite unfold_bind in UAT2. cbn in *.
      destruct UAT1 as [UAT1 _]. destruct UAT2 as [UAT2 _].
      dependent destruction UAT1. dependent destruction UAT2. simpobs.
      econstructor. intros. specialize (H x). pclearbot. fold_bind. eauto using rclo2.
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

Lemma euttE_clo_trans {E R1 R2} RR :
  weak_respectful2 (@euttE_ E R1 R2 RR) euttE_trans_clo.
Proof.
  econstructor; [pmonauto|].
  intros. inv PR.
  punfold EQVl. punfold EQVr. destruct EQVl, EQVr. split.
  { rewrite FIN, FIN0. apply GF in REL. destruct REL. eauto. }

  intros. apply proj1 in FIN. edestruct FIN as [n'' [t2'' TAUS'']]; [eexists; eauto|].
  hexploit EQV; eauto. intros EUTT1.
  apply proj1 in FIN0. edestruct FIN0 as [n''' [t2''' TAUS''']]; [eexists; eauto|].
  hexploit EQV0; eauto. intros EUTT2.
  apply GF in REL. destruct REL.
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
  pclearbot. eauto using rclo2.
Qed.

Arguments euttE_clo_trans : clear implicits.
