(** * Simulation Up To Tau *)

Require Import Paco.paco.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core.

From ITree Require Import
     Eq.UpToTaus.

Section SUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive suttF (eutt : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itreeF E R1 (itree E R1))
          (ot2 : itreeF E R2 (itree E R2)) : Prop :=
| suttF_ (FIN: finite_tausF ot1 -> finite_tausF ot2)
         (EQV: forall ot1' ot2'
                  (UNTAUS1: unalltausF ot1 ot1')
                  (UNTAUS2: unalltausF ot2 ot2'),
               eq_notauF RR eutt ot1' ot2')
.
Hint Constructors suttF.

Lemma suttF_unpack eutt ot1 ot2 :
  suttF eutt ot1 ot2 <->
  forall ot1', unalltausF ot1 ot1' ->
  exists ot2', unalltausF ot2 ot2' /\ eq_notauF RR eutt ot1' ot2'.
Proof.
  split.
  - intros [] ot1' H1.
    edestruct FIN; eauto.
  - intros. constructor.
    + intros []; auto. edestruct H as [? []]; eauto.
    + intros; edestruct H as [y []]; eauto.
      replace ot2' with y; auto.
      eapply unalltaus_injective; eauto.
Qed.

Inductive suttF0 (eutt : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itreeF E R1 (itree E R1))
          (ot2 : itreeF E R2 (itree E R2)) : Prop :=
| suttF0_notau ot2' :
    notauF ot1 ->
    unalltausF ot2 ot2' ->
    eq_notauF RR eutt ot1 ot2' ->
    suttF0 eutt ot1 ot2
| suttF0_tau t1 :
    ot1 = TauF t1 ->
    suttF eutt (observe t1) ot2 ->
    suttF0 eutt ot1 ot2
.
Hint Constructors suttF0.

Lemma sutt_inv eutt ot1 ot2 :
  suttF eutt ot1 ot2 <->
  suttF0 eutt ot1 ot2.
Proof.
  split; intros SUTT.
  - destruct SUTT. destruct ot1.
    + assert (Iuat1 : @unalltausF E _ (RetF r) (RetF r)).
      { repeat constructor. }
      edestruct FIN as [ot2' [Iuntaus Inotau]].
      { eauto. }
      eapply suttF0_notau; eauto.
    + eapply suttF0_tau; auto.
      constructor.
      * rewrite finite_taus_tau in FIN; auto.
      * intros. apply EQV; auto.
        eapply unalltaus_tau'; auto.
    + assert (Iuat1 : @unalltausF E _ (VisF e k) (VisF e k)).
      { repeat constructor. }
      edestruct FIN as [ot2' [Iuntaus Inotau]].
      { eauto. }
      eapply suttF0_notau; eauto.
  - destruct SUTT.
    + constructor; eauto.
      intros; auto_untaus.
    + subst; destruct H0; constructor.
      * rewrite finite_taus_tau; auto.
      * intros; auto_untaus.
        eapply unalltaus_tau in UNTAUS1; auto.
        apply EQV; auto.
Qed.

Definition sutt_ (eutt : itree E R1 -> itree E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  suttF eutt (observe t1) (observe t2).
Hint Unfold sutt_.

(* [sutt_] is monotone. *)
Lemma monotone_sutt_ : monotone2 sutt_.
Proof. pmonauto. Qed.
Hint Resolve monotone_sutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition sutt : itree E R1 -> itree E R2 -> Prop := paco2 sutt_ bot2.

Global Arguments sutt t1%itree t2%itree.

End SUTT.

Hint Constructors suttF.
Hint Unfold sutt_.
Hint Resolve monotone_sutt_ : paco.

Hint Constructors suttF0.

Lemma monotone_eq_notauF_RR {E R1 R2} (RR1 RR2 : R1 -> R2 -> Prop)
      {I J} (r : I -> J -> Prop) :
  (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) ->
  forall t1 t2, eq_notauF RR1 r t1 t2 -> @eq_notauF E _ _ RR2 _ _ r t1 t2.
Proof. intros ? ? ? []; auto. Qed.

Lemma monotone_sutt_RR {E R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) r :
  (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) ->
  forall t1 t2, sutt_ RR1 r t1 t2 -> @sutt_ E _ _ RR2 r t1 t2.
Proof.
  intros. induction H0.
  constructor; auto.
  intros.
  edestruct EQV; eauto;
    eapply monotone_eq_notauF_RR; eauto.
Qed.

Theorem sutt_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 -> sutt (flip RR) t2 t1 -> eutt RR t1 t2.
Proof.
  pcofix self; intros t1 t2 H1 H2.
  punfold H1. punfold H2.
  destruct H1 as [FIN1 EQV1], H2 as [FIN2 EQV2].
  pfold; constructor.
  - split; auto.
  - intros.
    eapply eq_notauF_and.
    + intros ? ? I1 I2; right.
      apply self; [ apply I1 | apply I2 ].
    + eapply monotone_eq_notauF; auto using EQV1.
      intros; pclearbot; auto.
    + apply eq_notauF_flip.
      eapply monotone_eq_notauF; auto using EQV2.
      intros; pclearbot; auto.
Qed.

Theorem eutt_sutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR t1 t2 -> sutt RR t1 t2.
Proof.
  pcofix self; intros t1 t2 H1.
  punfold H1.
  destruct H1 as [FIN1 EQV1].
  pfold; constructor.
  - apply FIN1.
  - intros.
    eapply monotone_eq_notauF; eauto.
    intros; pclearbot; auto.
Qed.

Inductive suttF1 {E R} (sutt: itree' E R -> itree' E R -> Prop) :
  itree' E R -> itree' E R -> Prop :=
| suttF1_ret r : suttF1 sutt (RetF r) (RetF r)
| suttF1_vis u (e : E u) k1 k2
      (SUTTK: forall x, sutt (observe (k1 x)) (observe (k2 x))):
    suttF1 sutt (VisF e k1) (VisF e k2)
| suttF1_tau_right ot1 t2
      (EQTAUS: suttF1 sutt ot1 (observe t2)):
    suttF1 sutt ot1 (TauF t2)
| suttF1_tau_left t1 ot2
      (EQTAUS: sutt (observe t1) ot2):
    suttF1 sutt (TauF t1) ot2
.
Hint Constructors suttF1.

Definition sutt1 {E R} (t1 t2 : itree E R) :=
  paco2 (@suttF1 E R) bot2 (observe t1) (observe t2).
Hint Unfold sutt1.

Lemma reflexive_suttF1 {E R} sutt (r1:Reflexive sutt) : Reflexive (@suttF1 E R sutt).
Proof.
  unfold Reflexive. intros x.
  destruct x; eauto.
Qed.

Lemma monotone_suttF1 {E R} : monotone2 (@suttF1 E R).
Proof. repeat red; intros. induction IN; eauto. Qed.
Hint Resolve monotone_suttF1 : paco.

Lemma sutt_to_sutt1 {E R} :
  forall (t1 t2: itree E R), sutt eq t1 t2 -> sutt1 t1 t2.
Proof.
  pcofix self; intros t1 t2 SUTT.
  punfold SUTT. pfold.
  apply sutt_inv in SUTT.
  destruct SUTT.
  - destruct H0 as [Huntaus Hnotau].
    induction Huntaus.
    + destruct H1; subst; auto.
      pclearbot; constructor; right; apply self; apply H0.
    + subst; auto.
  - rewrite H; constructor. right; apply self. pfold; auto.
Qed.

Lemma sutt1_to_sutt {E R} :
  forall (t1 t2: itree E R), sutt1 t1 t2 -> sutt eq t1 t2.
Proof.
  pcofix self; intros t1 t2 SUTT.
  punfold SUTT. pfold. red.
  induction SUTT.
  - apply sutt_inv; eauto 7.
  - pclearbot. apply sutt_inv; eapply suttF0_notau; eauto.
    constructor; auto.
  - destruct IHSUTT. constructor.
    + rewrite finite_taus_tau; auto.
    + intros. eapply unalltaus_tau in UNTAUS2; eauto.
  - pclearbot. apply suttF_unpack.
    intros. eapply unalltaus_tau in H; eauto.
    destruct H as [Huntaus Hnotau].
    revert ot2 EQTAUS; induction Huntaus; intros.
    + punfold EQTAUS. induction EQTAUS.
      * eauto 9.
      * eexists; split.
        { repeat constructor. }
        { pclearbot; constructor; auto. }
      * destruct IHEQTAUS as [? []]; auto.
        eauto using unalltaus_tau'.
      * contradiction.
    + punfold EQTAUS. induction EQTAUS; try discriminate.
      * destruct IHEQTAUS as [? []]; auto.
        eauto using unalltaus_tau'.
      * pclearbot; inv OBS. eauto.
Qed.

Lemma sutt_is_sutt1 {E R} (t1 t2 : itree E R) :
  sutt eq t1 t2 <-> sutt1 t1 t2.
Proof.
  split. apply sutt_to_sutt1. apply sutt1_to_sutt.
Qed.
