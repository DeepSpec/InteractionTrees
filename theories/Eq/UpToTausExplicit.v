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

(* Equivalence between visible steps of computation (i.e., [Vis] or
   [Ret], parameterized by a relation [euttE] between continuations
   in the [Vis] case. *)
Variant eq_notauF {I J} (euttE : I -> J -> Prop)
: itreeF E R1 I -> itreeF E R2 J -> Prop :=
| Eutt_ret : forall r1 r2,
    RR r1 r2 ->
    eq_notauF euttE (RetF r1) (RetF r2)
| Eutt_vis : forall u (e : E u) k1 k2,
    (forall x, euttE (k1 x) (k2 x)) ->
    eq_notauF euttE (VisF e k1) (VisF e k2).
Hint Constructors eq_notauF.

Lemma eq_notauF_vis_inv1 {I J} {euttE : I -> J -> Prop} {U}
  ot (e : E U) k :
  eq_notauF euttE ot (VisF e k) ->
  exists k',
    ot = VisF e k' /\ (forall x, euttE (k' x) (k x)).
Proof.
  intros. remember (VisF e k) as t.
  inversion H; subst; try discriminate.
  inversion H2; subst; auto_inj_pair2; subst; eauto.
Qed.

(*
Variant eq_notauF' {I} (euttE : relation I)
: relation (itreeF E R I) :=
| Eutt_ret' : forall r, eq_notauF' euttE (RetF r) (RetF r)
| Eutt_vis' : forall {u1 u2} (e1 : E u1) (e2 : E u2) k1 k2,
    eq_dep _ E _ e1 _ e2 ->
    (forall x1 x2, JMeq x1 x2 -> euttE (k1 x1) (k2 x2)) ->
    eq_notauF' euttE (VisF e1 k1) (VisF e2 k2).
Hint Constructors eq_notauF'.

Lemma eq_notauF_eq_eq_notauF': forall I (euttE : relation I) t s,
  eq_notauF euttE t s <-> eq_notauF' euttE t s.
Proof.
  split; intros EUTT; destruct EUTT; eauto.
  - econstructor; intros; subst; eauto.
  - assert (u1 = u2) by (inv H; eauto).
    subst. apply eq_dep_eq in H. subst. eauto.
Qed.
*)

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
               eq_notauF euttE ot1' ot2')
.
Hint Constructors euttEF.

Definition euttE_ (euttE : itree E R1 -> itree E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  euttEF euttE (observe t1) (observe t2).
Hint Unfold euttE_.

(* Paco takes the greatest fixpoints of monotone relations. *)

Lemma monotone_eq_notauF : forall I J (r r' : I -> J -> Prop) x1 x2
      (IN: eq_notauF r x1 x2)
      (LE: r <2= r'),
    eq_notauF r' x1 x2.
Proof. pmonauto. Qed.
Hint Resolve monotone_eq_notauF.

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

Lemma eq_unalltaus (t1 : itree E R1) (t2 : itree E R2) ot1'
    (FT: unalltausF (observe t1) ot1')
    (EQV: eq_itree RR t1 t2) :
  exists ot2', unalltausF (observe t2) ot2'.
Proof.
  genobs t1 ot1. revert t1 Heqot1 t2 EQV.
  destruct FT as [Huntaus Hnotau].
  induction Huntaus; intros; punfold EQV; unfold_eq_itree; subst.
  - eexists. constructor; eauto. inv EQV; simpl; eauto.
  - inv EQV; simpobs; try inv Heqot1.
    pclearbot. edestruct IHHuntaus as [? []]; eauto.
Qed.

Lemma eq_unalltaus_eqF (t : itree E R1) (s : itree E R2) ot'
    (UNTAUS : unalltausF (observe t) ot')
    (EQV: eq_itree RR t s) :
  exists os', unalltausF (observe s) os' /\ eq_itreeF RR (eq_itree RR) ot' os'.
Proof.
  destruct UNTAUS as [Huntaus Hnotau].
  remember (observe t) as ot. revert s t Heqot EQV.
  induction Huntaus; intros; punfold EQV; unfold_eq_itree.
  - eexists (observe s). split.
    inv EQV; simpobs; eauto.
    subst; eauto.
    eapply eq_itreeF_mono; eauto.
    intros ? ? [| []]; eauto.
  - inv EQV; simpobs; inversion Heqot; subst.
    destruct REL as [| []].
    edestruct IHHuntaus as [? [[]]]; eauto 10.
Qed.

Lemma eq_unalltaus_eq (t : itree E R1) (s : itree E R2) t'
    (UNTAUS : unalltausF (observe t) (observe t'))
    (EQV: eq_itree RR t s) :
  exists s', unalltausF (observe s) (observe s') /\ eq_itree RR t' s'.
Proof.
  eapply eq_unalltaus_eqF in UNTAUS; try eassumption.
  destruct UNTAUS as [os' []]. eexists (go os'); split; eauto.
  pfold. eapply eq_itreeF_mono; eauto.
Qed.

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
Hint Resolve monotone_eq_notauF.
Hint Constructors eq_notauF.
Hint Constructors euttEF.
Hint Resolve monotone_euttE_ : paco.

(** *** [eq_notauF] lemmas *)

Lemma eq_notauF_and {E R1 R2} (RR : R1 -> R2 -> Prop) {I J}
        (euttE1 euttE2 euttE : I -> J -> Prop) :
  (forall t1 t2, euttE1 t1 t2 -> euttE2 t1 t2 -> euttE t1 t2) ->
  forall (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J),
    eq_notauF RR euttE1 ot1 ot2 -> eq_notauF RR euttE2 ot1 ot2 ->
    eq_notauF RR euttE ot1 ot2.
Proof.
  intros ? ? ? [] Hen2; inversion Hen2; auto.
  auto_inj_pair2; subst; auto.
Qed.

Lemma eq_notauF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) {I J}
      (euttE : I -> J -> Prop) :
  forall (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J),
    eq_notauF (flip RR) (flip euttE) ot2 ot1 ->
    eq_notauF RR euttE ot1 ot2.
Proof.
  intros ? ? []; auto.
Qed.

Delimit Scope euttE_scope with euttE.

(** ** Generalized symmetry and transitivity *)

Lemma Symmetric_eq_notauF_ {E R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      {I J} (r1 : I -> J -> Prop) (r2 : J -> I -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (ot1 : itreeF E R1 I) (ot2 : itreeF E R2 J) :
  eq_notauF RR1 r1 ot1 ot2 ->
  eq_notauF RR2 r2 ot2 ot1.
Proof. intros []; auto. Qed.

Lemma Transitive_eq_notauF_ {E R1 R2 R3}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (RR3 : R1 -> R3 -> Prop)
      {I J K} (r1 : I -> J -> Prop) (r2 : J -> K -> Prop)
      (r3 : I -> K -> Prop)
      (TRANS_RR : forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR3 r1 r3)
      (TRANS_r : forall i j k, r1 i j -> r2 j k -> r3 i k)
      (ot1 : itreeF E R1 I) ot2 ot3 :
  eq_notauF RR1 r1 ot1 ot2 ->
  eq_notauF RR2 r2 ot2 ot3 ->
  eq_notauF RR3 r3 ot1 ot3.
Proof.
  intros [] I2; inversion I2; eauto.
  auto_inj_pair2; subst; eauto.
Qed.

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

(* Reflexivity of [eq_notauF], modulo a few assumptions. *)
Lemma Reflexive_eq_notauF `{Reflexive _ RR} I (eq_ : I -> I -> Prop) :
  Reflexive eq_ ->
  forall (ot : itreeF E R I), notauF ot -> eq_notauF RR eq_ ot ot.
Proof.
  intros. destruct ot; try contradiction; econstructor; intros; subst; eauto.
Qed.

Global Instance Symmetric_eq_notauF `{Symmetric _ RR} I (eq_ : I -> I -> Prop) :
  Symmetric eq_ -> Symmetric (@eq_notauF E _ _ RR _ _ eq_).
Proof.
  repeat intro. eapply Symmetric_eq_notauF_; eauto.
Qed.

Global Instance Transitive_eq_notauF `{Transitive _ RR} I (eq_ : I -> I -> Prop) :
  Transitive eq_ -> Transitive (@eq_notauF E _ _ RR _ _ eq_).
Proof.
  repeat intro. eapply Transitive_eq_notauF_; eauto.
Qed.

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

Global Instance eq_itree_notauF :
  Proper (going (@eq_itree E R _ eq) ==> flip impl) notauF.
Proof.
  intros ? ? [] ?; punfold H. inv H; simpl in *; subst; eauto.
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

Lemma eq_itree_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eq_itree RR (k1 u) (k2 u)) ->
  eq_itree RR (Vis e k1) (Vis e k2).
Proof.
  intros; pfold; constructor; left. apply H.
Qed.

Lemma eq_itree_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 -> @eq_itree E _ _ RR (Ret r1) (Ret r2).
Proof.
  intros; pfold; eauto; constructor; auto.
Qed.

(* Lemmas about [bind]. *)

Lemma untaus_bind {E S R} : forall t t' (k: S -> itree E R)
      (UNTAUS: untausF (observe t) (observe t')),
  untausF (observe (ITree.bind t k)) (observe (ITree.bind t' k)).
Proof.
  intros. genobs t ot; genobs t' ot'. revert t Heqot t' Heqot'.
  induction UNTAUS; intros; subst.
  - rewrite !unfold_bind; simpobs; eauto.
  - rewrite unfold_bind. simpobs. cbn. eauto.
Qed.

Lemma untaus_bindF {E S R} : forall t t' (k: S -> itree E R)
      (UNTAUS: untausF (observe t) t'),
  untausF (observe (ITree.bind t k)) (observe (ITree.bind (go t') k)).
Proof.
  intros; eapply untaus_bind; eauto.
Qed.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (ITree.bind t f) -> finite_taus t.
Proof.
  intros [tf' [TAUS PROP]].
  genobs (ITree.bind t f) obtf. move TAUS at top. revert_until TAUS.
  induction TAUS; intros; subst.
  - rewrite unfold_bind in PROP.
    genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
  - genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
    rewrite unfold_bind in Heqobtf. simpobs. inv Heqobtf. unfold_bind.
    eapply finite_taus_tau; eauto.
Qed.

Lemma finite_taus_bind {E R S}
      (t : itree E R) (f : R -> itree E S)
      (FINt: finite_tausF (observe t))
      (FINk: forall v, finite_tausF (observe (f v))):
  finite_tausF (observe (ITree.bind t f)).
Proof.
  rewrite unfold_bind.
  genobs t ot. clear Heqot t.
  destruct FINt as [ot' [UNT NOTAU]].
  induction UNT; subst.
  - destruct ot0; inv NOTAU; simpl; eauto 7.
  - apply finite_taus_tau. eauto.
Qed.

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
