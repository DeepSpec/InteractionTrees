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
   - relate to Eq.Eq.eq_itree
   - prove monad laws (see [eutt_bind_bind_fail])
   - make [eutt] easier to work with ([eutt_bind] is already a mess)
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     Logic.JMeq Logic.EqdepFacts.

From ITree Require Import paco2_upto Core Eq.Eq.

Set Bullet Behavior "Strict Subproofs".

(* [notau t] holds when [t] does not start with a [Tau]. *)
Definition notauF E R (t : itreeF E R (itree E R)) : Prop :=
  match t with
  | TauF _ => False
  | _ => True
  end.
Arguments notauF [E] [R] t.

Notation notau t := (notauF (observe t)).

Section EUTT.

Context {E : Type -> Type} {R : Type}.

(* note(LY): maybe we should use equalities instead of type indices.
   In the transitivity proof at least, it is a bit annoying to
   rewrite the goal from
   [eutt_0F eutt (t1.(observe)) (t2.(observe))] to
   [eutt_0F eutt (RetF r) (RetF r)]. *)

(* Equivalence between visible steps of computation (i.e., [Vis] or
   [Ret], parameterized by a relation [eutt] between continuations
   in the [Vis] case. *)
Variant euttF0 (eutt : relation (itree E R))
: relation (itreeF E R (itree E R)) :=
| Eutt_ret : forall r, euttF0 eutt (RetF r) (RetF r)
| Eutt_vis : forall u (e : E u) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    euttF0 eutt (VisF e k1) (VisF e k2).
Hint Constructors euttF0.

Variant euttF0' (eutt : relation (itree E R))
: relation (itreeF E R (itree E R)) :=
| Eutt_ret' : forall r, euttF0' eutt (RetF r) (RetF r)
| Eutt_vis' : forall {u1 u2} (e1 : E u1) (e2 : E u2) k1 k2,
    eq_dep _ E _ e1 _ e2 ->
    (forall x1 x2, JMeq x1 x2 -> eutt (k1 x1) (k2 x2)) ->
    euttF0' eutt (VisF e1 k1) (VisF e2 k2).
Hint Constructors euttF0'.

Lemma euttF0_eq_euttF0': forall eutt t s,
  euttF0 eutt t s <-> euttF0' eutt t s.
Proof.
  split; intros EUTT; destruct EUTT; eauto.
  - econstructor; intros; subst; eauto.
  - assert (u1 = u2) by (inv H; eauto).
    subst. apply eq_dep_eq in H. subst. eauto.
Qed.

(* [untaus t' t] holds when [t = Tau (... Tau t' ...)]:
   [t] steps to [t'] by "peeling off" a finite number of [Tau].
   "Peel off" means to remove only taus at the root of the tree,
   not any behind a [Vis] step). *)
Inductive untaus (all: bool) : nat -> relation (itreeF E R _) :=
| NoTau ot0 (PROP: if all then notauF ot0 else True) : untaus all 0 ot0 ot0
| OneTau n ot t' ot0 (OBS: TauF t' = ot) (TAUS: untaus all n (observe t') ot0): untaus all (S n) ot ot0
.
Hint Constructors untaus.

Notation unalltaus := (untaus true).

(* [finite_taus t] holds when [t] has a finite number of taus
   to peel. *)
Definition finite_taus ot : Prop := exists n t', unalltaus n ot (observe t').
Hint Unfold finite_taus.

(* [eutt_ eutt t1 t2] means that, if [t1] or [t2] ever takes a
   visible step ([Vis] or [Ret]), then the other takes the same
   step, and the subsequent continuations (in the [Vis] case) are
   related by [eutt]. In particular, [(t1 = spin)%eq_itree] if
   and only if [(t2 = spin)%eq_itree]. Note also that in that
   case, the parameter [eutt] is irrelevant.

   This is the relation we will take a fixpoint of. *)
Inductive euttF (eutt : relation (itree E R)) (t1 t2: itree E R) : Prop :=
| euttF_ (FIN: finite_taus (observe t1) <-> finite_taus (observe t2))
         (EQV: forall n m t1' t2'
                  (UNTAUS1: unalltaus n (observe t1) (observe t1'))
                  (UNTAUS2: unalltaus m (observe t2) (observe t2')),
               euttF0 eutt (observe t1') (observe t2'))
.
Hint Constructors euttF.

(* Paco takes the greatest fixpoints of monotone relations. *)

Lemma monotone_euttF0: forall r r' x1 x2
      (IN: euttF0 r x1 x2)
      (LE: r <2= r'),
    euttF0 r' x1 x2.
Proof. pmonauto. Qed.
Hint Resolve monotone_euttF0.

(* [eutt_] is monotone. *)
Lemma monotone_euttF : monotone2 euttF.
Proof. pmonauto. Qed.
Hint Resolve monotone_euttF : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : relation (itree E R) := paco2 euttF bot2.

Global Arguments eutt t1%itree t2%itree.

(* note: overlaps with [not] *)
Infix "~~" := eutt (at level 70).

(* Lemmas about the auxiliary relations. *)

(* Many have a name [X_Y] to represent an implication
   [X _ -> Y _] (possibly with more arguments on either side). *)

Lemma untaus_all  n ot ot' :
  untaus false n ot ot' -> notauF ot' -> unalltaus n ot ot'.
Proof. induction 1; eauto. Qed.

Lemma unalltaus_notau n ot ot' : unalltaus n ot ot' -> notauF ot'.
Proof. intros. induction H; eauto. Qed.

Lemma notau_tau ot (t0: itree E R)
  (NOTAU : notauF ot)
  (OBS: TauF t0 = ot): False.
Proof. subst. auto. Qed.
Hint Resolve notau_tau.

Lemma notau_ret: forall (ot: itreeF _ _ (itree E R)) r (OBS: RetF r = ot), notauF ot.
Proof. intros. subst. red. eauto. Qed.
Hint Resolve notau_ret.

Lemma notau_vis u: forall ot (e: E u) k (OBS: VisF e k = ot), @notauF E R ot.
Proof. intros. subst. red. eauto. Qed.
Hint Resolve notau_vis.

(* If [t] does not start with [Tau], removing all [Tau] does
   nothing. Can be thought of as [notau_unalltaus] composed with
   [unalltaus_injective] (below). *)
Lemma unalltaus_notau_id n ot ot' :
  unalltaus n ot ot' -> notauF ot -> ot = ot'.
Proof.
  intros. destruct H; eauto. exfalso; eauto.
Qed.

(* There is only one way to peel off all taus. *)
Lemma unalltaus_injective : forall n m ot ot1 ot2,
    unalltaus n ot ot1 -> unalltaus m ot ot2 -> ot1 = ot2.
Proof.
  intros. revert m ot2 H0.
  induction H; intros; eauto using unalltaus_notau_id.
  inv H0.
  - exfalso. eauto.
  - inv OBS0. eauto.
Qed.

(* Adding a [Tau] to [t1] then peeling them all off produces
   the same result as peeling them all off from [t1]. *)
Lemma unalltaus_tau n t ot1 ot2
    (OBS: TauF t = ot1)
    (TAUS: unalltaus n ot1 ot2):
  unalltaus (pred n) (observe t) ot2.
Proof.
  inv TAUS.
  - exfalso; eauto.
  - inv OBS0. eauto.
Qed.

(* If [t] does not start with [Tau], then it starts with finitely
   many [Tau]. *)
Lemma notau_finite_taus ot : notauF ot -> finite_taus ot.
Proof. eexists 0. eexists (go _); cbn. eauto. Qed.

(* [Vis] and [Ret] start with no taus, of course. *)
Lemma finite_taus_ret ot (r : R) (OBS: RetF r = ot) : finite_taus ot.
Proof. eexists 0. eexists (go _); cbn. eauto. Qed.

Lemma finite_taus_vis {u} ot (e : E u) (k : u -> itree E R) (OBS: VisF e k = ot):
  finite_taus ot.
Proof. eexists 0. eexists (go _); cbn. eauto. Qed.

(* [finite_taus] is preserved by removing or adding one [Tau]. *)
Lemma finite_taus_tau ot t'
      (OBS: TauF t' = ot):
  finite_taus ot <-> finite_taus (observe t').
Proof.
  subst; split; intros TAUS; destruct TAUS, H; do 2 eexists; eauto using unalltaus_tau.
Qed.

(* (* [finite_taus] is preserved by removing or adding any finite *)
(*    number of [Tau]. *) *)
Lemma untaus_finite_taus P n ot ot':
    untaus P n ot ot' -> (finite_taus ot <-> finite_taus ot').
Proof.
  induction 1; intros; subst.
  - reflexivity.
  - erewrite finite_taus_tau; eauto.
Qed.

(**)

Lemma eq_unalltaus :
  forall n (t1 t2 : itree E R) ot1'
    (FT: unalltaus n (observe t1) ot1')
    (EQV: t1 ≅ t2),
  exists t2', unalltaus n (observe t2) (observe t2').
Proof.
  intros. genobs t1 ot1. revert t1 Heqot1 t2 EQV.
  induction FT; intros; punfold EQV; unfold_eq_itree; subst.
  - eexists. econstructor. inv EQV; simpl; eauto.
  - inv EQV; simpobs; try inv Heqot1.
    pclearbot. edestruct IHFT; eauto.
Qed.

Lemma eq_unalltaus_eq :
  forall n (t s : itree E R) t'
    (UNTAUS : unalltaus n (observe t) (observe t'))
    (EQV: t ≅ s),
  exists s', unalltaus n (observe s) (observe s') /\ t' ≅ s'.
Proof.
  intros. genobs t ot; genobs t' ot'. revert t Heqot t' Heqot' s EQV.
  induction UNTAUS; intros; punfold EQV; unfold_eq_itree.
  - eexists. inv EQV; simpobs; split; eauto; pfold; red; simpobs; eauto.
  - inv EQV; simpobs; inv Heqot.
    pclearbot. edestruct IHUNTAUS as [s' [? ?]]; eauto.
Qed.

(* Reflexivity of [eutt_0], modulo a few assumptions. *)
Lemma reflexive_euttF0 eutt ot :
  Reflexive eutt -> notauF ot -> euttF0 eutt ot ot.
Proof.
  intros. destruct ot; try contradiction; econstructor; intros; subst; eauto.
Qed.

Lemma euttF_tau r t1 t2 t1' t2'
    (OBS1: TauF t1' = observe t1)
    (OBS2: TauF t2' = observe t2)
    (REL: euttF r t1' t2'):
  euttF r t1 t2.
Proof.
  intros. destruct REL. econstructor.
  - do 2 (symmetry; rewrite finite_taus_tau; eauto).
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Lemma euttF_vis {u} (r : relation (itree E R)) t1 t2 (e : _ u) k1 k2
    (OBS1: VisF e k1 = observe t1)
    (OBS2: VisF e k2 = observe t2)
    (REL: forall x, r (k1 x) (k2 x)):
  euttF r t1 t2.
Proof.
  intros. econstructor.
  - split; intros; eapply notau_finite_taus; eauto.
  - intros.
    apply unalltaus_notau_id in UNTAUS1; eauto.
    apply unalltaus_notau_id in UNTAUS2; eauto.
    simpobs. eauto.
Qed.

(**)

Lemma Reflexive_euttF (r : relation (itree E R)) :
  Reflexive r -> Reflexive (euttF r).
Proof.
  split.
  - reflexivity.
  - intros.
    erewrite (unalltaus_injective _ _ _ _ _ UNTAUS1 UNTAUS2).
    apply reflexive_euttF0; eauto using unalltaus_notau.
Qed.

Lemma eutt_refl r x : paco2 euttF r x x.
Proof.
  revert x. pcofix CIH.
  intros. pfold. apply Reflexive_euttF. eauto.
Qed.

(* [eutt] is an equivalence relation. *)
Global Instance Reflexive_eutt: (Reflexive eutt).
Proof.
  repeat intro. apply eutt_refl.
Qed.

Global Instance Symmetric_eutt
: Symmetric eutt.
Proof.
  pcofix Symmetric_eutt.
  intros t1 t2 H12.
  punfold H12.
  pfold.
  destruct H12 as [I12 H12].
  split.
  - symmetry; assumption.
  - intros. hexploit H12; eauto. intros.
    inv H; eauto.
    econstructor. intros. specialize (H2 x). pclearbot. eauto.
Qed.

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  pcofix Transitive_eutt.
  intros t1 t2 t3 H12 H23.
  punfold H12.
  punfold H23.
  pfold.
  destruct H12 as [I12 H12].
  destruct H23 as [I23 H23].
  split.
  - etransitivity; eauto.
  - intros n m t1' t3' H1 H3.
    destruct I12 as [I1 I2].
    destruct I1 as [n2' [t2' TAUS2]]; eauto.
    hexploit H12; eauto. intros REL1.
    hexploit H23; eauto. intros REL2.
    genobs t1' ot1'. genobs t2' ot2'. genobs t3' ot3'.
    dependent destruction REL1; dependent destruction REL2; eauto.
    econstructor. intros.
    specialize (H x); specialize (H0 x). pclearbot. eauto.
Qed.

(**)

(* [eutt] is preserved by removing one [Tau]. *)
Lemma tauF_eutt (t t': itree E R) (OBS: TauF t' = observe t): t ~~ t'.
Proof.
  pfold. split.
  - apply finite_taus_tau; auto.
  - intros n m t1' t2' H1 H2.
    eapply unalltaus_tau in H1; eauto.
    assert (X := unalltaus_injective _ _ _ _ _ H1 H2); simpobs.
    apply reflexive_euttF0; eauto using unalltaus_notau.
    left. apply Reflexive_eutt.
Qed.

Lemma tau_eutt (t: itree E R) : Tau t ~~ t.
Proof.
  eapply tauF_eutt. eauto.
Qed.

(* [eutt] is preserved by removing all [Tau]. *)
Lemma untaus_eutt P n (t t' : itree E R) : untaus P n (observe t) (observe t') -> t ~~ t'.
Proof.
  intros H.
  pfold. split.
  - eapply untaus_finite_taus; eauto.
  - induction H; intros.
    + rewrite (unalltaus_injective _ _ _ _ _ UNTAUS1 UNTAUS2).
      apply reflexive_euttF0; eauto using unalltaus_notau.
      left; apply Reflexive_eutt.
    + eapply unalltaus_tau in UNTAUS1; eauto.
Qed.

End EUTT.

Notation unalltaus := (untaus true).

Hint Constructors euttF0.
Hint Constructors euttF0'.
Hint Constructors untaus.
Hint Unfold finite_taus.
Hint Constructors euttF.
Hint Resolve monotone_euttF : paco.
Hint Resolve notau_ret.
Hint Resolve notau_vis.
Hint Resolve notau_tau.

Delimit Scope eutt_scope with eutt.

Infix "~~" := eutt (at level 70).

(* We can now rewrite with [eutt] equalities. *)
Instance Equivalence_eutt E R : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

Instance subrelation_eq_eutt {E R} : subrelation (@eq_itree E R) eutt.
Proof.
  pcofix CIH. intros.
  pfold. econstructor.
  { split; [|symmetry in H0]; intros; destruct H as [n [? ?]]; eauto using eq_unalltaus. }

  intros. eapply eq_unalltaus_eq in H0; eauto. destruct H0 as [s' [UNTAUS' EQV']].
  hexploit @unalltaus_injective; [apply UNTAUS' | apply UNTAUS2 | intro X]; subst.
  punfold EQV'. unfold_eq_itree. inv EQV'; simpobs; eauto.
  - eapply unalltaus_notau in UNTAUS1. simpobs. contradiction.
  - econstructor. intros. specialize (REL x0). pclearbot. eauto.
Qed.

Instance subrelation_go_sim_eq_eutt {E R} : subrelation (go_sim (@eq_itree E R)) (go_sim (@eutt E R)).
Proof.
  repeat intro. red. red in H. rewrite H. reflexivity.
Qed.

Instance eutt_go {E R} :
  Proper (go_sim (@eutt E R) ==> @eutt E R) (@go E R).
Proof.
  repeat intro. eauto.
Qed.

Instance eutt_observe {E R} :
  Proper (@eutt E R ==> go_sim (@eutt E R)) (@observe E R).
Proof.
  repeat intro. punfold H. pfold. destruct H. econstructor; eauto.
Qed.

Instance eutt_tauF {E R} :
  Proper (@eutt E R ==> go_sim (@eutt E R)) (@TauF E R _).
Proof.
  repeat intro. pfold. punfold H.
  destruct H. econstructor.
  - split; intros.
    + rewrite finite_taus_tau, <-FIN, <-finite_taus_tau; eauto.
    + rewrite finite_taus_tau, FIN, <-finite_taus_tau; eauto.
  - intros. eapply EQV; eapply unalltaus_tau; eauto.
Qed.

Instance eutt_VisF {E R u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> go_sim (@eutt E R)) (VisF e).
Proof.
  repeat intro. red in H. pfold. econstructor.
  - repeat econstructor.
  - intros. dependent destruction UNTAUS1. dependent destruction UNTAUS2. simpobs.
    econstructor. intros. left. apply H.
Qed.

Instance eq_itree_notauF {E R} :
  Proper (go_sim (@eq_itree E R) ==> flip impl) (@notauF E R).
Proof.
  repeat intro. punfold H. inv H; simpl in *; subst; eauto.
Qed.

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Instance eutt_finite_taus {E R} :
  Proper (go_sim (@eutt E R) ==> flip impl) (@finite_taus E R).
Proof.
  repeat intro. punfold H. eapply H. eauto.
Qed.

(* Lemmas about [bind]. *)

Lemma untaus_bind P {E S R} : forall n t t' (k: S -> itree E R)
      (UNTAUS: untaus P n (observe t) (observe t')),
  untaus false n (observe (ITree.bind t k)) (observe (ITree.bind t' k)).
Proof.
  intros. genobs t ot; genobs t' ot'. revert t Heqot t' Heqot'.
  induction UNTAUS; intros; subst.
  - rewrite !bind_unfold; simpobs; eauto.
  - rewrite bind_unfold. simpobs. cbn. eauto.
Qed.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (observe (ITree.bind t f)) -> finite_taus (observe t).
Proof.
  intros [n [tf' TAUS]].
  genobs (ITree.bind t f) obtf. genobs tf' otf'. move TAUS at top. revert_until TAUS.
  induction TAUS; intros; subst.
  - rewrite bind_unfold in PROP, Heqotf'.
    genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
    contradiction.
  - genobs t ot; destruct ot; eauto using finite_taus_ret, finite_taus_vis.
    rewrite bind_unfold in Heqobtf. simpobs. inv Heqobtf. unfold_bind.
    eapply finite_taus_tau; eauto.
Qed.

Lemma untaus_eq_idx P E R: forall n m (ot1 ot2: itreeF E R _),
    n = m -> untaus P n ot1 ot2 -> untaus P m ot1 ot2.
Proof. intros; subst; eauto. Qed.

Lemma untaus_untaus P Q E R: forall n m (ot1 ot2 ot3: itreeF E R _),
    untaus P n ot1 ot2 -> untaus Q m ot2 ot3 -> untaus Q (n+m) ot1 ot3.
Proof.
  intros n m t1 t2 t3. induction 1; simpl; eauto.
Qed.

Lemma untaus_unalltus_rev all E R: forall n m (ot1 ot2 ot3: itreeF E R _),
    untaus all n ot1 ot2 -> unalltaus m ot1 ot3 -> unalltaus (m-n) ot2 ot3.
Proof.
  intros. revert m ot3 H0.
  induction H; intros.
  - eauto using untaus_eq_idx with arith.
  - inversion H0; subst.
    + exfalso. eauto.
    + inv OBS0. eauto.
Qed.

Lemma eutt_strengthen {E R}:
  forall r (t1 t2: itree E R)
     (FIN: finite_taus (observe t1) <-> finite_taus (observe t2))
     (EQV: forall n1 n2 m1 m2 t1' t2'
              (UNT1: unalltaus m1 (observe t1) (observe t1'))
              (UNT2: unalltaus m2 (observe t2) (observe t2'))
              (LEn: m1 < n1)
              (LEm: m2 < n2),
         paco2 (euttF ∘ gres2 euttF) r t1' t2'),
    paco2 (euttF ∘ gres2 euttF) r t1 t2.
Proof.
  intros. pfold. econstructor; eauto.
  intros. hexploit (EQV (S (max n m))); eauto with arith. intro EQV'.
  punfold EQV'. destruct EQV'.
  eauto 7 using unalltaus_notau.
Qed.

Inductive eutt_trans_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| eutt_pre_clo_intro (t1 t2 t3 t4: itree E R)
      (EQVl: t1 ~~ t2)
      (EQVr: t4 ~~ t3)
      (REL: r t2 t3)
  : eutt_trans_clo r t1 t4
.
Hint Constructors eutt_trans_clo.

Lemma eutt_clo_trans E R: weak_respectful2 (@euttF E R) eutt_trans_clo.
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
  genobs t1' ot1'. genobs t2'' ot2''. genobs t2' ot2'. genobs t2''' ot2'''.
  dependent destruction EUTT1; dependent destruction EUTT2; dependent destruction EUTT3; eauto.
  econstructor. intros. specialize (H x). specialize (H0 x). pclearbot. eauto using rclo2.
Qed.

Inductive eutt_bind_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| eutt_bind_clo_intro U (t1 t2: itree E U) k1 k2
      (EQV: t1 ~~ t2)
      (REL: forall v, r (k1 v) (k2 v))
  : eutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eutt_bind_clo.

Lemma eutt_clo_bind E R: weak_respectful2 (@euttF E R) eutt_bind_clo.
Proof.
  econstructor; [pmonauto|].
  intros. destruct PR. punfold EQV. destruct EQV. split.
  - split; intros.
    + assert (FT1 := H). apply finite_taus_bind_fst in FT1.
      assert (FT2 := FT1). apply FIN in FT2.
      destruct FT1 as [n [a FT1]], FT2 as [m [b FT2]].
      hexploit EQV; eauto. intros EQV'.
      edestruct @untaus_finite_taus; [eapply untaus_bind, FT1 | apply H0 in H].
      eapply untaus_finite_taus; eauto using untaus_bind.
      rewrite bind_unfold in H |- *.
      inv EQV'; simpobs; cbn.
      * edestruct GF; eauto. apply FIN0. eauto.
      * eauto using finite_taus_vis.
    + assert (FT1 := H). apply finite_taus_bind_fst in FT1.
      assert (FT2 := FT1). apply FIN in FT2.
      destruct FT1 as [n [a FT1]], FT2 as [m [b FT2]].
      hexploit EQV; eauto. intros EQV'.
      edestruct @untaus_finite_taus; [eapply untaus_bind, FT1 | apply H0 in H].
      eapply untaus_finite_taus; eauto using untaus_bind.
      rewrite bind_unfold in H |- *.
      inv EQV'; simpobs.
      * edestruct GF; eauto. apply FIN0. eauto.
      * cbn. eauto using finite_taus_vis.
  - intros.
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS1|]. intros [n' [a FT1]].
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS2|]. intros [m' [b FT2]].
    hexploit @untaus_bind; [apply FT1|]. intros UT1.
    hexploit @untaus_bind; [apply FT2|]. intros UT2.
    specialize (EQV _ _ _ _ FT1 FT2).
    hexploit untaus_unalltus_rev; [apply UT1| |]; eauto. intros UAT1.
    hexploit untaus_unalltus_rev; [apply UT2| |]; eauto. intros UAT2.
    inv EQV.
    + rewrite bind_unfold in UAT1, UAT2. simpobs. cbn in *.
      eapply GF in REL. destruct REL.
      eapply monotone_euttF0; eauto using rclo2.
    + rewrite bind_unfold in UAT1, UAT2. simpobs. cbn in *.
      dependent destruction UAT1. dependent destruction UAT2. simpobs.
      econstructor. intros. specialize (H1 x3). pclearbot. fold_bind. eauto using rclo2.
Qed.

(* [eutt] is a congruence wrt. [bind] *)

Instance eutt_bind {E R S} :
  Proper (@eutt E R ==>
          pointwise_relation _ eutt ==>
          @eutt E S) ITree.bind.
Proof.
  repeat intro. pupto2_init.
  pupto2 (eutt_clo_bind E S). econstructor; eauto.
  intros. pupto2_final. apply H0.
Qed.

Instance eutt_paco {E R} r:
  Proper (@eutt E R ==> @eutt E R ==> flip impl)
         (paco2 (euttF ∘ gres2 euttF) r).
Proof.
  repeat intro. pupto2 (eutt_clo_trans E R). eauto.
Qed.

Instance eutt_gres {E R} r:
  Proper (@eutt E R ==> @eutt E R ==> flip impl)
         (gres2 euttF (upaco2 (euttF ∘ gres2 euttF) r)).
Proof.
  repeat intro. pupto2 (eutt_clo_trans E R). eauto.
Qed.

Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> @eutt E R ==> @eutt E S) ITree.map.
Proof.
Admitted.

Instance eutt_forever {E R S} :
  Proper (@eutt E R ==> @eutt E S) ITree.forever.
Proof.
Admitted.
Instance eutt_when {E} (b : bool) :
  Proper (@eutt E unit ==> @eutt E unit) (ITree.when b).
Proof.
Admitted.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt (ITree.map g (ITree.map f t))
       (ITree.map (fun x => g (f x)) t).
Proof.
  rewrite map_map. reflexivity.
Qed.

Notation itree' E R := (itreeF E R (itree E R)).

Definition observing {E R}
           (f : itree' E R -> itree' E R -> Prop)
           (x y : itree E R) :=
  f x.(observe) y.(observe).

Inductive euttF1' {E R} (r : itree E R -> itree E R -> Prop) :
  itree' E R -> itree' E R -> Prop :=
| euttF1_Tau_L : forall t1 t2,
    euttF1' r t1.(observe) t2 ->
    euttF1' r (TauF t1) t2
| euttF1_Tau_R : forall t1 t2,
    euttF1' r t1 t2.(observe) ->
    euttF1' r t1 (TauF t2)
| euttF1_euttF0 : forall t1 t2,
    euttF0 r t1 t2 ->
    euttF1' r t1 t2
.

Definition euttF1 {E R} (r : relation (itree E R)) :
  relation (itree E R) := observing (euttF1' r).

Lemma euttF1_euttF {E R} (r : relation (itree E R)) :
  forall t1 t2,
    euttF1 r t1 t2 -> euttF r t1 t2.
Proof.
Admitted.
