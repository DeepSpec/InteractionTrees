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

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     Logic.JMeq Logic.EqdepFacts.

Require Import Paco.paco.

From ITree Require Import paco2_respectful Core Eq.Eq.

Set Bullet Behavior "Strict Subproofs".

Lemma iff_or_and {P Q : Prop} :
  P <-> Q -> P \/ Q -> P /\ Q.
Proof. firstorder. Qed.


(* [notau t] holds when [t] does not start with a [Tau]. *)
Definition notau E R (t : itree E R) : Prop :=
  match t.(observe) with
  | TauF _ => False
  | _ => True
  end.
Arguments notau [E] [R] t.

Definition anyitree E R (t : itree E R) : Prop := True.
Arguments anyitree [E] [R] t.
Hint Unfold anyitree.

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
: relation (itree E R) :=
| Eutt_ret : forall r, euttF0 eutt (Ret r) (Ret r)
| Eutt_vis : forall u (e : E u) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    euttF0 eutt (Vis e k1) (Vis e k2).
Hint Constructors euttF0.

Variant euttF0' (eutt : relation (itree E R))
: relation (itree E R) :=
| Eutt_ret' : forall r, euttF0' eutt (Ret r) (Ret r)
| Eutt_vis' : forall {u1 u2} (e1 : E u1) (e2 : E u2) k1 k2,
    eq_dep _ E _ e1 _ e2 ->
    (forall x1 x2, JMeq x1 x2 -> eutt (k1 x1) (k2 x2)) ->
    euttF0' eutt (Vis e1 k1) (Vis e2 k2).
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
Inductive untaus (P: forall E R, itree E R -> Prop) : nat -> relation (itree E R) :=
| NoTau t (PROP: P _ _ t) : untaus P 0 t t
| OneTau n t t' (TAUS: untaus P n t t') : untaus P (S n) (Tau t) t'
.
Hint Constructors untaus.

Notation unalltaus := (untaus notau).

(* [finite_taus t] holds when [t] has a finite number of taus
   to peel. *)
Definition finite_taus t : Prop := exists n t', unalltaus n t t'.
Hint Unfold finite_taus.

(* [eutt_ eutt t1 t2] means that, if [t1] or [t2] ever takes a
   visible step ([Vis] or [Ret]), then the other takes the same
   step, and the subsequent continuations (in the [Vis] case) are
   related by [eutt]. In particular, [(t1 = spin)%eq_itree] if
   and only if [(t2 = spin)%eq_itree]. Note also that in that
   case, the parameter [eutt] is irrelevant.

   This is the relation we will take a fixpoint of. *)
Inductive euttF (eutt : relation (itree E R)) (t1 t2: itree E R) : Prop :=
| euttF_ (FIN: finite_taus t1 <-> finite_taus t2)
         (EQV: forall n m t1' t2'
                  (UNTAUS1: unalltaus n t1 t1')
                  (UNTAUS2: unalltaus m t2 t2'),
               euttF0 eutt t1' t2')
.
Hint Constructors euttF.

(* Paco takes the greatest fixpoints of monotone relations. *)

(* [eutt_0] is monotone: if a binary relation [eutt] implies [eutt'],
   then [eutt_0 eutt] implies [eutt_0 eutt']. *)
Lemma monotone_euttF0 : monotone2 euttF0.
Proof.
  pmonauto.
Qed.
Hint Resolve monotone_euttF0.

(* [eutt_] is monotone. *)
Lemma monotone_euttF : monotone2 euttF.
Proof.
  pmonauto.
Qed.
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


Lemma untaus_change_prop Q P n (t t' : itree E R) :
  untaus P n t t' -> (Q _ _ t':Prop) -> untaus Q n t t'.
Proof. induction 1; eauto. Qed.

Lemma untaus_prop P n (t t' : itree E R) : untaus P n t t' -> P _ _ t'.
Proof. intros. induction H; eauto. Qed.

(* If [t] does not start with [Tau], removing all [Tau] does
   nothing. Can be thought of as [notau_unalltaus] composed with
   [unalltaus_injective] (below). *)
Lemma unalltaus_notau_id n t t' :
  unalltaus n t t' -> notau t -> t' = t.
Proof.
  intros. destruct H; eauto. contradiction.
Qed.

(* There is only one way to peel off all taus. *)
Lemma unalltaus_injective : forall n m t t1 t2,
    unalltaus n t t1 -> unalltaus m t t2 -> t2 = t1.
Proof.
  intros. revert m t2 H0.
  induction H; intros; eauto using unalltaus_notau_id.
  inv H0; eauto. contradiction.
Qed.

(* Adding a [Tau] to [t1] then peeling them all off produces
   the same result as peeling them all off from [t1]. *)
Lemma unalltaus_tau n t1 t2 :
  unalltaus n (Tau t1) t2 -> unalltaus (pred n) t1 t2.
Proof.
  intros. inv H; eauto. contradiction.
Qed.

(* If [t] does not start with [Tau], then it starts with finitely
   many [Tau]. *)
Lemma notau_finite_taus (t : itree E R) : notau t -> finite_taus t.
Proof. eexists 0. eexists. eauto. Qed.

Lemma notau_ret: forall r, notau (Ret r: itree E R).
Proof. intros. cbn. eauto. Qed.
Hint Resolve notau_ret.

Lemma notau_vis u: forall (e: E u) k, notau (Vis e k: itree E R).
Proof. intros. cbn. eauto. Qed.
Hint Resolve notau_vis.

(* [Vis] and [Ret] start with no taus, of course. *)
Lemma finite_taus_ret (r : R) : finite_taus (Ret r).
Proof. eexists 0. eauto. Qed.

Lemma finite_taus_vis {u} (e : E u) (k : u -> itree E R) :
  finite_taus (Vis e k).
Proof. eexists 0. eauto. Qed.

(* [finite_taus] is preserved by removing or adding one [Tau]. *)
Lemma finite_taus_tau (t : itree E R) :
  finite_taus (Tau t) <-> finite_taus t.
Proof.
  split; intros TAUS; destruct TAUS, H; red; eexists; eauto using unalltaus_tau.
Qed.

(* (* [finite_taus] is preserved by removing or adding any finite *)
(*    number of [Tau]. *) *)
Lemma untaus_finite_taus P n (t t' : itree E R) :
    untaus P n t t' -> (finite_taus t <-> finite_taus t').
Proof.
  induction 1.
  - reflexivity.
  - erewrite finite_taus_tau; eassumption.
Qed.

(**)

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Lemma finite_taus_eutt (t1 t2 : itree E R) :
  t1 ~~ t2 -> finite_taus t1 -> finite_taus t2.
Proof. intros. punfold H. apply H. eauto. Qed.

Lemma eq_unalltaus :
  forall n (t1 t2 t1' : itree E R)
    (FT: unalltaus n t1 t1')
    (EQV: t1 ≅ t2),
  exists t2', unalltaus n t2 t2'.
Proof.
  intros. revert t2 EQV.
  induction FT; intros; punfold EQV; unfold_eq_itree.
  - absobs t ot. absobs t2 ot2. inv EQV; cbn; eauto.
  - simpl in EQV. absobs t2 ot2. inv EQV. pclearbot.
    edestruct IHFT; eauto.
Qed.

Lemma eq_unalltaus_eq :
  forall n (t t' s : itree E R)
    (UNTAUS : unalltaus n t t')
    (EQV: t ≅ s),
  exists s', unalltaus n s s' /\ t' ≅ s'.
Proof.
  intros. revert s EQV.
  induction UNTAUS; intros; punfold EQV; unfold_eq_itree.
  - exists s. split; eauto.
    absobs s os. absobs t ot. inv EQV; eauto.
  - absobs s os. inv EQV. pclearbot.
    edestruct IHUNTAUS as [s' [? ?]]; eauto.
Qed.


(* If [t1] and [t2] are equivalent, and one starts with finitely many
   taus, then both do, and the peeled off [t1'] and [t2'] take
   the same visible step. *)
Lemma eutt_unalltaus_1 (t1 t2 : itree E R) :
  t1 ~~ t2 -> finite_taus t1 ->
  exists n m t1' t2',
    unalltaus n t1 t1' /\ unalltaus m t2 t2' /\ euttF0 eutt t1' t2'.
Proof.
  intros Heutt Ht1. punfold Heutt.
  destruct Heutt as [Hfinite Heutt0].
  assert (Ht2 : finite_taus t2).
  { apply Hfinite; auto. }
  destruct Ht1 as [n [t1' Ht1']].
  destruct Ht2 as [m [t2' Ht2']].
  exists n, m, t1', t2'; repeat split; eauto.
  eapply monotone_euttF0; eauto.
  intros. pclearbot. eauto.
Qed.

(* Reflexivity of [eutt_0], modulo a few assumptions. *)
Lemma reflexive_euttF0 eutt t :
  Reflexive eutt -> notau t -> euttF0 eutt t t.
Proof.
  intros. absobs t ot. destruct ot; try contradiction; econstructor; intros; subst; eauto.
Qed.

Lemma euttF_tau r t1 t2 :
  (euttF r t1 t2) ->
  euttF r (Tau t1) (Tau t2).
Proof.
  intros. destruct H. econstructor.
  - rewrite !finite_taus_tau. eauto.
  - intros. eapply EQV; apply unalltaus_tau; eauto.
Qed.

Lemma euttF_vis {u} (r : relation (itree E R)) (e : _ u) k1 k2 :
  (forall x, r (k1 x) (k2 x)) ->
  euttF r (Vis e k1) (Vis e k2).
Proof.
  intros. econstructor.
  - split; intros; now apply notau_finite_taus.
  - intros.
    apply unalltaus_notau_id in UNTAUS1; [ | constructor ].
    apply unalltaus_notau_id in UNTAUS2; [ | constructor ].
    subst. eauto.
Qed.

(**)

Lemma Reflexive_euttF (r : relation (itree E R)) :
  Reflexive r -> Reflexive (euttF r).
Proof.
  split.
  - reflexivity.
  - intros.
    erewrite (unalltaus_injective _ _ _ _ _ UNTAUS1 UNTAUS2).
    apply reflexive_euttF0; eauto using (untaus_prop notau).
Qed.

(* [eutt] is an equivalence relation. *)
Global Instance Reflexive_eutt: (Reflexive eutt).
Proof.
  pcofix Reflexive_eutt.
  intros. pfold. apply Reflexive_euttF. eauto.
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
    econstructor. intros. specialize (H0 x). pclearbot. eauto.
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
    dependent destruction REL1; dependent destruction REL2; eauto.
    econstructor. intros.
    specialize (H x); specialize (H0 x). pclearbot. eauto.
Qed.

(**)

(* [eutt] is preserved by removing one [Tau]. *)
Lemma eutt_tau1 (t : itree E R) : (Tau t) ~~ t.
Proof.
  pfold. split.
  - apply finite_taus_tau; auto.
  - intros n m t1' t2' H1 H2.
    apply unalltaus_tau in H1.
    assert (X := unalltaus_injective _ _ _ _ _ H1 H2); subst.
    apply reflexive_euttF0; eauto using (untaus_prop notau).
    left. apply Reflexive_eutt.
Qed.

(* [eutt] is preserved by removing all [Tau]. *)
Lemma untaus_eutt P n (t t' : itree E R) : untaus P n t t' -> t ~~ t'.
Proof.
  intros H.
  pfold. split.
  - eapply untaus_finite_taus; eauto.
  - induction H; intros.
    + rewrite (unalltaus_injective _ _ _ _ _ UNTAUS1 UNTAUS2).
      apply reflexive_euttF0; eauto using (untaus_prop notau).
      left; apply Reflexive_eutt.
    + apply unalltaus_tau in UNTAUS1. eauto.
Qed.

End EUTT.

Notation unalltaus := (untaus notau).

Hint Constructors euttF0.
Hint Constructors euttF0'.
Hint Constructors untaus.
Hint Unfold finite_taus.
Hint Constructors euttF.
Hint Resolve monotone_euttF0.
Hint Resolve monotone_euttF : paco.
Hint Resolve notau_ret.
Hint Resolve notau_vis.

Delimit Scope eutt_scope with eutt.

Infix "~~" := eutt (at level 70).

(* We can now rewrite with [eutt] equalities. *)
Instance Equivalence_eutt E R : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

(* Lemmas about [bind]. *)

Lemma untaus_bind P {E S R} : forall n t t' (k: S -> itree E R)
      (UNTAUS: untaus P n t t'),
  untaus anyitree n (ITree.bind t k) (ITree.bind t' k).
Proof.
  intros. induction UNTAUS; eauto.
  rewrite tau_bind. eauto.
Qed.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (ITree.bind t f) -> finite_taus t.
Proof.
  remember (ITree.bind t f) as tf eqn:Etf.
  intros [n [tf' TAUS]].
  generalize dependent t.
  induction TAUS; intros; subst.
  - absobs t0 ot0; destruct ot0; try contradiction; eauto using finite_taus_ret, finite_taus_vis.
  - absobs t0 ot0; destruct ot0; eauto using finite_taus_ret, finite_taus_vis.
    setoid_rewrite tau_bind in Etf.
    inv Etf.
    apply finite_taus_tau.
    eauto.
Qed.

Lemma untaus_eq_idx P E R: forall n m (t1 t2: itree E R),
    n = m -> untaus P n t1 t2 -> untaus P m t1 t2.
Proof. intros; subst; eauto. Qed.

Lemma untaus_untaus P Q E R: forall n m (t1 t2 t3: itree E R),
    untaus P n t1 t2 -> untaus Q m t2 t3 -> untaus Q (n+m) t1 t3.
Proof.
  intros n m t1 t2 t3. induction 1; simpl; eauto.
Qed.

Lemma untaus_unalltus_rev P E R: forall n m (t1 t2 t3: itree E R),
    untaus P n t1 t2 -> unalltaus m t1 t3 -> unalltaus (m-n) t2 t3.
Proof.
  intros. revert m t3 H0.
  induction H; intros.
  - eauto using untaus_eq_idx with arith.
  - inversion H0; try contradiction. eauto.
Qed.

Lemma eutt_strengthen {E R}:
  forall r (t1 t2: itree E R)
     (FIN: finite_taus t1 <-> finite_taus t2)
     (EQV: forall n1 n2 m1 m2 t1' t2'
              (UNT1: unalltaus m1 t1 t1')
              (UNT2: unalltaus m2 t2 t2')
              (LEn: m1 < n1)
              (LEm: m2 < n2),
         paco2 (euttF ∘ gres2 euttF) r t1' t2'),
    paco2 (euttF ∘ gres2 euttF) r t1 t2.
Proof.
  intros. pfold. econstructor; eauto.
  intros. hexploit (EQV (S (max n m))); eauto with arith. intro EQV'.
  punfold EQV'. destruct EQV'.
  eauto 7 using (untaus_prop notau).
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
      inv EQV'.
      * rewrite ret_bind in *.
        edestruct GF; eauto. apply FIN0. eauto.
      * rewrite vis_bind. eauto using finite_taus_vis.
    + assert (FT1 := H). apply finite_taus_bind_fst in FT1.
      assert (FT2 := FT1). apply FIN in FT2.
      destruct FT1 as [n [a FT1]], FT2 as [m [b FT2]].
      hexploit EQV; eauto. intros EQV'.
      edestruct @untaus_finite_taus; [eapply untaus_bind, FT1 | apply H0 in H].
      eapply untaus_finite_taus; eauto using untaus_bind.
      inv EQV'.
      * rewrite ret_bind in *.
        edestruct GF; eauto. apply FIN0. eauto.
      * rewrite vis_bind. eauto using finite_taus_vis.
  - intros.
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS1|]. intros [n' [a FT1]].
    hexploit (@finite_taus_bind_fst E); [do 2 eexists; apply UNTAUS2|]. intros [m' [b FT2]].
    hexploit @untaus_bind; [apply FT1|]. intros UT1.
    hexploit @untaus_bind; [apply FT2|]. intros UT2.
    specialize (EQV _ _ _ _ FT1 FT2).
    hexploit untaus_unalltus_rev; [apply UT1| |]; eauto. intros UAT1.
    hexploit untaus_unalltus_rev; [apply UT2| |]; eauto. intros UAT2.
    inv EQV.
    + rewrite ret_bind in UAT1, UAT2.
      eapply GF in REL. destruct REL.
      eapply monotone_euttF0; eauto using rclo2.
    + rewrite vis_bind in UAT1, UAT2.
      inversion UAT1; inversion UAT2. subst.
      econstructor. intros. specialize (H x). pclearbot. eauto using rclo2.
Qed.

Instance eutt_tau {E R} :
  Proper (@eutt E R ==>
          @eutt E R) (fun t => Tau t).
Proof.
  repeat intro. etransitivity. apply eutt_tau1.
  etransitivity. eauto.
  symmetry. apply eutt_tau1.
Qed.

Instance eutt_vis {E R u} (e: E u) :
  Proper (pointwise_relation _ eutt ==>
          @eutt E R) (fun k => Vis e k).
Proof.
  repeat intro. red in H. pfold. split; intros.
  - split; eauto.
  - inversion UNTAUS1; subst. inv UNTAUS1. inv UNTAUS2.
    econstructor; intros. left. apply H.
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

Instance subrelation_eq_eutt {E R} : subrelation (@eq_itree E R) eutt.
Proof.
  pcofix CIH. intros.
  pfold. econstructor.
  { split; [|symmetry in H0]; intros; destruct H as [? []]; eauto using eq_unalltaus. }

  intros. eapply eq_unalltaus_eq in H0; eauto. destruct H0 as [s' [UNTAUS' EQV']].
  hexploit @unalltaus_injective; [apply UNTAUS' | apply UNTAUS2 | intro X]; subst.

  punfold EQV'. unfold_eq_itree. absobs t1' ot1'. absobs s' os'. inv EQV'; eauto.
  - eapply untaus_prop in UNTAUS1. contradiction.
  - econstructor. intros. specialize (REL x0). pclearbot. eauto.
Qed.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt (ITree.map g (ITree.map f t))
       (ITree.map (fun x => g (f x)) t).
Proof.
  rewrite map_map. reflexivity.
Qed.
