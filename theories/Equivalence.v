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

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.

Require Import Paco.paco.
Require Import ExtLib.Structures.Monad.

Require Import ITree.ITree.

Lemma iff_or_and {P Q : Prop} :
  P <-> Q -> P \/ Q -> P /\ Q.
Proof. firstorder. Qed.

Section EUTT.

Context {E : Type -> Type} {R : Type}.

(* Equivalence between visible steps of computation (i.e., [Vis] or
   [Ret], parameterized by a relation [eutt] between continuations
   in the [Vis] case. *)
Variant eutt_0F (eutt : relation (itree E R))
: relation (itreeF E R (itree E R)) :=
| Eutt_Ret : forall r, eutt_0F eutt (RetF r) (RetF r)
| Eutt_Vis : forall {u} (e : E u) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    eutt_0F eutt (VisF e k1) (VisF e k2).
Hint Constructors eutt_0F.

Inductive eutt_0 (eutt : relation (itree E R)) (l r : itree E R) : Prop :=
{ eutt_0_observe : eutt_0F eutt l.(observe) r.(observe) }.

(* [untaus t' t] holds when [t = Tau (... Tau t' ...)]:
   [t] steps to [t'] by "peeling off" a finite number of [Tau].
   "Peel off" means to remove only taus at the root of the tree,
   not any behind a [Vis] step). *)
Inductive untaus t' : itree E R -> Prop :=
| OneTau : forall t, untaus t' t -> untaus t' (Tau t)
| NoTau : untaus t' t'
.

(* [notau t] holds when [t] does not start with a [Tau]. *)
Definition notau (t : itree E R) : Prop :=
  match t.(observe) with
  | TauF _ => False
  | _ => True
  end.

(* [unalltaus t t'] holds when [t] steps to [t'] by peeling off
   all of its taus, of which there must be a finite number. *)
Definition unalltaus t t' := notau t' /\ untaus t' t.

(* [finite_taus t] holds when [t] has a finite number of taus
   to peel. *)
Definition finite_taus t : Prop := exists t', unalltaus t t'.

(* [eutt_ eutt t1 t2] means that, if [t1] or [t2] ever takes a
   visible step ([Vis] or [Ret]), then the other takes the same
   step, and the subsequent continuations (in the [Vis] case) are
   related by [eutt]. In particular, [(t1 = spin)%eq_itree] if
   and only if [(t2 = spin)%eq_itree]. Note also that in that
   case, the parameter [eutt] is irrelevant.

   This is the relation we will take a fixpoint of. *)
Definition eutt_ (eutt : relation _) : relation _ := fun t1 t2 =>
  (finite_taus t1 <-> finite_taus t2) /\
  forall t1' t2',
    unalltaus t1 t1' -> unalltaus t2 t2' ->
    eutt_0 eutt t1' t2'.

(* Paco takes the greatest fixpoints of monotone relations. *)

(* [eutt_0] is monotone: if a binary relation [eutt] implies [eutt'],
   then [eutt_0 eutt] implies [eutt_0 eutt']. *)
Lemma monotone_eutt_0 : monotone2 eutt_0.
Proof.
  constructor. inversion IN.
  inversion eutt_0_observe0; constructor; eauto.
Qed.

Hint Resolve monotone_eutt_0 : paco.

(* [eutt_] is monotone. *)
Lemma monotone_eutt_ : monotone2 eutt_.
Proof.
  unfold monotone2.
  intros t1 t2 r r' [I H] Hr.
  split.
  - auto.
  - intros t1' t2' H1 H2.
    eapply monotone_eutt_0; eauto.
Qed.

Hint Resolve monotone_eutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : relation (itree E R) := paco2 eutt_ bot2.

Global Arguments eutt t1%itree t2%itree.

Delimit Scope eutt_scope with eutt.
Local Open Scope eutt_scope.

Infix "~" := eutt (at level 70) : eutt_scope.

(* Lemmas about the auxiliary relations. *)

(* Many have a name [X_Y] to represent an implication
   [X _ -> Y _] (possibly with more arguments on either side). *)

(* If a tree [t] does not start with a [Tau], then peeling off
   all [Tau] does nothing to it. *)
Lemma notau_unalltaus (t : itree E R) : notau t -> unalltaus t t.
Proof. split; [ auto | constructor ]. Qed.

(* If [t] does not start with [Tau], removing all [Tau] does
   nothing. Can be thought of as [notau_unalltaus] composed with
   [unalltaus_injective] (below). *)
Lemma unalltaus_notau_id t t' :
  unalltaus t t' -> notau t -> t' = t.
Proof. now intros [? []]. Qed.

(* "Peel off all taus" is a special case of "peel off taus". *)
Lemma unalltaus_untaus (t t' : itree E R) :
  unalltaus t t' -> untaus t' t.
Proof. firstorder. Qed.

(* There is only one way to peel off all taus. *)
Lemma unalltaus_injective : forall t t1 t2,
    unalltaus t t1 -> unalltaus t t2 -> t2 = t1.
Proof.
  intros t t1 t2 [I1 H1] [I2 H2].
  induction H1 as [t1_ H1 IH1| ];
    inversion H2 as [t2_ H2' H2'' | H2' ]; auto;
      subst; contradiction.
Qed.

(* Adding a [Tau] to [t1] then peeling them all off produces
   the same result as peeling them all off from [t1]. *)
Lemma unalltaus_tau (t1 t2 : itree E R) :
  unalltaus (Tau t1) t2 <-> unalltaus t1 t2.
Proof.
  split; intros [I1 H1].
  - inversion H1; subst.
    + split; assumption.
    + inversion I1.
  - split; [ | apply OneTau ]; assumption.
Qed.

(* If [t] does not start with [Tau], then it starts with finitely
   many [Tau]. *)
Lemma notau_finite_taus (t : itree E R) : notau t -> finite_taus t.
Proof.
  exists t. split. assumption. constructor.
Qed.

(* [Vis] and [Ret] start with no taus, of course. *)
Lemma finite_taus_Ret (r : R) : finite_taus (Ret r).
Proof.
  apply notau_finite_taus; constructor.
Qed.

Lemma finite_taus_Vis {u} (e : E u) (k : u -> itree E R) :
  finite_taus (Vis e k).
Proof.
  apply notau_finite_taus; constructor.
Qed.

(* [finite_taus] is preserved by removing or adding one [Tau]. *)
Lemma finite_taus_Tau (t : itree E R) :
    finite_taus (Tau t) <-> finite_taus t.
Proof.
  split; intros [t' [I1 H1]].
  - inversion H1; subst.
    + exists t'; split; assumption.
    + inversion I1.
  - exists t'; split; [ | apply OneTau ]; assumption.
Qed.

(* [finite_taus] is preserved by removing or adding any finite
   number of [Tau]. *)
Lemma untaus_finite_taus (t t' : itree E R) :
    untaus t t' -> (finite_taus t <-> finite_taus t').
Proof.
  induction 1.
  - rewrite finite_taus_Tau; assumption.
  - reflexivity.
Qed.

(* [finite_taus] is preserved by removing all taus. *)
Lemma unalltaus_finite_taus (t t' : itree E R) :
    unalltaus t t' -> (finite_taus t <-> finite_taus t').
Proof.
  intros []. symmetry. apply untaus_finite_taus; assumption.
Qed.

(**)

(* If [t1] and [t2] are equivalent, then either both start with
   finitely many taus, or both [spin]. *)
Lemma eutt_finite_taus (t1 t2 : itree E R) :
  t1 ~ t2 -> finite_taus t1 <-> finite_taus t2.
Proof. intro H; punfold H; apply H. Qed.

(* If [t1] and [t2] are equivalent, and one starts with finitely many
   taus, then both do, and the peeled off [t1'] and [t2'] take
   the same visible step. *)
Lemma eutt_unalltaus_1 (t1 t2 : itree E R) :
  t1 ~ t2 -> finite_taus t1 ->
  exists t1' t2',
    unalltaus t1 t1' /\ unalltaus t2 t2' /\ eutt_0 eutt t1' t2'.
Proof.
  intros Heutt Ht1. punfold Heutt.
  destruct Heutt as [Hfinite Heutt0].
  assert (Ht2 : finite_taus t2).
  { apply Hfinite; auto. }
  destruct Ht1 as [t1' Ht1'].
  destruct Ht2 as [t2' Ht2'].
  exists t1'.
  exists t2'.
  do 2 (split; auto).
  eapply monotone_eutt_0; eauto.
  (* No idea what's going on. Paco magic *)
  intros ? ? PR; pfold. destruct PR; [ punfold H | inversion H ].
Qed.

(* Reflexivity of [eutt_0], modulo a few assumptions. *)
Lemma reflexive_eutt_0 eutt t :
  Reflexive eutt -> notau t -> eutt_0 eutt t t.
Proof.
  intros Hrefl Ht.
  revert Ht.
  intros.
  constructor.
  unfold notau in *.
  destruct (observe t); try constructor.
  contradiction.
  intros. eapply Hrefl.
Qed.

(**)

Lemma eutt_Vis_ {u} (r : relation (itree E R)) (e : _ u) k1 k2 :
  (forall x, r (k1 x) (k2 x)) -> eutt_ r (Vis e k1) (Vis e k2).
Proof.
  split.
  - split; intros; now apply notau_finite_taus.
  - intros t1' t2' H1 H2.
    apply unalltaus_notau_id in H1; [ | constructor ].
    apply unalltaus_notau_id in H2; [ | constructor ].
    constructor. subst. constructor. apply H.
Qed.

Lemma Reflexive_eutt_ (r : relation (itree E R)) :
  Reflexive r -> Reflexive (eutt_ r).
Proof.
  split.
  - reflexivity.
  - intros t1 t2 H1 H2.
    erewrite (unalltaus_injective _ _ _ H1 H2).
    apply reflexive_eutt_0; auto.
    firstorder.
Qed.

(* [eutt] is an equivalence relation. *)
Global Instance Reflexive_eutt
: forall r, Reflexive r -> Reflexive (paco2 eutt_ r).
Proof.
  pcofix Reflexive_eutt.
  intros.
  pfold.
  apply Reflexive_eutt_; auto.
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
  - intros t1' t2' H21' H12'.
    specialize (H12 _ _ H12' H21').
    constructor.
    inversion H12.
    + inversion eutt_0_observe0; try constructor.
      admit.
Admitted. (* todo(gmm): not sure what is happening here *)

(*
(* Inversion of an [eutt_0] assumption that doesn't produce
   heterogeneous equalities ([existT _ _ _ = existT _ _ _]). *)
Lemma eutt_0_inj_Vis : forall {u} rel e (k : u -> itree E R) z,
    eutt_0 rel (Vis e k) z ->
    exists k', z = Vis e k' /\ (forall x, rel (k x) (k' x)).
Proof.
  intros.
  refine match H in eutt_0 _ X Z
               return match X.(observe) return Prop with
                      | VisF e k => _
                      | _ => True
                      end
         with
         | Eutt_Ret _ _ => I
         | Eutt_Vis _ _ _ _ _ => _
         end; simpl.
  eexists; split. reflexivity. assumption.
Defined.

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
  - intros t1' t3' H1 H3.
    destruct (proj1 I12 (ex_intro _ _ H1)) as [t2' H2].
    specialize (H12 _ _ H1 H2).
    specialize (H23 _ _ H2 H3).
    inversion H12.
    + subst. now inversion H23.
    + subst. eapply eutt_0_inj_Vis in H23.
      destruct H23 as [ k' [ ? ? ] ].
      subst.
      constructor.
      * intro x.
        specialize (H x); specialize (H4 x); pclearbot.
        right; eapply Transitive_eutt; eauto.
Qed.

(**)

(* [eutt] is preserved by removing one [Tau]. *)
Lemma eutt_tau (t : itree E R) : Tau t ~ t.
Proof.
  pfold.
  split.
  - apply finite_taus_Tau.
  - intros t1' t2' H1 H2.
    rewrite unalltaus_tau in H1.
    pose proof (unalltaus_injective _ _ _ H1 H2); subst.
    apply reflexive_eutt_0.
    { left; apply Reflexive_eutt. }
    { apply H1. }
Qed.

(* [eutt] is preserved by removing all [Tau]. *)
Lemma unalltaus_eutt (t t' : itree E R) : unalltaus t t' -> t ~ t'.
Proof.
  intros H.
  pfold. split.
  - now apply unalltaus_finite_taus.
  - destruct H. induction H0.
    + intros t1' t2' H1 H2.
      apply IHuntaus; auto.
      now apply unalltaus_tau.
    + intros t1' t2' H1 H2.
      rewrite (unalltaus_injective _ _ _ H1 H2).
      apply reflexive_eutt_0.
      { left; apply Reflexive_eutt. }
      { apply H1. }
Qed.
*)

End EUTT.

Hint Resolve monotone_eutt_0 : paco.
Hint Resolve monotone_eutt_ : paco.
Infix "~" := eutt (at level 80).
(*
(* We can now rewrite with [eutt] equalities. *)
Add Parametric Relation E R : (itree E R) eutt
    as eutt_equiv.

(* Lemmas about [bind]. *)

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (t >>= f) -> finite_taus t.
Proof.
  intros [tf' [Hnotau Hunalltaus]].
  remember (t >>= f)%itree as tf eqn:Etf.
  generalize dependent t.
  (* todo(gmm): this doesn't port well. *)
  induction Hunalltaus; intros t' Etf;
    rewrite match_bind in Etf; destruct t'; inversion Etf;
    try now apply notau_finite_taus.
  - apply finite_taus_Tau.
    apply IHHunalltaus.
    unfold bind. unfold bind'. unfold Tau. simpl.
  - subst tf'; inversion Hnotau.
Qed.

Lemma finite_taus_bind_unalltaus {E R S}
      (t t' : itree E R) (k : R -> itree E S) :
  untaus t' t ->
  finite_taus (t >>= k) <-> finite_taus (t' >>= k).
Proof.
  induction 1.
  - rewrite (match_bind (Tau _)); simpl.
    rewrite finite_taus_Tau; auto.
  - reflexivity.
Qed.

Lemma finite_taus_bind {E R S}
      (t1 t2 : itree E R) (k1 k2 : R -> itree E S) :
    t1 ~ t2 -> (forall x, k1 x ~ k2 x) ->
    finite_taus (t1 >>= k1) -> finite_taus (t2 >>= k2).
Proof.
  intros Ht Hk Hfin.
  destruct (eutt_unalltaus_1 t1 t2) as [t1' [t2' [Ht1' [Ht2' Ht12']]]].
  { auto. }
  { eapply finite_taus_bind_fst; eauto. }
  rewrite finite_taus_bind_unalltaus
    by eauto using unalltaus_untaus.
  rewrite finite_taus_bind_unalltaus in Hfin
    by eauto using unalltaus_untaus.
  rewrite match_bind in Hfin; rewrite match_bind.
  inversion Ht12'; subst; simpl in *.
  - rewrite <- eutt_finite_taus; eauto.
  - apply notau_finite_taus; constructor.
Qed.

Lemma notau_bind {E R S} t (k : R -> itree E S) :
  notau (t >>= k) -> notau t.
Proof.
  rewrite match_bind; now destruct t.
Qed.

Lemma unalltaus_bind {E R S} (t : itree E R) (k : R -> itree E S) tk' :
  unalltaus (t >>= k) tk' ->
  (exists t', unalltaus t t' /\ unalltaus (t' >>= k) tk').
Proof.
  intros [Hnotau Hunalltaus].
  remember (t >>= k)%itree as tk eqn:Etk.
  generalize dependent t.
  induction Hunalltaus; intros t' Etk'; subst.
  - rewrite match_bind in Etk'.
    destruct t'; simpl in Etk'; inversion Etk'; subst.
    + exists (Ret r). split.
      * do 2 constructor.
      * rewrite match_bind; simpl; rewrite <- Etk'.
        now rewrite unalltaus_tau.
    + edestruct IHHunalltaus as [t2 [Ht2 Htk2]]; eauto.
      eexists; split; eauto.
      rewrite unalltaus_tau; auto.
  - exists t'. split.
    + eapply notau_unalltaus, notau_bind; eauto.
    + apply notau_unalltaus; auto.
Qed.

(* [eutt] is a congruence wrt. [bind] *)
Lemma eutt_bind {E R S} (t1 t2 : itree E R) (k1 k2 : R -> itree E S) :
    t1 ~ t2 -> (forall x, k1 x ~ k2 x) -> (t1 >>= k1) ~ (t2 >>= k2).
Proof.
  revert t1 t2.
  pcofix eutt_bind.
  intros t1 t2 Ht Hk.
  pfold.
  split.
  - split; now apply finite_taus_bind.
  - intros tk1' tk2' H1' H2'.
    pose proof (unalltaus_bind _ _ _ H1') as [t1' [Ht1 Htk1]].
    pose proof (unalltaus_bind _ _ _ H2') as [t2' [Ht2 Htk2]].
    punfold Ht.
    destruct Ht as [_ Ht].
    destruct (Ht _ _ Ht1 Ht2).
    + rewrite match_bind in Htk1; rewrite match_bind in Htk2;
        simpl in *.
      specialize (Hk r0).
      punfold Hk.
      destruct Hk as [_ Hk].
      eapply monotone_eutt_0; eauto.
      intros ? ? [ | []].
      now left; eapply paco2_mon; eauto.
    + rewrite match_bind in Htk1;
        destruct Htk1 as [Hnotau1 Huntau1]; inversion Huntau1.
      rewrite match_bind in Htk2;
        destruct Htk2 as [Hnotau2 Huntau2]; inversion Huntau2.
      constructor.
      intro x. right. apply eutt_bind; auto.
      destruct (H x) as [ | []]; auto.
Qed.

(* Failed naive attempt *)
Lemma eutt_bind_bind_fail {E R S T}
      (t : itree E R) (k : R -> itree E S) (h : S -> itree E T) :
    (t >>= k >>= h) ~ (t >>= fun r => k r >>= h)%itree.
Proof.
  revert t; pcofix eutt_bind_bind; intros t.
  do 2 rewrite (match_bind t).
  destruct t; simpl.
  - now eapply paco2_mon; [ eapply Reflexive_eutt | ].
  - rewrite (match_bind (Tau _)); simpl. admit. (* Stuck? *)
  - rewrite (match_bind (Vis _ _)); simpl.
    pfold.
    apply eutt_Vis_; auto.
Abort.
*)