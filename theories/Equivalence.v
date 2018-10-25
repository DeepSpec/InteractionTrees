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

Context {E : Effect} {R : Type}.

Inductive eutt_0 (eutt : relation (itree E R)) :
  relation (itree E R) :=
| Eutt_Ret : forall r, eutt_0 eutt (Ret r) (Ret r)
| Eutt_Vis : forall (e : E) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    eutt_0 eutt (Vis e k1) (Vis e k2).
Hint Constructors eutt_0.

Inductive untaus t' : itree E R -> Prop :=
| OneTau : forall t, untaus t' t -> untaus t' (Tau t)
| NoTau : untaus t' t'
.

Definition notau (t : itree E R) :=
  match t with
  | Tau _ => False
  | _ => True
  end.

Definition unalltaus t t' := notau t' /\ untaus t' t.

Definition finite_taus t := exists t', unalltaus t t'.

Definition is_spin (t : itree E R) := t = spin.

Definition eutt_ eutt : relation _ := fun t1 t2 =>
  (finite_taus t1 <-> finite_taus t2) /\
  forall t1' t2',
    unalltaus t1 t1' -> unalltaus t2 t2' ->
    eutt_0 eutt t1' t2'.

Lemma monotone_eutt_0 : monotone2 eutt_0.
Proof. pmonauto. Qed.

Hint Resolve monotone_eutt_0 : paco.

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

Definition eutt : relation (itree E R) := paco2 eutt_ bot2.

Global Arguments eutt t1%itree t2%itree.

Infix "~" := eutt
  (at level 80).

(**)

Lemma notau_unalltaus (t : itree E R) : notau t -> unalltaus t t.
Proof. split; [ auto | constructor ]. Qed.

Lemma unalltaus_untaus (t t' : itree E R) :
  unalltaus t t' -> untaus t' t.
Proof. firstorder. Qed.

Lemma unalltaus_injective : forall t t1 t2,
    unalltaus t t1 -> unalltaus t t2 -> t2 = t1.
Proof.
  intros t t1 t2 [I1 H1] [I2 H2].
  induction H1 as [t1_ H1 IH1| ];
    inversion H2 as [t2_ H2' H2'' | H2' ]; auto;
      subst; contradiction.
Qed.

Lemma unalltaus_notau : forall t t', ~unalltaus t (Tau t').
Proof.
  intros t t' [I H]; auto.
Qed.

Lemma unalltaus_tau (t1 t2 : itree E R) :
  unalltaus (Tau t1) t2 <-> unalltaus t1 t2.
Proof.
  split; intros [I1 H1].
  - inversion H1; subst.
    + split; assumption.
    + inversion I1.
  - split; [ | apply OneTau ]; assumption.
Qed.

Lemma finite_taus_notau (t : itree E R) : notau t -> finite_taus t.
Proof.
  eexists; split; [ eauto | econstructor ].
Qed.

Lemma notau_finite_taus (t : itree E R) : notau t -> finite_taus t.
Proof.
  exists t. split. assumption. constructor.
Qed.

Lemma finite_taus_Ret (r : R) : finite_taus (Ret r).
Proof.
  apply finite_taus_notau; constructor.
Qed.

Lemma finite_taus_Vis (e : E) (k : reaction e -> itree E R) :
  finite_taus (Vis e k).
Proof.
  apply finite_taus_notau; constructor.
Qed.

Lemma finite_taus_Tau (t : itree E R) :
    finite_taus (Tau t) <-> finite_taus t.
Proof.
  split; intros [t' [I1 H1]].
  - inversion H1; subst.
    + exists t'; split; assumption.
    + inversion I1.
  - exists t'; split; [ | apply OneTau ]; assumption.
Qed.

Lemma untaus_finite_taus (t t' : itree E R) :
    untaus t t' -> (finite_taus t <-> finite_taus t').
Proof.
  induction 1.
  - rewrite finite_taus_Tau; assumption.
  - reflexivity.
Qed.

Lemma unalltaus_finite_taus (t t' : itree E R) :
    unalltaus t t' -> (finite_taus t <-> finite_taus t').
Proof.
  intros []. symmetry. apply untaus_finite_taus; assumption.
Qed.

(**)

Lemma eutt_finite_taus (t1 t2 : itree E R) :
  t1 ~ t2 -> finite_taus t1 <-> finite_taus t2.
Proof. intro H; punfold H; apply H. Qed.

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

Lemma reflexive_eutt_0 eutt t :
  Reflexive eutt -> notau t -> eutt_0 eutt t t.
Proof.
  intros Hrefl Ht.
  destruct t.
  + constructor.
  + inversion Ht.
  + constructor; auto.
Qed.

(* [eutt] is an equivalence relation. *)

Global Instance Reflexive_eutt : Reflexive eutt.
Proof.
  pcofix Reflexive_eutt.
  intro t.
  pfold.
  split.
  - reflexivity.
  - intros t1 t2 H1 H2.
    erewrite (unalltaus_injective _ _ _ H1 H2).
    apply reflexive_eutt_0; auto.
    firstorder.
Qed.

Global Instance Symmetric_eutt : Symmetric eutt.
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
    inversion H12.
    + constructor.
    + constructor.
      intro x.
      specialize (H x); pclearbot.
      auto.
Qed.

Lemma eutt_0_inj_Vis : forall rel e (k : reaction e -> itree E R) z,
    eutt_0 rel (Vis e k) z ->
    exists k', z = Vis e k' /\ (forall x, rel (k x) (k' x)).
Proof.
  intros.
  refine match H in eutt_0 _ X Z
               return match X return Prop with
                      | Vis e k => _
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
    + subst. inversion H23. constructor.
    + subst. eapply eutt_0_inj_Vis in H23.
      destruct H23 as [ k' [ ? ? ] ].
      subst.
      constructor.
      * intro x.
        specialize (H x); specialize (H4 x); pclearbot.
        right; eapply Transitive_eutt; eauto.
Qed.

Lemma equiv_tau (t : itree E R) : Tau t ~ t.
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

Lemma unalltaus_equiv (t t' : itree E R) : unalltaus t t' -> t ~ t'.
Proof.
  intros H.
  pfold. split.
  - apply unalltaus_finite_taus; assumption.
  - destruct H. induction H0.
    + intros t1' t2' H1 H2. apply IHuntaus.
      apply unalltaus_tau; assumption. assumption.
    + intros t1' t2' H1 H2.
      rewrite (unalltaus_injective _ _ _ H1 H2).
      apply reflexive_eutt_0.
      { left; apply Reflexive_eutt. }
      { apply H1. }
Qed.

End EUTT.

Hint Resolve monotone_eutt_0 : paco.
Hint Resolve monotone_eutt_ : paco.
Infix "~" := eutt (at level 80).

Add Parametric Relation E R : (itree E R) eutt
    as eutt_equiv.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (t >>= f) -> finite_taus t.
Proof.
  intros [tf' [Hnotau Hunalltaus]].
  remember (t >>= f)%itree as tf eqn:Etf.
  generalize dependent t.
  induction Hunalltaus; intros t' Etf;
    rewrite match_bind in Etf; destruct t'; inversion Etf;
    try (apply finite_taus_notau; constructor).
  - apply finite_taus_Tau.
    apply IHHunalltaus; auto.
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
  - apply finite_taus_notau; constructor.
Qed.

Lemma notau_bind {E R S} t (k : R -> itree E S) :
  notau (t >>= k) -> notau t.
Proof.
  rewrite match_bind.
  destruct t; constructor + contradiction.
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
        rewrite unalltaus_tau.
        split; auto.
    + edestruct IHHunalltaus as [t2 [Ht2 Htk2]]; eauto.
      eexists; split; eauto.
      rewrite unalltaus_tau; auto.
  - exists t'. split.
    + eapply notau_unalltaus, notau_bind; eauto.
    + apply notau_unalltaus; auto.
Qed.

Lemma eutt_bind {E R S} (t1 t2 : itree E R) (k1 k2 : R -> itree E S) :
    t1 ~ t2 -> (forall x, k1 x ~ k2 x) -> (t1 >>= k1) ~ (t2 >>= k2).
Proof.
  revert t1 t2.
  pcofix eutt_bind.
  intros t1 t2 Ht Hk.
  pfold.
  split.
  - split; apply finite_taus_bind; auto;
      intros; symmetry; auto.
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
      left; eapply paco2_mon; eauto; intros ? ? [].
    + rewrite match_bind in Htk1;
        destruct Htk1 as [Hnotau1 Huntau1]; inversion Huntau1.
      rewrite match_bind in Htk2;
        destruct Htk2 as [Hnotau2 Huntau2]; inversion Huntau2.
      constructor.
      intro x. right. apply eutt_bind; auto.
      destruct (H x) as [ | []]; auto.
Qed.
