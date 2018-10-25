Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.

Require Import Paco.paco.
Require Import ExtLib.Structures.Monad.

Require Import ITree.ITree.

Section EUTT.

Context {E : Effect} {R : Type}.

Inductive eutt_0 (eutt : relation (itree E R)) :
  relation (itree E R) :=
| Eutt_Ret : forall r, eutt_0 eutt (Ret r) (Ret r)
| Eutt_Vis : forall (e : E) k1 k2,
    (forall x, eutt (k1 x) (k2 x)) ->
    eutt_0 eutt (Vis e k1) (Vis e k2).
Hint Constructors eutt_0.

Inductive untaus' t' : itree E R -> Prop :=
| OneTau : forall t, untaus' t' t -> untaus' t' (Tau t)
| NoTau : untaus' t' t'
.

Definition notau (t : itree E R) :=
  match t with
  | Tau _ => False
  | _ => True
  end.

Definition untaus t t' := notau t' /\ untaus' t' t.

Definition finite_taus t := exists t', untaus t t'.

Definition is_spin (t : itree E R) := t = spin.

Definition eutt_ eutt : relation _ := fun t1 t2 =>
  (finite_taus t1 <-> finite_taus t2) /\
  forall t1' t2',
    untaus t1 t1' -> untaus t2 t2' ->
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

Definition eutt := paco2 eutt_ bot2.

Infix "~" := eutt
  (at level 80).

(**)

Lemma untaus_injective : forall t t1 t2,
    untaus t t1 -> untaus t t2 -> t2 = t1.
Proof.
  intros t t1 t2 [I1 H1] [I2 H2].
  induction H1 as [t1_ H1 IH1| ];
    inversion H2 as [t2_ H2' H2'' | H2' ]; auto;
      subst; contradiction.
Qed.

Lemma untaus_notau : forall t t', ~untaus t (Tau t').
Proof.
  intros t t' [I H]; auto.
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

Global Instance Reflexive_eutt : Reflexive eutt.
Proof.
  pcofix Reflexive_eutt.
  intro t.
  pfold.
  split.
  - reflexivity.
  - intros t1 t2 H1 H2.
    erewrite (untaus_injective _ _ _ H1 H2).
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

End EUTT.

Hint Resolve monotone_eutt_0 : paco.
Hint Resolve monotone_eutt_ : paco.
Infix "~" := eutt (at level 80).

Add Parametric Relation E R : (itree E R) eutt
    as eutt_equiv.

Lemma bind_tau : forall {E R S} (t : itree E R) (f : R -> itree E S) ,
    bind (Tau t) f = Tau (bind t f).
Proof.
  intros E R S t f.
  rewrite match_itree at 1.
  reflexivity.
Qed.


(*
Lemma finite_taus_bind_inv1 : forall {E R S} (t : itree E R) (f : R -> itree E S),
    finite_taus (bind t f) -> finite_taus t.
Proof.
  intros E R S t f H.
  unfold finite_taus in *.
  destruct H as [t' [I1 H1]].
  remember (bind t f) as u eqn:Heq.
  generalize dependent t.
  induction H1; intros t1 Heq.
  - rewrite bind_def in Heq. destruct t1; inversion Heq; subst.
    + exists (Ret r). split. simpl. auto. apply NoTau.
    + destruct (@IHuntaus' t1 eq_refl).
      exists x. destruct H as [Hx1 Hx2].
      split. assumption. apply OneTau. assumption.
  - subst.
    rewrite bind_def in I1.
    destruct t1; simpl in *.
    + inversion I1.
    + exists (Vis e k). split. simpl; auto. apply NoTau.
    + inversion I1.
Qed.
*)

Lemma finite_taus_notau {E R} (t : itree E R) :
  notau t -> finite_taus t.
Proof.
  eexists; split; [ eauto | econstructor ].
Qed.

Lemma finite_taus_Ret {E R} (r : R) : @finite_taus E _ (Ret r).
Proof.
  apply finite_taus_notau; constructor.
Qed.

Lemma finite_taus_Vis {E : Effect} {R}
      (e : E) (k : reaction e -> itree E R) :
  finite_taus (Vis e k).
Proof.
  apply finite_taus_notau; constructor.
Qed.

Lemma finite_taus_tau {E R} (t : itree E R) :
    finite_taus (Tau t) <-> finite_taus t.
Proof.
  split; intros [t' [I1 H1]].
  - inversion H1; subst.
    + exists t'; split; assumption.
    + inversion I1.
  - exists t'; split; [ | apply OneTau ]; assumption.
Qed.

Lemma untaus_tau {E R} (t1 t2 : itree E R) :
  untaus (Tau t1) t2 <-> untaus t1 t2.
Proof.
  split; intros [I1 H1].
  - inversion H1; subst.
    + split; assumption.
    + inversion I1.
  - split; [ | apply OneTau ]; assumption.
Qed.

Lemma notau_finite_taus : forall (E : Effect) (R : Type) (t : itree E R),
    notau t -> finite_taus t.
Proof.
  intros E R t H. exists t. split. assumption. constructor.
Qed.

Lemma untaus'_finite_taus : forall (E : Effect) (R : Type) (t t' : itree E R),
    untaus' t t' -> (finite_taus t <-> finite_taus t').
Proof.
  intros E R t t' H. induction H.
  - intuition. rewrite finite_taus_tau; assumption.
    rewrite finite_taus_tau in H2. auto.
  - reflexivity.
Qed.

Lemma untaus_finite_taus :  forall (E : Effect) (R : Type) (t t' : itree E R),
    untaus t t' -> (finite_taus t <-> finite_taus t').
Proof.
  intros E R t t' [H1 H2]. symmetry. apply untaus'_finite_taus; assumption.
Qed.

Lemma equiv_tau {E R} (t : itree E R) : Tau t ~ t.
Proof.
  pfold.
  split.
  - apply finite_taus_tau.
  - intros t1' t2' H1 H2.
    rewrite untaus_tau in H1.
    pose proof (untaus_injective _ _ _ H1 H2); subst.
    apply reflexive_eutt_0.
    { left; apply Reflexive_eutt. }
    { apply H1. }
Qed.

Lemma untaus_equiv : forall (E : Effect) (R : Type) (t t' : itree E R),
    untaus t t' -> t ~ t'.
Proof.
  intros E R t t' H.
  pfold. split.
  - apply untaus_finite_taus; assumption.
  - destruct H. induction H0.
    + intros t1' t2' H1 H2. apply IHuntaus'.
      apply untaus_tau; assumption. assumption.
    + intros t1' t2' H1 H2.
      rewrite (untaus_injective _ _ _ H1 H2).
      apply reflexive_eutt_0.
      { left; apply Reflexive_eutt. }
      { apply H1. }
Qed.

Lemma finite_taus_equiv : forall (E : Effect) (R : Type) (t1 t2 : itree E R),
    t1 ~ t2 -> finite_taus t1 -> finite_taus t2.
Proof.
  intros E R t1 t2 H1 H2.
  destruct H2 as [t1' [I H]].
  generalize dependent t2.
  induction H; intros t2 H1.
  - apply IHuntaus'. rewrite equiv_tau in H1. assumption.
  - pinversion H1.
    apply H.
    apply notau_finite_taus; auto.
Qed.

Lemma finite_taus_bind_fst {E R S}
      (t : itree E R) (f : R -> itree E S) :
  finite_taus (t >>= f) -> finite_taus t.
Proof.
  intros [tf' [Hnotau Huntaus]].
  remember (t >>= f)%itree as tf eqn:Etf.
  generalize dependent t.
  induction Huntaus; intros t' Etf;
    rewrite match_bind in Etf; destruct t'; inversion Etf;
    try (apply finite_taus_notau; constructor).
  - apply finite_taus_tau.
    apply IHHuntaus; auto.
  - subst tf'; inversion Hnotau.
Qed.

Lemma eutt_equiv_finite_taus E R (t1 t2 : itree E R) :
  t1 ~ t2 -> finite_taus t1 <-> finite_taus t2.
Proof.
  intro H; punfold H; apply H.
Qed.

Lemma iff_or_and {P Q : Prop} :
  P <-> Q -> P \/ Q -> P /\ Q.
Proof. firstorder. Qed.

Lemma eutt_untaus_1 {E R} (t1 t2 : itree E R) :
  t1 ~ t2 -> finite_taus t1 ->
  exists t1' t2',
    untaus t1 t1' /\ untaus t2 t2' /\ eutt_0 eutt t1' t2'.
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

Lemma finite_taus_bind_untaus {E R S}
      (t t' : itree E R) (k : R -> itree E S) :
  untaus' t' t ->
  finite_taus (t >>= k) <-> finite_taus (t' >>= k).
Proof.
  induction 1.
  - rewrite (match_bind (Tau _)); simpl.
    rewrite finite_taus_tau; auto.
  - reflexivity.
Qed.

Lemma untaus_untaus' {E R} (t t' : itree E R) :
  untaus t t' -> untaus' t' t.
Proof. firstorder. Qed.

Lemma finite_taus_bind {E R S}
      (t1 t2 : itree E R) (f : R -> itree E S) :
    t1 ~ t2 -> finite_taus (t1 >>= f) -> finite_taus (t2 >>= f).
Proof.
  intros Hequiv Hfin.
  destruct (eutt_untaus_1 t1 t2) as [t1' [t2' [Ht1' [Ht2' Ht12']]]].
  { auto. }
  { eapply finite_taus_bind_fst; eauto. }
  rewrite finite_taus_bind_untaus
    by eauto using untaus_untaus'.
  rewrite finite_taus_bind_untaus in Hfin
    by eauto using untaus_untaus'.
  rewrite match_bind in Hfin; rewrite match_bind.
  inversion Ht12'; subst; [ auto | ].
  apply finite_taus_notau; constructor.
Qed.

(*
Lemma eutt_bind_hom1 : forall {E R S} (t1 t2 : itree E R) (f : R -> itree E S),
    t1 ~ t2 -> (bind t1 f) ~ (bind t2 f).
Proof.
Admitted.
*)
