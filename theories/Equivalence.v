Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.

Require Import Paco.paco.
Require Import ExtLib.Structures.Monad.

Require Import ITree.ITree.

Section EUTT.

Variable E : Type -> Type.
Variable R : Type.

Inductive eutt_0 (eutt : relation (itree E R)) :
  relation (itree E R) :=
| Eutt_Ret : forall r, eutt_0 eutt (Ret r) (Ret r)
| Eutt_Vis : forall X (e : E X) k1 k2,
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

Definition reflexive_eutt : reflexive _ eutt.
Proof.
  pcofix reflexive_eutt.
  intro t.
  pfold.
  split.
  - reflexivity.
  - intros t1 t2 H1 H2.
    erewrite (untaus_injective _ _ _ H1 H2).
    destruct t1.
    + constructor.
    + constructor; auto.
    + destruct (untaus_notau _ _ H1).
Qed.

Lemma eutt_0_inj_Vis : forall {T} rel e (k : T -> itree E R) z,
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
         | Eutt_Vis _ _ _ _ _ _ => _
         end; simpl.
  eexists; split. reflexivity. assumption.
Defined.

Definition transitive_eutt : transitive _ eutt.
Proof.
  pcofix transitive_eutt.
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
        right; eapply transitive_eutt; eauto.
Qed.

End EUTT.

Arguments finite_taus {E R}.
Arguments untaus {E R}.
Hint Resolve monotone_eutt_0 : paco.
Hint Resolve monotone_eutt_ : paco.
Infix "~" := (@eutt _ _) (at level 80).


Lemma bind_tau : forall {E R S} (t : itree E R) (f : R -> itree E S) ,
    bind (Tau t) f = Tau (bind t f).
Proof.
  intros E R S t f.
  rewrite match_itree at 1.
  reflexivity.
Qed.


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

Lemma finite_taus_tau1: forall (E : Type -> Type) (R : Type) (t : itree E R),
    finite_taus t -> finite_taus (Tau t).
Proof.
  intros E R t H.
  destruct H as [t' [I1 H1]].
  exists t'. split. assumption. apply OneTau. assumption.
Qed.

Lemma finite_taus_tau2: forall (E : Type -> Type) (R : Type) (t : itree E R),
    finite_taus (Tau t) -> finite_taus t.
Proof.
  intros E R t H.
  destruct H as [t' [I1 H1]].
  inversion H1.
  - subst. exists t'. split; assumption.
  - subst. inversion I1.
Qed.

Lemma untaus_tau_tau1 : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    untaus t1 t2 -> untaus (Tau t1) t2.
Proof.
  intros E R t1 t2 H.
  destruct H as [I1 H1].
  split.
  - assumption.
  - apply OneTau. assumption.
Qed.

Lemma untaus_tau_tau2 : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    untaus (Tau t1) t2 -> untaus t1 t2.
Proof.
  intros E R t1 t2 H.
  destruct H as [I1 H1].
  inversion H1; subst.
  - split. assumption. assumption.
  - inversion I1.
Qed.

Lemma equiv_tau1 : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    Tau t1 ~ t2 -> t1 ~ t2.
Proof.
  intros E R.
  intros t1 t2 H.
  pfold.
  pinversion H.
  split.
  - split.
    + intros. apply H0. apply finite_taus_tau1. assumption.
    + intros. apply finite_taus_tau2. apply H0. assumption.
  - intros t1' t2' H2 H3.
    eapply H1.
    + apply untaus_tau_tau1. assumption.
    + assumption.
Qed.

Lemma equiv_tau2 : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    t1 ~ t2 -> Tau t1 ~ t2.
Proof.
  intros E R.
  intros t1 t2 H.
  pfold.
  pinversion H.
  split.
  - split.
    + intros. apply H0. apply finite_taus_tau2. assumption.
    + intros. apply finite_taus_tau1. apply H0. assumption.
  - intros t1' t2' H2 H3.
    eapply H1.
    + apply untaus_tau_tau2. assumption.
    + assumption.
Qed.

Lemma untaus_equiv : forall (E : Type -> Type) (R : Type) (t t' : itree E R), untaus t t' -> t ~ t'.
Proof.
  intros E R.
Admitted.

Lemma finite_taus_equiv : forall (E : Type -> Type) (R : Type) (t1 t2 : itree E R),
    t1 ~ t2 -> finite_taus t1 -> finite_taus t2.
Proof.
  intros E R t1 t2 H1 H2.
  destruct H2 as [t1' [I H]].
  generalize dependent t2.
  induction H; intros t2 H1.
  - apply IHuntaus'. apply equiv_tau1. assumption.
  - pinversion H1.
    apply H.
    destruct t1'.
    + exists (Ret r). split. simpl; auto. apply NoTau.
    + exists (Vis e k). split. simpl; auto. apply NoTau.
    + inversion I.
Qed.

Lemma finite_taus_bind : forall E R S (t1 t2 : itree E R) (f : R -> itree E S),
    t1 ~ t2 -> finite_taus (bind t1 f) -> finite_taus (bind t2 f).
Proof.
  intros E R S t1 t2 f Hequiv Hfin.
  assert (finite_taus t1). eapply finite_taus_bind_inv1. apply Hfin.
  assert (finite_taus t2). eapply finite_taus_equiv; eauto.
Admitted.





Lemma eutt_bind_hom1 : forall {E R S} (t1 t2 : itree E R) (f : R -> itree E S),
    t1 ~ t2 -> (bind t1 f) ~ (bind t2 f).
Proof.
Admitted.
