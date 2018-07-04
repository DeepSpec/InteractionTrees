Require Import Relations.
Require Import Eqdep.
Require Import Paco.paco.

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
    inversion H12; inversion H23; subst; try discriminate.
    + inversion H4. constructor.
    + inversion H6; subst.
      apply inj_pair2 in H7; subst.
      constructor.
      * intro x.
        specialize (H x); specialize (H5 x); pclearbot.
        right; eapply transitive_eutt; eauto.
        apply inj_pair2 in H8. (* Boo *)
        subst.
        auto.
Qed.
        
End EUTT.
