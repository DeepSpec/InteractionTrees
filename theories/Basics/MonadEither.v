From Coq Require Import
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad
     EitherMonad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Section Either.
  Variable M : Type -> Type.
  Variable A : Type.
  Context {EQM : EqM M}.
  Context {HM: Monad M}.
  Context {HEQP: @EqMProps M _ EQM}.
  Context {ML: @MonadLaws M _ HM}.

  Global Instance EqM_eitherTM : EqM (eitherT A M).
  Proof.
    intros ? [a] [b].
    exact (eqm a b).
  Defined.

  Global Instance EqMProps_eitherTM : @EqMProps (eitherT A M) _ EqM_eitherTM.
  Proof.
  constructor.
  - intros [x]; cbn; reflexivity.
  - intros [x] [y]; cbn; symmetry; auto.
  - intros [x] [y] [z]; cbn; etransitivity; eauto.
  Qed.

  Instance MonadLaws_eitherTM : @MonadLaws (eitherT A M) _ _.
  Proof.
  constructor.
  - cbn. intros a b f x; destruct (f x) eqn:EQ.
    repeat red.
    rewrite bind_ret_l, EQ; cbn.
    reflexivity.
  - cbn. intros a [x]; cbn.
    match goal with
      |- _ ≈ ?h => rewrite <- (bind_ret_r _ h) at 2
    end.
    apply Proper_bind; [reflexivity | intros [b | m]; reflexivity].
  - cbn. intros a b c [x] f g; cbn.
    rewrite bind_bind.
    apply Proper_bind; [reflexivity | intros [? | m]].
    + rewrite bind_ret_l; reflexivity.
    + reflexivity.
  - cbn; intros a b [x] [y] EQ x' y' H'; cbn in *.
    apply Proper_bind; [auto | intros [? | ?]]; [reflexivity |].
    specialize (H' a0).
    destruct (x' a0), (y' a0); cbn in *; auto.
  Qed.

  Context {IM: Iter (Kleisli M) sum}.
  Context {CM: Iterative (Kleisli M) sum}.

  Definition iso {a b:Type} (Aab : A + (a + b)) : (a  + (A + b)) :=
    match Aab with
    | inl A => inr (inl A)
    | inr (inl a) => inl a
    | inr (inr b) => inr (inr b)
    end.

  Definition internalize {a b:Type} (f : Kleisli (eitherT A M) a b) : Kleisli M a (A + b) :=
    fun x => let '(mkEitherT y) := f x in y.

  Global Instance Iter_eitherTM : Iter (Kleisli (eitherT A M)) sum :=
    fun (a b: Type) (f: a -> (eitherT A M (a + b))) x =>
      mkEitherT (iter ((internalize f) >>> (pure iso)) x).

  Instance proper_internalize {a b}: Proper (eq2 ==> eq2) (@internalize a b).
  intros x y H o; specialize (H o).
  unfold internalize; destruct (x o), (y o).
  apply H.
  Qed.

  Global Instance Proper_Iter_eitherTM : forall a b, @Proper (Kleisli (eitherT A M) a (a + b) -> (Kleisli (eitherT A M) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    intros a b x y H a0.
    apply iterative_proper_iter.
    apply cat_eq2_r.
    rewrite H; reflexivity.
 Qed.

  Global Instance IterUnfold_eitherTM : IterUnfold (Kleisli (eitherT A M)) sum.
  Proof.
    destruct CM.
    intros a b f o.
    cbn; destruct (f o) as [e] eqn:EQ; cbn.
    unfold cat, Cat_Kleisli.
    unfold iter, Iter_eitherTM.
    rewrite iterative_unfold.
    unfold cat, Cat_Kleisli.
    rewrite bind_bind.
    apply Proper_bind.
    + unfold internalize; rewrite EQ; reflexivity.
    + intros [xA | [xa | xb]]; unfold pure; rewrite bind_ret_l; reflexivity.
  Qed.

  Global Instance IterNatural_eitherTM : IterNatural (Kleisli (eitherT A M)) sum.
  Proof.
    destruct CM.
    intros a b c f g o.
    cbn; destruct (f o) as [e] eqn:EQf; cbn.
    setoid_rewrite iterative_natural.
    apply iterative_proper_iter; intros a'.
    unfold cat, Cat_Kleisli.
    unfold internalize; destruct (f a') eqn:EQf'; cbn.
    rewrite! bind_bind.
    apply Proper_bind; [reflexivity |].
    intros [xA | [xa | xb]]; unfold pure; cbn; rewrite !bind_ret_l; cbn; unfold cat, Cat_Kleisli; cbn.
    - rewrite bind_ret_l; cbn; reflexivity.
    - unfold id_, Id_Kleisli, pure; rewrite bind_ret_l; reflexivity.
    - destruct (g xb); cbn; rewrite bind_bind.
      apply Proper_bind; [reflexivity |].
      intros [? | ?]; rewrite bind_ret_l; reflexivity.
  Qed.

  Lemma iter_dinatural_helper:
    forall (a b c : Type) (f : Kleisli (eitherT A M) a (b + c)) (g : Kleisli (eitherT A M) b (a + c)),
      internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_.
  Proof.
    destruct CM.
    intros a b c f g o.
    unfold cat, Cat_Kleisli, internalize; cbn.
    repeat rewrite bind_bind.
    destruct (f o) as [fo] eqn: EQ; cbn.
    unfold pure; cbn.
    apply Proper_bind; [reflexivity | intros [xA | [xa | xb]]]; cbn.
    - rewrite !bind_ret_l; reflexivity.
    - destruct (g xa) as [gxa] eqn:EQ'; cbn.
      rewrite bind_ret_l; cbn; rewrite EQ'; reflexivity.
    - rewrite !bind_ret_l; reflexivity.
  Qed.

  Global Instance IterDinatural_eitherTM : IterDinatural (Kleisli (eitherT A M)) sum.
  Proof.
    destruct CM.
    unfold IterDinatural.
    intros a b c f g o.
    unfold iter, Iter_eitherTM. cbn.
    eapply transitivity.
    eapply iterative_proper_iter.
    apply iter_dinatural_helper.
    rewrite iterative_dinatural.
    cbn.
    unfold cat, Cat_Kleisli.
    rewrite bind_bind.
    unfold internalize. cbn.
    apply Proper_bind.
    - reflexivity.
    - unfold pure; cbn; intros [xA | [xa | xb]]; cbn.
      + rewrite bind_ret_l; cbn; reflexivity.
      + rewrite bind_ret_l; cbn.
        eapply iterative_proper_iter.
        intros ?; rewrite !bind_bind.
        destruct (g a0) eqn:EQ; cbn.
        apply Proper_bind; [reflexivity | intros [|[|]]]; cbn; rewrite !bind_ret_l; try reflexivity.
      + rewrite bind_ret_l; cbn.
        reflexivity.
  Qed.

  Global Instance IterCodiagonal_eitherTM : IterCodiagonal (Kleisli (eitherT A M)) sum.
  Proof.
    destruct CM.
    unfold IterCodiagonal.
    intros a b f o.
    unfold iter, Iter_eitherTM.
    cbn.
    eapply transitivity.
    eapply iterative_proper_iter.
    eapply Proper_cat_Kleisli; [| reflexivity].
    unfold internalize; cbn. reflexivity.
    eapply transitivity.

   eapply iterative_proper_iter.
   apply iterative_natural.
   rewrite iterative_codiagonal.
   eapply iterative_proper_iter.
   rewrite cat_assoc, bimap_case, cat_id_l, cat_id_r.
   unfold internalize.
   intros o'; cbn.
   unfold cat, Cat_Kleisli; rewrite !bind_bind; destruct (f o'); cbn.
   apply Proper_bind; [reflexivity | intros [| [|]]].
   unfold pure; rewrite !bind_ret_l; reflexivity.
   unfold pure; cbn; rewrite !bind_ret_l; reflexivity.
   unfold pure; cbn; rewrite !bind_ret_l; reflexivity.
  Qed.

  Global Instance Iterative_eitherTM : Iterative (Kleisli (eitherT A M)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

End Either.
