From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

Import CatNotations.
Import MonadNotation.
Local Open Scope cat_scope.
Local Open Scope cat.
Local Open Scope monad_scope.

Definition eitherT (exn: Type) (M: Type -> Type) (a: Type) : Type :=
  M (sum exn a).
Definition either (exn a : Type) : Type :=
  sum exn a.

Section Functor_Either.
  Global Instance Functor_eitherT {M} {Fm : Functor M} (exn: Type) : Functor (eitherT exn M)
    := {|
        fmap _ _ f :=  fmap (fun ma => match ma with
                                    | inl e => inl e
                                    | inr a => inr (f a)
                                    end)
      |}.

End Functor_Either.

Section Monad_Either.
  Variable M : Type -> Type.
  Variable exn : Type.
  Context {EQM : EqM M}.
  Context {HM: Monad M}.
  Context {HEQP: @EqMProps M _ EQM}.
  Context {ML: @MonadLaws M _ HM}.

  Global Instance Monad_eitherT : Monad (eitherT exn M)
    := {|
        ret _ a := ret (inr a)
        ; bind _ _ t k :=
            bind (m := M) t
                 (fun ma =>
                    match ma with
                    | inl e => ret (inl e)
                    | inr a => k a
                    end)
      |}.

  Global Instance EqM_eitherTM : EqM (eitherT exn M) := fun _ => eqm (m := M).

  Global Instance EqMProps_eitherTM : @EqMProps _ _ EqM_eitherTM.
  Proof.
  constructor.
  - repeat red; reflexivity.
  - repeat red; intros x y; cbn; symmetry; auto.
  - repeat red; intros x y z; cbn; etransitivity; eauto.
  Qed.

  Instance MonadLaws_eitherTM : @MonadLaws (eitherT exn M) _ _.
  Proof.
  constructor.
  - cbn. intros a b f x.
    repeat red.
    rewrite bind_ret_l; cbn.
    reflexivity.
  - cbn; intros a x. unfold eitherT in x.
    unfold eqm, EqM_eitherTM.
    match goal with
      |- _ ≈ ?h => rewrite <- (bind_ret_r _ h) at 2
    end.
    apply Proper_bind; [reflexivity | intros [b | m]; reflexivity].
  - cbn. intros a b c x f g; cbn.
    rewrite bind_bind. do 2 red.
    apply Proper_bind; [reflexivity | intros [? | m]].
    + rewrite bind_ret_l; reflexivity.
    + reflexivity.
  - cbn; intros a b x y EQ x' y' H'; cbn in *.
    do 2 red; apply Proper_bind; [auto | intros [? | ?]]; [reflexivity | apply H'].
  Qed.

End Monad_Either.

Section Iter_Either.

  Variable M : Type -> Type.
  Variable exn : Type.
  Context {EQM : EqM M}.
  Context {HM: Monad M}.
  Context {HEQP: @EqMProps M _ EQM}.
  Context {ML: @MonadLaws M _ HM}.
  Context {IM: MonadIter M}.
  Context {CM: Iterative (Kleisli M) sum}.

  Definition iso {a b:Type} (Aab : exn + (a + b)) : (a  + (exn + b)) :=
    match Aab with
    | inl A => inr (inl A)
    | inr (inl a) => inl a
    | inr (inr b) => inr (inr b)
    end.

  Definition internalize {a b:Type} (f : Kleisli (eitherT exn M) a b) : Kleisli M a (exn + b) := f.

  Global Instance Iter_eitherTM : MonadIter (eitherT exn M) :=
    fun (b a: Type) (f: a -> M (exn + (a + b))) x =>
      iter ((internalize f) >>> (pure iso)) x.

  Instance proper_internalize {a b}: Proper (eq2 ==> eq2) (@internalize a b).
  intros x y H o; apply H.
  Qed.

  Global Instance Proper_Iter_eitherTM : forall a b, @Proper (Kleisli (eitherT exn M) a (a + b) -> (Kleisli (eitherT exn M) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    intros A B x y H a.
    apply iterative_proper_iter.
    apply cat_eq2_r.
    rewrite H; reflexivity.
  Qed.

  Global Instance IterUnfold_eitherTM : IterUnfold (Kleisli (eitherT exn M)) sum.
  Proof.
    intros A B f a; cbn.
    unfold CategoryOps.iter, Iter_Kleisli.
    rewrite iter_monad_to_cat.
    rw_pointed_l iter_unfold.
    unfold cat, Cat_Kleisli.
    do 2 red.
    rewrite bind_bind.
    apply Proper_bind.
    + reflexivity.
    + intros [xA | [xa | xb]]; unfold pure; rewrite bind_ret_l; reflexivity.
  Qed.

  Global Instance IterNatural_eitherTM : IterNatural (Kleisli (eitherT exn M)) sum.
  Proof.
    destruct CM.
    intros A B C f g a; cbn.
    setoid_rewrite iterative_natural.
    apply iterative_proper_iter; intros a'.
    unfold cat, Cat_Kleisli.
    unfold internalize; cbn.
    rewrite! bind_bind.
    apply Proper_bind; [reflexivity |].
    intros [xA | [xa | xb]]; unfold pure; cbn; rewrite !bind_ret_l; cbn; unfold cat, Cat_Kleisli; cbn.
    - rewrite bind_ret_l; cbn; reflexivity.
    - unfold id_, Id_Kleisli, pure; rewrite bind_bind, !bind_ret_l; reflexivity.
    - cbn; rewrite bind_bind.
      apply Proper_bind; [reflexivity |].
      intros [? | ?]; rewrite bind_ret_l; reflexivity.
  Qed.

  Lemma iter_dinatural_helper:
    forall (a b c : Type) (f : Kleisli (eitherT exn M) a (b + c)) (g : Kleisli (eitherT exn M) b (a + c)),
      internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_.
  Proof.
    destruct CM.
    intros a b c f g o.
    unfold cat, Cat_Kleisli, internalize; cbn.
    repeat rewrite bind_bind; cbn.
    unfold pure; cbn.
    apply Proper_bind; [reflexivity | intros [xA | [xa | xb]]]; cbn.
    - rewrite !bind_ret_l; reflexivity.
    - rewrite bind_ret_l; reflexivity.
    - rewrite !bind_ret_l; reflexivity.
  Qed.

  Global Instance IterDinatural_eitherTM : IterDinatural (Kleisli (eitherT exn M)) sum.
  Proof.
    destruct CM.
    unfold IterDinatural.
    intros A B C f g a.
    unfold iter, Iter_eitherTM. cbn.
    eapply transitivity.
    eapply iterative_proper_iter.
    apply iter_dinatural_helper.
    rewrite iterative_dinatural.
    cbn.
    unfold cat, Cat_Kleisli.
    rewrite bind_bind.
    unfold internalize. cbn.
    do 2 red.
    apply Proper_bind.
    - reflexivity.
    - unfold pure; cbn; intros [xA | [xa | xb]]; cbn.
      + rewrite bind_ret_l; cbn; reflexivity.
      + rewrite bind_ret_l; cbn.
        eapply iterative_proper_iter.
        intros ?; rewrite !bind_bind.
        apply Proper_bind; [reflexivity | intros [|[|]]]; cbn; rewrite !bind_ret_l; try reflexivity.
      + rewrite bind_ret_l; cbn.
        reflexivity.
  Qed.

  Global Instance IterCodiagonal_eitherTM : IterCodiagonal (Kleisli (eitherT exn M)) sum.
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
    unfold cat, Cat_Kleisli; cbn; rewrite !bind_bind; cbn.
    apply Proper_bind; [reflexivity | intros [| [|]]].
    unfold pure; rewrite !bind_ret_l; reflexivity.
    unfold pure; cbn; rewrite !bind_ret_l; reflexivity.
    unfold pure; cbn; rewrite !bind_ret_l; reflexivity.
  Qed.

  Global Instance Iterative_eitherTM : Iterative (Kleisli (eitherT exn M)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

End Iter_Either.

(* Section Interpretable_Either. *)

(*   Variable M : Type -> Type. *)
(*   Variable exn : Type. *)
(*   Context {EQM : EqM M}. *)
(*   Context {HM: Monad M}. *)
(*   Context {HEQP: @EqMProps M _ EQM}. *)
(*   Context {ML: @MonadLaws M _ HM}. *)
(*   Context {IM: MonadIter M}. *)
(*   Context {CM: Iterative (Kleisli M) sum}. *)

