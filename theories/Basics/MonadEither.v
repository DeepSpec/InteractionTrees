(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Tacs
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Monad.

Import CatNotations.
Import MonadNotation.
Import RelNotations.
Local Open Scope cat_scope.
Local Open Scope monad_scope.

Definition eitherT (exn: Type) (m: Type -> Type) (A: Type) : Type :=
  m (sum exn A).
Definition either (exn A : Type) : Type :=
  sum exn A.

Section Monad_Either.
  Variable m : Type -> Type.
  Variable exn : Type.
  Context {EqmRm : EqmR m}.
  Context {Mm: Monad m}.
  Context {EqmROKm : EqmR_OK m}.
  Context {MLm: EqmRMonad m}.

  Notation eitherT := (eitherT exn m).

  Global Instance Monad_eitherT : Monad eitherT
    := {|
        ret _ a := ret (inr a)
        ; bind _ _ t k :=
            bind (m := m) t
                 (fun ma =>
                    match ma with
                    | inl e => ret (inl e)
                    | inr a => k a
                    end)
      |}.

  (* NOTE: For now we work with [eq] over the exception type. We might be able to generalize *)
  Global Instance Eqm_eitherT : EqmR eitherT :=
    {| eqmR := fun _ _ R => eqmR (sum_rel eq R) |}.

  Ltac unfold_either := unfold eqmR, Eqm_eitherT, eitherT in *.

  Lemma sum_eq_eq {A B : Type}
    : @eq A ⊕ @eq B ≡ eq.
  Proof.
    split; intros!; [invn sum_rel; auto | subst; reflexivity].
  Qed.

  Global Instance EqMProps_eitherT : EqmR_OK eitherT.
  Proof with unfold_either.
    constructor...
    - intros!; reflexivity.
    - intros!; symmetry; auto.
    - intros!; etransitivity; eauto.
    - intros.
      rewrite <- (eq_id_r eq), sum_compose.
      eapply eqmR_rel_trans; eauto.
    - intros!; split; intros!.
      + (* TODO: Rewrite fails here for a reason unbeknownst to me.
           See https://coq.discourse.group/t/confused-with-a-failure-of-a-generalized-rewrite/783
         *)
        apply (eqmR_lift_transpose _ (@eq exn ⊕ R)).
        rewrite transpose_sum, transpose_sym; auto.
      + rewrite <- transpose_sym, <- transpose_sum; auto.
        apply eqmR_lift_transpose; auto.
    - (* TODO: Define a better intro tactic in the style of Chargueraud or Boutiller *)
      intros ? ? ? ? EQ1 ? ? EQ2 ? ? EQ3; split; intros EQR.
      + rewrite <- EQ1.
        rewrite sum_eq_eq in EQ2.
        rewrite sum_eq_eq in EQ3.
        rewrite <- EQ2, <- EQ3; auto.
      + rewrite sum_eq_eq in EQ2.
        rewrite sum_eq_eq in EQ3.
        rewrite EQ1, EQ2, EQ3; auto.
    - intros!.
      (* TODO: Be able to rewrite ⊑ ? *)
      eapply eqmR_Proper_mono; eauto.
      typeclasses eauto.
  Qed.

  Instance MonadLaws_eitherT : EqmRMonad eitherT.
  Proof with unfold_either.
    constructor...
    - cbn; split; intros H.
      + rewrite <- eqmR_ret; auto.
      + rewrite <- eqmR_ret in H; auto; invn sum_rel; auto.
    - cbn.
      intros; intros ? ? EQ1 ? ? EQ2.
      (* TODO: Why does this rewrite fail? *)
      Fail setoid_rewrite EQ1.
      eapply eqmR_Proper_bind; [auto | apply EQ1 |].
      intros [] [] EQ3; invn sum_rel; auto.
      apply eqmR_ret; auto.
    - intros!; cbn.
      apply eqmR_bind_ret_l with (RA := @eq exn ⊕ RA); auto.
      intros!; invn sum_rel; eauto.
      apply eqmR_ret; auto.
    - intros!; cbn.
      match goal with
        |- eqmR ?RA _ ?ma => generalize (eqmR_bind_ret_r m RA ma ma_OK)
      end.
      intros EQ.
      (* TODO: Why can't I rewrite EQ here?? *)
      (* Even simpler case: *)
      (* assert (eqmR (eq ⊕ RA) ma ma). *)
      (* This loops *)
      (* rewrite <- EQ. *)
      (* Instead we go the hard way, but I'm not sure if it's necessary or something missing in our setup *)
      setoid_rewrite <- eq_id_l.
      apply eqmR_rel_trans with (mb := y <- ma;; ret y); [auto | | auto].
      apply eqmR_Proper_bind with (RA := eq ⊕ RA); auto.
      (* apply eqmR_Proper_bind with (RA := eq); auto. *)
      intros [] [] EQ'; invn sum_rel; auto.
      apply eqmR_ret; auto.
      apply eqmR_ret; auto.
      (* ??? *)
      admit.
    - admit.
 Admitted.

End Monad_Either.

Section Iter_Either.

  Variable M : Type -> Type.
  Variable exn : Type.
  Context {EQM : EqM M}.
  Context {HM: Monad M}.
  Context {HEQP: @EqMProps M HM EQM}.
  Context {ML: @MonadLaws M EQM HM}.
  Context {IM: MonadIter M}.
  Context {CM: Iterative (Kleisli M) sum}.

  Definition iso {a b:Type} (Aab : exn + (a + b)) : (a  + (exn + b)) :=
    match Aab with
    | inl A => inr (inl A)
    | inr (inl a) => inl a
    | inr (inr b) => inr (inr b)
    end.

  Definition internalize {a b:Type} (f : Kleisli (eitherT exn M) a b) : Kleisli M a (exn + b) := f.

  Global Instance Iter_eitherT : MonadIter (eitherT exn M) :=
    fun (b a: Type) (f: a -> M (exn + (a + b))) x =>
      iter ((internalize f) >>> (pure iso)) x.

  Instance proper_internalize {a b}: Proper (eq2 ==> eq2) (@internalize a b).
  intros x y H o; apply H.
  Qed.

  Global Instance Proper_Iter_eitherT : forall a b, @Proper (Kleisli (eitherT exn M) a (a + b) -> (Kleisli (eitherT exn M) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    intros A B x y H a.
    apply iterative_proper_iter.
    apply cat_eq2_r.
    rewrite H; reflexivity.
  Qed.

  Global Instance IterUnfold_eitherT : IterUnfold (Kleisli (eitherT exn M)) sum.
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

  Global Instance IterNatural_eitherT : IterNatural (Kleisli (eitherT exn M)) sum.
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

  Global Instance IterDinatural_eitherT : IterDinatural (Kleisli (eitherT exn M)) sum.
  Proof.
    destruct CM.
    unfold IterDinatural.
    intros A B C f g a.
    unfold iter, Iter_eitherT. cbn.
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

  Global Instance IterCodiagonal_eitherT : IterCodiagonal (Kleisli (eitherT exn M)) sum.
  Proof.
    destruct CM.
    unfold IterCodiagonal.
    intros a b f o.
    unfold iter, Iter_eitherT.
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

  Global Instance Iterative_eitherT : Iterative (Kleisli (eitherT exn M)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

End Iter_Either.
