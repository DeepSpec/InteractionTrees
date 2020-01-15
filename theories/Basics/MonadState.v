(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

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

Section State.
  Variable M : Type -> Type.
  Variable S : Type.
  Context {EQM : EqM M}.
  Context {HM: Monad M}.
  Context {HEQP: @EqMProps M _ EQM}.
  Context {ML: @MonadLaws M _ HM}.

  Global Instance EqM_stateTM : EqM (stateT S M).
  Proof.
    exact (fun a => pointwise_relation _ eqm).
  Defined.

  Global Instance EqMProps_stateTM : @EqMProps (stateT S M) _ EqM_stateTM.
  Proof.
  constructor.
  - repeat red.
    reflexivity.
  - repeat red. intros. symmetry. apply H.
  - repeat red. intros. etransitivity; eauto. apply H.  apply H0.
  Qed.

  Instance MonadLaws_stateTM : @MonadLaws (stateT S M) _ _.
  Proof.
  constructor.
  - cbn. intros a b f x.
    repeat red.  intros s.
    rewrite bind_ret_l. reflexivity.
  - cbn. intros a x.
    repeat red. intros s.
    assert (EQM _ (bind (x s) (fun sa : S * a => ret (fst sa, snd sa))) (bind (x s) (fun sa => ret sa))).
    { apply Proper_bind. reflexivity. intros.  repeat red. destruct a0; reflexivity. }
    rewrite H.
    rewrite bind_ret_r. reflexivity.
  - cbn. intros a b c x f g.
    repeat red. intros s.
    rewrite bind_bind.
    apply Proper_bind.
    + reflexivity.
    + reflexivity.
  - repeat red. intros a b x y H x0 y0 H0 s.
    apply Proper_bind.
    + apply H.
    + repeat red.
      destruct a0.
      apply H0.
  Qed.

  Context {IM: Iter (Kleisli M) sum}.
  Context {CM: Iterative (Kleisli M) sum}.

  Definition iso {a b:Type} (sab : S * (a + b)) : (S * a) + (S * b) :=
    match sab with
    | (s, inl x) => inl (s, x)
    | (s, inr y) => inr (s, y)
    end.

  Definition iso_inv {a b:Type} (sab : (S * a) + (S * b)) : S * (a + b) :=
    match sab with
    | inl (s, a) => (s, inl a)
    | inr (s, b) => (s, inr b)
    end.

  Definition internalize {a b:Type} (f : Kleisli (stateT S M) a b) : Kleisli M (S * a) (S * b) :=
    fun (sa : S * a) => f (snd sa) (fst sa).

  Lemma internalize_eq {a b:Type} (f g : Kleisli (stateT S M) a b) :
    eq2 f g <-> eq2 (internalize f) (internalize g).
  Proof.
    split.
    - intros.
      repeat red. destruct a0.
      unfold internalize. cbn.  apply H.
    - intros.
      repeat red. intros.
      unfold internalize in H.
      specialize (H (a1, a0)).
      apply H.
  Qed.


  Lemma internalize_cat {a b c} (f : Kleisli (stateT S M) a b) (g : Kleisli (stateT S M) b c) :
    (internalize (f >>> g)) ⩯ ((internalize f) >>> (internalize g)).
  Proof.
    repeat red.
    destruct a0.
    cbn.
    unfold internalize.
    unfold cat, Cat_Kleisli.
    cbn.
    reflexivity.
  Qed.


  Lemma internalize_pure {a b c} (f : Kleisli (stateT S M) a b) (g : S * b -> S * c) :
    internalize f >>> pure g   ⩯   (internalize (f >>> (fun b s => ret (g (s,b))))).
  Proof.
    repeat red.
    destruct a0.
    unfold internalize, cat, Cat_Kleisli. cbn.
    apply Proper_bind; auto.
    - reflexivity.
    - repeat red.
      destruct a1.
      unfold pure. reflexivity.
  Qed.


  Global Instance Iter_stateTM : Iter (Kleisli (stateT S M)) sum.
  Proof.
    exact
      (fun (a b : Type) (f : a -> S -> M (S * (a + b))) (x:a) (s:S) =>
        iter ((internalize f) >>> (pure iso)) (s, x)).
  Defined.

  Global Instance Proper_Iter_stateTM : forall a b, @Proper (Kleisli (stateT S M) a (a + b) -> (Kleisli (stateT S M) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    repeat red.
    intros a b x y H a0 s.
    apply iterative_proper_iter.
    repeat red.
    destruct a1.
    cbn.
    apply Proper_bind.
    - apply H.
    - repeat red. destruct a2 as [s' [x1|y1]]; reflexivity.
 Qed.

  Global Instance IterUnfold_stateTM : IterUnfold (Kleisli (stateT S M)) sum.
  Proof.
  destruct CM.
  unfold IterUnfold.
  intros a b f.
  repeat red.
  intros a0 s.
  unfold cat, Cat_Kleisli.
  unfold iter, Iter_stateTM.
  rewrite iterative_unfold.  (* SAZ: why isn't iter_unfold exposed here? *)
  unfold cat, Cat_Kleisli.
  simpl.
  rewrite bind_bind.
  apply Proper_bind.
  + reflexivity.
  + repeat red. destruct a1 as [s' [x | y]]; simpl.
    * unfold pure. rewrite bind_ret_l.
      reflexivity.
    * unfold pure. rewrite bind_ret_l.
      reflexivity.
  Qed.

  Global Instance IterNatural_stateTM : IterNatural (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterNatural.
    intros a b c f g.
    repeat red.
    intros a0 s.
    setoid_rewrite iterative_natural.
    apply iterative_proper_iter.
    repeat red.
    destruct a1.
    unfold cat, Cat_Kleisli.
    cbn.
    rewrite! bind_bind.
    apply Proper_bind.
    - reflexivity.
    - repeat red. destruct a2 as [s' [x | y]]; simpl.
      + unfold pure. rewrite bind_ret_l.
        cbn. unfold cat, Cat_Kleisli. cbn.
        rewrite bind_bind.
        rewrite bind_ret_l.
        rewrite bind_ret_l.
        cbn.
        unfold id_, Id_Kleisli. unfold pure. rewrite bind_ret_l. reflexivity.
      + unfold pure. rewrite bind_ret_l.
        cbn. unfold cat, Cat_Kleisli. cbn.
        rewrite bind_bind.
        apply Proper_bind.
        * reflexivity.
        * repeat red. destruct a2.
          cbn.
          rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma internalize_pure_iso {a b c} (f : Kleisli (stateT S M) a (b + c)) :
    ((internalize f) >>> pure iso) ⩯ (fun sa => (bind (f (snd sa) (fst sa))) (fun sbc => ret (iso sbc))).
  Proof.
    reflexivity.
  Qed.


  Lemma eq2_to_eqm : forall a b (f g : Kleisli (stateT S M) a b) (x:a) (s:S),
      eq2 f g ->
      eqm (f x s) (g x s).
  Proof.
    intros a b f g x s H.
    apply H.
  Qed.


  Lemma iter_dinatural_helper:
    forall (a b c : Type) (f : Kleisli (stateT S M) a (b + c)) (g : Kleisli (stateT S M) b (a + c)),
      internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_.
  Proof.
    destruct CM.
    intros a b c f g.
    repeat red.
    destruct a0.
    unfold cat, Cat_Kleisli, internalize.
    cbn.
    repeat rewrite bind_bind.
    apply Proper_bind.
    - reflexivity.
    - repeat red.
      destruct a1 as [s' [x | y]].
      + unfold pure.
        rewrite bind_ret_l.
        unfold case_, Case_Kleisli, Function.case_sum.
        reflexivity.
      + unfold pure. rewrite bind_ret_l.
        unfold case_, Case_Kleisli, Function.case_sum.
          cbn.
          rewrite bind_ret_l. reflexivity.
  Qed.


  Global Instance IterDinatural_stateTM : IterDinatural (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterDinatural.
    repeat red.
    intros a b c f g a0 a1.
    unfold iter, Iter_stateTM.
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
    - repeat red.
      destruct a2 as [s [x | y]].
      + unfold pure.
        rewrite bind_ret_l.
        cbn.
        eapply iterative_proper_iter.
        repeat red.
        destruct a2.
        cbn. rewrite! bind_bind.
        apply Proper_bind.
        * reflexivity.
        * repeat red.
          destruct a2 as [s' [x' | y]].
          ** cbn.  rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum.
             reflexivity.
          ** cbn.  rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum.
             rewrite bind_ret_l. reflexivity.
      + unfold pure.
        rewrite bind_ret_l.
        cbn.
        reflexivity.
    Qed.


  Global Instance IterCodiagonal_stateTM : IterCodiagonal (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterCodiagonal.
    intros a b f.
    unfold iter, Iter_stateTM.
    repeat red.
    intros.
    eapply transitivity.
    eapply iterative_proper_iter.
    eapply Proper_cat_Kleisli.

    assert (internalize (fun (x:a) (s:S) => iter (internalize f >>> pure iso) (s, x))
                       ⩯
                       iter (internalize f >>> pure iso)).
    { repeat red.
      destruct a2.
      unfold internalize.
      cbn.  reflexivity.
    }
   apply H.
   reflexivity.
   eapply transitivity.

   eapply iterative_proper_iter.
   apply iterative_natural.
   rewrite iterative_codiagonal.
   eapply iterative_proper_iter.
   rewrite internalize_cat.
   (* SAZ This proof can probably use less unfolding *)
   repeat red.
   destruct a2.
   unfold cat, Cat_Kleisli. cbn.
   repeat rewrite bind_bind.
   unfold internalize, pure.
   cbn.
   apply Proper_bind.
    - reflexivity.
    - repeat red.
      destruct a3 as [s' [x | [y | z]]].
      + rewrite bind_ret_l.
        cbn. unfold id_, Id_Kleisli, pure.
        rewrite bind_ret_l.
        unfold cat, Cat_Kleisli.
        rewrite bind_bind.
        rewrite bind_ret_l.
        cbn.  unfold inl_, Inl_Kleisli, pure.
        rewrite bind_ret_l. reflexivity.
      + rewrite bind_ret_l.
        cbn.
        rewrite bind_ret_l.
        unfold cat, Cat_Kleisli.
        rewrite bind_bind, bind_ret_l. cbn.
        unfold inr_, Inr_Kleisli, pure.
        rewrite bind_ret_l. reflexivity.
      + rewrite bind_ret_l.
        cbn.
        rewrite bind_ret_l.
        unfold cat, Cat_Kleisli.
        rewrite bind_bind, bind_ret_l. cbn.
        unfold inr_, Inr_Kleisli, pure.
        rewrite bind_ret_l.
        reflexivity.
  Qed.

  Global Instance Iterative_stateTM : Iterative (Kleisli (stateT S M)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

End State.
