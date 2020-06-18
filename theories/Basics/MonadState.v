(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.CategoryMonad
     Basics.HeterogeneousRelations
     Basics.Monad
     Basics.Tacs
     Basics.Typ
.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Import RelNotations.
Local Open Scope relationH_scope.
Local Open Scope cat_scope.
Local Open Scope cat.

Section State.
  Variable S : typ.

  Definition state (s : typ) (a : typ) : typ :=
    s ~~> prod_typ s a.

  Definition eqmR_state (A B : typ) (R : relationH A B) :=
    (fun (p : state S A × state S B) => forall (s : S),
      (* Weak equivalence on R *)
      ((forall (a : A), snd (fst p @ s) == a ->
        (exists (b : B), R @ (a, b) /\ snd (snd p @ s) == b)) /\
        (forall (b : B), snd (snd p @ s) == b ->
        (exists (a : A), R @ (a, b) /\ snd (fst p @ s) == a))) /\
      (* Equivalence on resulting state *)
      ((relationH_of_typ S) @ (fst (fst p @ s), fst (snd p @ s)))).

  Lemma equal_typ {A : typ} {x : A} : x == x. reflexivity. Qed.

  Program Instance EqmR_state : EqmR (state S) :=
    {
      eqmR := eqmR_state
    }.
  Next Obligation.
    repeat intro. destruct x2, y. cbn in *. destruct H.
    unfold eqmR_state. cbn. split.
    - intros.
      specialize (H1 s).
      specialize (H s s).
      assert (s == s) by reflexivity.
      specialize (H H2). specialize (H0 s s H2).
      destruct (t @ s). destruct (t0 @ s). destruct (t1 @ s). destruct (t2 @ s).
      destruct H, H0. intuition; cbn in *.
      intuition. edestruct H1; eauto. rewrite H5 in H8.
      destruct H8. exists (x2). split; eauto. rewrite <- H4; auto.
      edestruct H7; eauto. rewrite H5 in H8. destruct H8.
      exists x2; split; auto. rewrite <- H9; symmetry; auto.
      rewrite <- H0. rewrite <- H6. symmetry; auto.
    - intros.
      specialize (H1 s).
      specialize (H s s).
      assert (s == s) by reflexivity.
      specialize (H H2). specialize (H0 s s H2).
      destruct (t @ s). destruct (t0 @ s). destruct (t1 @ s). destruct (t2 @ s).
      destruct H, H0. intuition; cbn in *.
      intuition. edestruct H1. symmetry; eauto.
      rewrite H5 in H8.
      destruct H8. exists (x2). split; eauto. rewrite H4; auto.
      edestruct H7; eauto. symmetry; eauto.
      rewrite H5 in H8. destruct H8.
      exists x2; split; auto. rewrite <- H9; auto.
      symmetry; auto. rewrite H0. rewrite <- H6. symmetry; auto.
  Qed.
  Next Obligation.
    split; repeat intro. cbn in *. rewrite H0.
    - unfold eqmR_state in H.
      specialize (H x0).
      destruct H. destruct H. setoid_rewrite H0 in H.
      setoid_rewrite H0 in H2.
      setoid_rewrite H0 in H1.
      cbn in *. destruct (x @ y0) eqn: Hx. destruct (y @ y0) eqn: Hy. cbn in *.
      split. apply H1. specialize (H2 t2).
      specialize (H2 equal_typ).
      edestruct H2 as (? & ? & ?). rewrite H4. auto.
    - unfold eqmR_state in H.
      specialize (H s s equal_typ).
      cbn in *. destruct (x @ s) eqn: Hx. destruct (y @ s) eqn: Hy. cbn in *.
      destruct H. split. split.
      intros. exists t0. split; symmetry; auto.
      intros. exists t2; split; auto. auto.
  Qed.

  Instance EqmR_OK_state : EqmR_OK (state S).
  constructor.
  - intros. repeat intro. unfold ReflexiveH in H.
    cbn. split. split. intros. exists a0. split; eauto.
    intros. eauto. reflexivity.
  - intros. repeat intro. unfold SymmetricH in H.
    destruct p. cbn. cbn in H0.
    unfold eqmR_state in H0. cbn in H0.
    specialize (H0 s).
    destruct H0. destruct H0. split. split.
    intros. edestruct H2. apply H3. destruct H4.
    edestruct H0. apply H5. destruct H6. exists x. split; auto.
    specialize (H (x, a) H4). cbn in H. auto.
    intros. edestruct H0. apply H3. destruct H4.
    edestruct H2. apply H5. destruct H6. exists x. split; auto.
    specialize (H (b, x) H4). cbn in H. auto.
    symmetry; auto.
  - intros. repeat intro. unfold TransitiveH in H.
    destruct p, q. cbn in H2. red in H2.
    specialize (H2 s s equal_typ).
    cbn in *. unfold eqmR_state in *. cbn in *.
    specialize (H0 s). specialize (H1 s).
    destruct H2. destruct (t @ s), (t0 @ s), (t1 @ s), (t2 @ s).
    cbn in *. destruct H0. destruct H0. destruct H1. destruct H1.
    split. split.
    + intros. edestruct H1. symmetry; eauto.
      destruct H9. edestruct H0. apply H8. destruct H11.
      edestruct H5. apply H12. destruct H13. cbn in *.
      edestruct H7. apply H10. destruct H15. exists x. split; auto.
      rewrite H12 in H9. specialize (H (a, x0) (x0, x) H11 H9).
      cbn in H. specialize (H equal_typ). auto.
    + intros. edestruct H7; eauto. destruct H9.
      edestruct H1; eauto. destruct H11.
      edestruct H5; eauto. destruct H13. edestruct H0; eauto.
      destruct H15. rewrite <- H10 in H9.
      specialize (H (x1, t8) (t8, b) H13 H9).
      cbn in H.
      exists x1. split; intuition.
    + rewrite H4. rewrite H2. auto.
  - intros. cbn in *. unfold eqmR_state in *.
    intros. specialize (H s). specialize (H0 s).
    destruct H. destruct H. destruct H0. destruct H0. cbn in *.
    split. split.
    + intros. specialize (H a H5). edestruct H as (? & ? & ?); clear H.
      destruct (ma @ s), (mb @ s), (mc @ s). cbn in *.
      specialize (H2 _ H7). edestruct H2 as (? & ? & ?); clear H2.
      specialize (H0 _ H7). edestruct H0 as (? & ? & ?); clear H0.
      exists x1. split; intuition. exists x. split; intuition.
    + intros. specialize (H4 _ H5). edestruct H4 as (? & ? & ?); clear H4.
      destruct (ma @ s), (mb @ s), (mc @ s). cbn in *.
      specialize (H2 _ H7). edestruct H2 as (? & ? & ?); clear H2.
      exists x0. split; auto. exists x. split; auto.
    + destruct (ma @ s), (mb @ s), (mc @ s). cbn in *.
      rewrite H1. auto.
  - intros. split; repeat intro.
    + cbn in H. unfold eqmR_state in H. cbn in *.
      specialize (H s). destruct H. destruct H.
      destruct (x @ s), (y @ s); cbn in *.
      split. split.
      * intros. specialize (H1 _ H2). edestruct H1 as (? & ? & ?).
        exists x0. split; auto.
      * intros. specialize (H _ H2). edestruct H as (? & ? & ?).
        exists x0. split; auto.
      * symmetry; auto.
    + cbn in H. unfold eqmR_state in H. cbn in *.
      specialize (H s). destruct H. destruct H.
      destruct (x @ s), (y @ s); cbn in *.
      split. split.
      * intros. specialize (H1 _ H2). edestruct H1 as (? & ? & ?).
        exists x0. split; auto.
      * intros. specialize (H _ H2). edestruct H as (? & ? & ?).
        exists x0. split; auto.
      * symmetry; auto.
  - repeat intro. cbn in *. unfold eqmR_state.
    split; repeat intro. cbn in H0.
    + specialize (H0 s). cbn. destruct (x0 @ s), (y0 @ s). cbn in *.
      red in H. destruct H. red in H, H1.
      destruct H0. destruct H0.
      split. split.
      * intros. specialize (H0 _ H4). edestruct H0 as (? & ? & ?); clear H0.
        exists x1. split; auto.
      * intros. specialize (H3 _ H4). edestruct H3 as (? & ? & ?); clear H0.
        exists x1. split; auto.
      * auto.
    + specialize (H0 s). cbn in *. destruct (x0 @ s), (y0 @ s). cbn in *.
      red in H. destruct H. red in H, H1.
      destruct H0. destruct H0.
      split. split.
      * intros. specialize (H0 _ H4). edestruct H0 as (? & ? & ?); clear H0.
        exists x1. split; auto.
      * intros. specialize (H3 _ H4). edestruct H3 as (? & ? & ?); clear H0.
        exists x1. split; auto.
      * auto.
  - repeat intro. cbn in *. unfold eqmR_state in *.
    specialize (H0 s).
    destruct H0. destruct H0. cbn in *.
    destruct (x0 @ s), (y0 @ s).
    cbn in *.
    split. split.
    + intros. specialize (H0 _ H3). edestruct H0 as (? & ? & ?); clear H0.
      exists x1. split; auto.
    + intros. specialize (H2 _ H3). edestruct H2 as (? & ? & ?); clear H0.
      exists x1. split; auto.
    + auto.
  Qed.

  Lemma ret_stateT_P:
    forall (a : typ) (x : a),
      Proper (equalE S ==> equalE (S × a)) (fun s : S => (s, x)).
  Proof.
    intros a x.
    repeat intro. rewrite H. reflexivity.
  Qed.

  Lemma ret_stateT_P':
    forall a : typ,
      Proper (equalE a ==> equalE (state S a))
              (fun x : a => (-=->!) (fun s : S => (s, x)) (ret_stateT_P a x)).
  Proof.
    intros a.
    repeat intro. cbn. split; auto.
  Qed.

  Lemma bind_stateT_P:
    forall (a b : typ) (f : a -=-> state S b) (sa : state S a),
      Proper (equalE S ==> equalE (S × b))
        (fun s : S => (f @ snd (sa @ s)) @ (fst (sa @ s))).
  Proof.
    intros a b f sa.
    repeat intro. rewrite H. reflexivity.
  Qed.

  Lemma bind_stateT_P2:
    forall (a b : typ) (f : a -=-> state S b),
      Proper (equalE (state S a) ==> equalE (state S b))
              (fun sa : state S a =>
                (-=->!) (fun s : S => (f @ snd (sa @ s)) @ (fst (sa @ s))) (bind_stateT_P a b f sa)).
  Proof.
    intros a b f.
    repeat intro. cbn. rewrite H, H0. split; reflexivity.
  Qed.

  Instance MonadState : Monad typ_proper (state S).
  split.
  - intros. refine (-=->! (fun x => _) (ret_stateT_P' a)).
  - intros. refine (-=->! (fun sa => _) (bind_stateT_P2 a b f)).
  Defined.

  Definition state_prop {A : typ} (ma : state S A) :=
    (fun a : A => exists s s', ma @ s == (s', a)).

  Program Definition const_state {A : typ} (s : S) (a : A) : S -=-> (S × A) :=
    -=->! (fun s => (s, a)) _.
  Next Obligation.
    repeat intro. split; cbn; eauto. reflexivity.
  Qed.

  Lemma mayRet_state {A:typ} (ma : state S A) (a : A) :
    (exists s s' : S, (ma @ s) == (s', a)) <->
    mayRet (state S) ma @ a.
  Proof.
    split. intro.
    - cbn. intros. cbn in *. unfold eqmR_state in EQ.
      cbn in *.
      edestruct H as (? & ? & ?). clear H.
      specialize (EQ x). destruct EQ. destruct H, H0.
      specialize (H _ H3).
      edestruct H as (? & ? & ?).
      PER_reflexivityH.
    - intros HM. do 6 red in HM.
      intros.
      epose ((-=->! (state_prop ma) _) : A -=-> prop_typ) as Q.
      assert (eqmR (diagonal_prop Q) @ (ma, ma)).
      { intro. cbn. split. split.
        - intros.
          unfold state_prop. exists a0.
          split. split. intros.
          exists s. destruct (ma @ s) eqn: Hma.
          exists t. cbn in *. split; auto. reflexivity.
          exists s. destruct (ma @ s) eqn: Hma.
          cbn in *. exists t; split; auto. reflexivity.
          auto.
        - intros.
          unfold state_prop. exists b.
          split. split.
          exists s. destruct (ma @ s) eqn: Hma.
          exists t. cbn in *. split; auto. reflexivity.
          exists s. destruct (ma @ s) eqn: Hma.
          cbn in *. exists t; split; auto. reflexivity.
          auto.
        - reflexivity.
      }
      specialize (HM (diagonal_prop Q) (diagonal_prop_PER Q) H).
      unfold diagonal_prop in HM. cbn in HM.
      destruct HM as (HS & HS'); clear HS'. clear H.
      unfold state_prop in HS.
      edestruct HS as (? & ? & ?).
      auto.
      Unshelve.
      repeat intro. unfold state_prop. cbn.
      split.
      setoid_rewrite H. auto. setoid_rewrite H. auto.
  Qed.

  Lemma mayRet_bind_state :
    forall (A B : typ) (ma : state S A) (k : A -=-> state S B) (b : B),
    mayRet (state S) (bind k @ ma) @ b ->
    exists a : A, mayRet (state S) ma @ a /\ mayRet (state S) (k @ a) @ b.
  Proof.
    intros.
    setoid_rewrite <- mayRet_state. setoid_rewrite <- mayRet_state in H.
    edestruct H as (? & ? & ?); clear H.
    cbn in H0. destruct H0. destruct (ma @ x) eqn : Hma. cbn in *.
    exists t0. split.
    - exists x. rewrite Hma. cbn. exists t. split; reflexivity.
    - exists t, x0. split; auto.
  Qed.

  Opaque mayRet.

  Lemma eqmR_bind_ProperH_state :
    forall (A1 A2 B1 B2 : typ) (RA : relationH A1 A2) (RB : relationH B1 B2)
      (ma1 : state S A1) (ma2 : state S A2) (kb1 : A1 -=-> state S B1)
      (kb2 : A2 -=-> state S B2),
    eqmR RA @ (ma1, ma2) ->
    (forall a1 : A1,
    mayRet (state S) ma1 @ a1 ->
    forall a2 : A2, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2)) ->
    (forall a2 : A2,
    mayRet (state S) ma2 @ a2 ->
    forall a1 : A1, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2)) ->
    eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2).
  Proof.
    intros.
    cbn in *. unfold eqmR_state in *. cbn in *. intro.
    specialize (H s).
    destruct H. destruct H.
    destruct (ma1 @ s) eqn: Hma1.
    destruct (ma2 @ s) eqn: Hma2.
    cbn in *.
    specialize (H t0 equal_typ).
    specialize (H3 t2 equal_typ).
    edestruct H as (? & ? & ?); clear H.
    edestruct H3 as (? & ? & ?); clear H3.
    specialize (H0 t0). specialize (H1 t2).
    assert (mayRet (state S) ma1 @ t0). {
      rewrite <- mayRet_state. exists s, t. rewrite Hma1. reflexivity.
    }
    assert (mayRet (state S) ma2 @ t2). {
      rewrite <- mayRet_state. exists s, t1. rewrite Hma2. reflexivity.
    }
    specialize (H0 H3 _ H4 t1). specialize (H1 H7 x0 H t1).
    setoid_rewrite H6. setoid_rewrite H2. auto.
  Qed.

  Lemma image_eqmR_state :
    forall (A : typ) (ma : state S A), eqmR (image (state S) ma) @ (ma, ma).
  Proof.
    intros. cbn. unfold eqmR_state. intros. cbn.
    destruct (ma @ s) eqn: Hma.
    cbn in *. split. split.
    - intros. exists a. split. intros. unfold eqmR_state in EQ. cbn in *.
      specialize (EQ s). setoid_rewrite Hma in EQ.
      cbn in EQ. destruct EQ. destruct H0.
      specialize (H0 a H).
      edestruct H0 as (? & ? & ?); clear H0.
      PER_reflexivityH. auto.
    - intros. exists b. split. intros. unfold eqmR_state in EQ. cbn in *.
      specialize (EQ s). setoid_rewrite Hma in EQ.
      cbn in EQ. destruct EQ. destruct H0.
      specialize (H0 b H).
      edestruct H0 as (? & ? & ?); clear H0.
      PER_reflexivityH. auto.
    - reflexivity.
  Qed.

  Lemma eqmR_mayRet_l :
    forall (A1 A2 : typ) (RA : relationH A1 A2) (ma1 : state S A1)
      (ma2 : state S A2),
    eqmR RA @ (ma1, ma2) ->
    forall a1 : A1,
    mayRet (state S) ma1 @ a1 ->
    exists a2 : A2, RA @ (a1, a2) /\ mayRet (state S) ma2 @ a2.
  Proof.
    intros.
    rewrite <- mayRet_state in H0. edestruct H0 as (? & ? & ?); clear H0.
    cbn in *. destruct (ma1 @ x) eqn: Hma. cbn in *.
    destruct H1. unfold eqmR_state in H. cbn in H.
    specialize (H x). setoid_rewrite Hma in H.
    cbn in *. setoid_rewrite <- mayRet_state.
    destruct (ma2 @ x) eqn: Hma2. cbn in *.
    destruct H. destruct H.
    specialize (H _ H1). edestruct H as (? & ? & ?); clear H.
    specialize (H3 _ H5). edestruct H3 as (? & ? & ?); clear H3.
    exists x1. split. auto. exists x, t1. split. rewrite Hma2. reflexivity.
    rewrite Hma2. auto.
  Qed.

  Lemma eqmR_mayRet_r :
    forall (A1 A2 : typ) (RA : relationH A1 A2) (ma1 : state S A1)
      (ma2 : state S A2),
    eqmR RA @ (ma1, ma2) ->
    forall a2 : A2,
    mayRet (state S) ma2 @ a2 ->
    exists a1 : A1, RA @ (a1, a2) /\ mayRet (state S) ma1 @ a1.
  Proof.
    intros.
    rewrite <- mayRet_state in H0. edestruct H0 as (? & ? & ?); clear H0.
    cbn in *. destruct (ma1 @ x) eqn: Hma. cbn in *.
    destruct H1. unfold eqmR_state in H. cbn in H.
    specialize (H x). setoid_rewrite Hma in H.
    cbn in *. setoid_rewrite <- mayRet_state.
    destruct (ma2 @ x) eqn: Hma2. cbn in *.
    destruct H. destruct H.
    specialize (H3 _ H1). edestruct H3 as (? & ? & ?); clear H3.
    specialize (H _ H5). edestruct H as (? & ? & ?); clear H.
    exists x1. split. auto. exists x, t. split. rewrite Hma. reflexivity.
    rewrite Hma. auto.
  Qed.

  Lemma eqmR_ret_state :
    forall (A1 A2 : typ) (RA : relationH A1 A2) (a1 : A1) (a2 : A2),
    RA @ (a1, a2) -> eqmR (m := state S) RA @ (ret @ a1, ret @ a2).
  Proof.
    intros. cbn. unfold eqmR_state. cbn. intros.
    split. split.
    - intros. setoid_rewrite <- H0. exists a2. split; intuition.
    - intros. setoid_rewrite <- H0. exists a1. split; intuition.
    - reflexivity.
  Qed.

  Lemma eqmR_bind_ret_l_state:
    forall (A B : typ) (f : A -=-> state S B) (a : A), bind f @ (ret @ a) == f @ a.
  Proof.
    intros. repeat red. cbn. intros. split. rewrite H. reflexivity.
    rewrite H. reflexivity.
  Qed.

  Lemma eqmR_bind_ret_r_state:
    forall A : typ, typ -> forall ma : state S A, bind ret @ ma == ma.
  Proof.
    repeat intro. cbn. rewrite H. split; reflexivity.
  Qed.

  Lemma eqmR_bind_bind_state:
    forall (A B C : typ) (ma : state S A) (f : A -=-> state S B)
      (g : B -=-> state S C), (bind f >>> bind g) @ ma ==
                              bind (f >>> bind g) @ ma.
  Proof.
    repeat intro. cbn.
    assert (exists s1 a1, ma @ x == (s1, a1)). {
      destruct (ma @ x) eqn: Hma.
      exists t, t0. reflexivity.
    }
    assert (exists s1 a1, ma @ y == (s1, a1)). {
      destruct (ma @ y) eqn: Hma.
      exists t, t0. reflexivity.
    }
    edestruct H0 as (? & ? & ?).
    edestruct H1 as (? & ? & ?).
    clear H0; clear H1.
    rewrite H2. cbn.
    change (
      fst ((g @ snd ((f @ x1) @ x0)) @ fst ((f @ x1) @ x0)) ==
      fst
        ((g @ snd (f @ (snd (ma @ y)) @ fst (ma @ y))) @
        fst (f @ (snd (ma @ y)) @ fst (ma @ y))) /\
      snd ((g @ snd ((f @ x1) @ x0)) @ fst ((f @ x1) @ x0)) ==
      snd
        ((g @ snd (f @ (snd (ma @ y)) @ fst (ma @ y))) @
        fst (f @ (snd (ma @ y)) @ fst (ma @ y)))).
    rewrite H3. cbn. rewrite <- H in H3. rewrite H2 in H3.
    destruct H3. cbn in *. rewrite H0. rewrite H1. split; reflexivity.
  Qed.

  Instance EqmRMonad_state : EqmRMonad (state S).
  constructor.
  - apply image_eqmR_state.
  - apply mayRet_bind_state.
  - apply eqmR_mayRet_l.
  - apply eqmR_mayRet_r.
  - apply eqmR_ret_state.
  - apply eqmR_bind_ProperH_state.
  - apply eqmR_bind_ret_l_state.
  - apply eqmR_bind_ret_r_state.
  - apply eqmR_bind_bind_state.
  Qed.

  Lemma eqmR_bind_inv_state:
    forall (A B : typ) (RB : relationH B B),
    SymmetricH RB ->
    TransitiveH RB ->
    forall (ma : state S A) (k : A -=-> state S B) (b : B),
    mayRet (state S) (bind k @ ma) @ b ->
    eqmR (image (state S) ma) @ (ma, ma) /\
    (exists a : A, mayRet (state S) ma @ a ->
              mayRet (state S) (k @ a) @ b).
  Proof.
    repeat intro.
    split; [ split ; [ split | ] | ].
    - cbn. rewrite <- mayRet_state in H1.
      cbn in *. intros. exists a. split; auto. intros.
      unfold eqmR_state in EQ. cbn in EQ.
      specialize (EQ s). destruct EQ. destruct H3.
      specialize (H3 a H2).
      edestruct H3 as (? & ? & ?).
      PER_reflexivityH.
    - rewrite <- mayRet_state in H1.
      edestruct H1 as (? & ? & ?); clear H1.
      cbn. intros. exists b0. split; auto. intros.
      unfold eqmR_state in EQ. cbn in EQ.
      specialize (EQ s). destruct EQ. destruct H3.
      specialize (H5 _ H1).
      edestruct H5 as (? & ? & ?).
      PER_reflexivityH.
    - cbn. reflexivity.
    - cbn; intros.
      rewrite <- mayRet_state in H1. edestruct H1 as (? & ? & ?); clear H1.
      cbn in H2. destruct H2.
      destruct (ma @ x) eqn: H'. cbn in *.
      exists t0. intros.
      rewrite <- mayRet_state in H3. edestruct H3 as (? & ? & ?); clear H3.
      rewrite <- mayRet_state.
      exists t. exists x0. destruct ((k @ t0) @ t). cbn in *. split; auto.
  Qed.

  Context `{inhabited S}.
  Instance EqmRMonadInverses_state : EqmRMonadInverses (state S).
  constructor.
  - repeat intro.
    cbn in H. unfold eqmR_state in H. cbn in H.
    inversion inhabited0. specialize (H X).
    destruct H. destruct H.
    specialize (H a1 equal_typ). edestruct H as (? & ? & ?); clear H.
    specialize (H1 a2 equal_typ). edestruct H1 as (? & ? & ?); clear H1.
    rewrite H3. auto.
  - admit.
  - apply eqmR_bind_inv_state.
  Admitted.

End State.
