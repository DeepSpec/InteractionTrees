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
    (fun (p : state S A × state S B) =>
        forall s, S ⊗ R @ (fst p @ s, snd p @ s)).

  Program Instance EqmR_state : EqmR (state S) :=
    {
      eqmR := eqmR_state
    }.
  Next Obligation.
    repeat intro. destruct x2, y. cbn in *. destruct H.
    unfold eqmR_state. cbn. split. intros.
    specialize (H1 s).
    specialize (H s s).
    assert (s == s) by reflexivity.
    specialize (H H2). specialize (H0 s s H2).
    destruct (t @ s). destruct (t0 @ s). destruct (t1 @ s). destruct (t2 @ s).
    destruct H, H0. cbn in *; destruct H1. rewrite <- H. rewrite <- H0.
    split. auto. rewrite <- H3. rewrite <- H4. auto.
    intros.
    specialize (H1 s).
    specialize (H s s).
    assert (s == s) by reflexivity.
    specialize (H H2). specialize (H0 s s H2).
    destruct (t @ s). destruct (t0 @ s). destruct (t1 @ s). destruct (t2 @ s).
    destruct H, H0. cbn in *; destruct H1. rewrite H. rewrite H0.
    split. auto. rewrite H3. rewrite H4. auto.
  Qed.
  Next Obligation.
    split; repeat intro. cbn in *. rewrite H0.
    - unfold eqmR_state in H.
      specialize (H x0).
      change (S ⊗ A @ (x @ x0, y @ x0)) in H.
      rewrite <- H0. destruct (x @ x0). destruct (y @ x0).
      cbn in *. apply H.
    - change (S ⊗ A @ (x @ s, y @ s)).
      unfold state in *.
      repeat red in H. cbn in H. specialize (H s s).
      assert (s == s) by reflexivity.
      specialize (H H0). destruct (x @ s). destruct (y @ s).
      cbn in *. apply H.
  Qed.

  Lemma equal_typ {s} : s == s. reflexivity. Qed.

  Instance EqmR_OK_state : EqmR_OK (state S).
  constructor.
  - intros. repeat intro. unfold ReflexiveH in H.
    change (S ⊗ R @ (a @ s, a @ s)).
    unfold state in a.
    destruct (a @ s). cbn in *. split. reflexivity. auto.
  - intros. repeat intro. unfold SymmetricH in H.
    destruct p.
    change (S ⊗ R @ (t0 @ s, t @ s)).
    cbn in H0. unfold eqmR_state in H0.
    specialize (H0 s).
    change (S ⊗ R @ (t @ s, t0 @ s)) in H0.
    destruct (t0 @ s). destruct (t @ s).
    cbn in *. destruct H0. split. symmetry. apply H0.
    specialize (H (t4, t2) H1). apply H.
  - intros. repeat intro. unfold TransitiveH in H.
    destruct p, q. cbn in H2. red in H2.
    specialize (H2 s s equal_typ).
    change (S ⊗ R @ (t @ s, t2 @ s)).
    cbn in H0, H1; unfold eqmR_state in H0, H1.
    specialize (H0 s). specialize (H1 s).
    change (S ⊗ R @ (t @ s, t0 @ s)) in H0.
    change (S ⊗ R @ (t1 @ s, t2 @ s)) in H1.
    rewrite H2 in H0. clear H2; clear t0.
    destruct (t @ s), (t1 @ s), (t2 @ s).
    cbn in *. destruct H0, H1. split. etransitivity; eauto.
    specialize (H (t3, t5) (t5, t7) H2 H3). apply H. reflexivity.
  - repeat intro. cbn in H, H0. unfold eqmR_state in H, H0.
    specialize (H s); specialize (H0 s).
    change (S ⊗ R1 @ (ma @ s, mb @ s)) in H.
    change (S ⊗ R2 @ (mb @ s, mc @ s)) in H0.
    change (S ⊗ (R2 ∘ R1) @ (ma @ s, mc @ s)).
    destruct (ma @ s), (mb @ s), (mc @ s).
    cbn in *. destruct H, H0. split. etransitivity; eauto.
    exists t2. split; eauto.
  - intros. split; repeat intro.
    cbn in H; unfold eqmR_state in H.
    specialize (H s).
    change (S ⊗ † R @ (x @ s, y @ s)) in H.
    change (S ⊗ R @ (y @ s, x @ s)).
    destruct (x @ s), (y @ s).
    cbn in *. destruct H; split. symmetry; auto. auto.
    cbn in H; unfold eqmR_state in H.
    specialize (H s).
    change (S ⊗ R @ (y @ s, x @ s)) in H.
    change (S ⊗ † R @ (x @ s, y @ s)).
    destruct (x @ s), (y @ s).
    cbn in *. destruct H; split. symmetry; auto. auto.
  - repeat intro.
    red in H. destruct H. red in H, H0.
    split; repeat intro.
    + change (S ⊗ y @ (x0 @ s, y0 @ s)).
      cbn in H1. unfold eqmR_state in H1.
      specialize (H1 s).
      change (S ⊗ x @ (x0 @ s, y0 @ s)) in H1.
      destruct (x0 @ s), (y0 @ s).
      cbn in *. destruct H1. split; auto.
    + change (S ⊗ x @ (x0 @ s, y0 @ s)).
      cbn in H1. unfold eqmR_state in H1.
      specialize (H1 s).
      change (S ⊗ y @ (x0 @ s, y0 @ s)) in H1.
      destruct (x0 @ s), (y0 @ s).
      cbn in *. destruct H1. split; auto.
  - repeat intro.
    cbn in H0; unfold eqmR_state in H0.
    specialize (H0 s). red in H.
    change (S ⊗ y @ (x0 @ s, y0 @ s)).
    change (S ⊗ x @ (x0 @ s, y0 @ s)) in H0.
    destruct (x0 @ s), (y0 @ s). cbn in *.
    destruct H0. split; auto.
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
      Proper (equalE S ==> equalE (S × b)) (fun s : S => (f @ snd (sa @ s)) @ s).
  Proof.
    intros a b f sa.
    repeat intro. rewrite H. reflexivity.
  Qed.

  Lemma bind_stateT_P2:
    forall (a b : typ) (f : a -=-> state S b),
      Proper (equalE (state S a) ==> equalE (state S b))
              (fun sa : state S a =>
                (-=->!) (fun s : S => (f @ snd (sa @ s)) @ s) (bind_stateT_P a b f sa)).
  Proof.
    intros a b f.
    repeat intro. cbn. rewrite H, H0. split; reflexivity.
  Qed.

  Instance MonadState : Monad typ_proper (state S).
  split.
  - intros. refine (-=->! (fun x => _) (ret_stateT_P' a)).
  - intros. refine (-=->! (fun sa => _) (bind_stateT_P2 a b f)).
  Defined.

  Instance EqmRMonadInverses_state : EqmRMonadInverses (state S).
  constructor.
  Admitted.

  Instance EqmRMonad_state : EqmRMonad (state S).
  constructor.
  Admitted.

End State.




Section StateT.
  Variable m : typ -> typ.
  Variable S : typ.
  Context {Mm : Monad typ_proper m}.
  Context {EqmRm : EqmR m}.
  Context {EqmROKm : EqmR_OK m}.
  Context {EqmRInv : EqmRMonadInverses m}.
  Context {ML : EqmRMonad m}.

  (* Ported from Basics, the monad definitions on Basics should all change with
     typ. *)
  Definition stateT (s : typ) (m : typ -> typ) (a : typ) : typ :=
    s ~~> m (prod_typ s a).

  Global Instance EqmR_stateT : EqmR (stateT S m).
  econstructor. Unshelve. 2 : {
    refine (
        fun A B (R : relationH A B) =>
        -=->! (fun (p : stateT S m A × stateT S m B) =>
                   forall (s : S), eqmR (S ⊗ R) @ ((fst p) @ s, (snd p) @ s)) _).
    repeat intro. setoid_rewrite H. reflexivity.
  }
  repeat intro; split; repeat intro; cbn in *.
  - rewrite H0.
    eapply eqmR_equal.
    eapply eqmR_Proper_mono; eauto.
    repeat red. intros. destruct x1, y1. cbn in *. apply H1.
  - eapply eqmR_Proper_mono; eauto.
    2 : { eapply eqmR_equal in H. 2 : reflexivity. apply H. }
    apply prod_rel_eq.
  Defined.

  (* Lemma eqmR_rel_prod : forall {A B : typ} *)
  (*                       (R : relationH A B) *)
  (*                       (x : A) (y : B) (s : S), *)
  (*   R @ (x, y) -> *)
  (*   eqmR (m := stateT S m) (S ⊗ R) @ (ret @ ((s, x),(s, y))). *)

  Global Instance EqmR_OK_stateT : EqmR_OK (stateT S m).
  Proof.
    split; unfold eqmR, EqmR_stateT; intros.
    - red. cbn. intros.
      epose proof @prod_rel_refl.
      rewrite ReflexiveH_Reflexive in H.
      specialize (H0 _ _ S _ _ H).
      eapply eqmR_transport_refl in H0; eauto.
    - red. cbn. intros.
      epose proof @prod_rel_sym.
      apply SymmetricH_Symmetric in H.
      specialize (H1 S A S R _ H).
      eapply eqmR_transport_symm in H0; eauto.
      2 : { apply SymmetricH_Symmetric; eauto. }
      cbn in H0. apply H0.
    - cbn . intros!. cbn in *.
      apply TransitiveH_Transitive in H.
      epose proof @prod_rel_trans.
      specialize (H3 S A S R _ H).
      pose proof @eqmR_transport_trans.
      apply TransitiveH_Transitive in H3.
      specialize (H4 m _ _ _ _ H3).
      red in H4. red in H2.
      specialize (H4 (fst p @ s, snd p @ s) (fst q @ s, snd q @ s)).
      specialize (H4 (H0 s) (H1 s)).
      cbn in H4. apply H4.
      apply H2. reflexivity.
    - red; cbn; repeat intro. cbn in *.
      specialize (H s). specialize (H0 s).
      eapply eqmR_Proper; eauto.
      rewrite <- (eq_id_r S).
      rewrite prod_compose. reflexivity.
      eapply eqmR_rel_trans; auto.
      + apply H.
      + apply H0.
    - split; intros smb sma Heq s.
      + specialize (Heq s).
        cbn in *.
        apply eqmR_lift_transpose; eauto.
        eapply eqmR_Proper; eauto.
        rewrite transpose_prod.
        rewrite transpose_sym_eq_rel; eauto. reflexivity.
        typeclasses eauto.
      + unfold transpose in Heq. specialize (Heq s).
        eapply eqmR_Proper; eauto.
        rewrite <- transpose_sym_eq_rel; auto.
        rewrite <- transpose_prod.
        reflexivity. typeclasses eauto.
        cbn in *. apply eqmR_lift_transpose; auto.
    - repeat intro. cbn in *. split.
      +  repeat intro. cbn.
          specialize (H0 s). cbn in *.
          eapply eqmR_Proper; eauto.
          rewrite H. reflexivity.
      + repeat intro. cbn.
        specialize (H0 s). cbn in *.
        eapply eqmR_Proper; eauto.
        rewrite H. reflexivity.
    - repeat red. repeat intro. specialize (H0 s).
      eapply (eqmR_Proper_mono) in H0; eauto.
      apply prod_rel_monotone. intuition. eauto.
  Qed.

  (* Making properness proofs opaque, so it's doesn't do the ugly unfolding in
   proof contexts *)
  Lemma Proper_ret :
    forall (a : typ) (x : a),
      Proper (equalE S ==> equalE (m (S × a))) (fun s : S => ret @ (s, x)).
  Proof.
    repeat intro. rewrite H. reflexivity.
  Qed.

  Lemma Proper_ret_2 :
    forall (a : typ),
      Proper (equalE a ==> equalE (S ~~> m (S × a)))
         (fun x : a => (-=->!) (fun s : S => ret @ (s, x)) (Proper_ret a x)).
  Proof.
    repeat intro. cbn. rewrite H0, H. reflexivity.
  Qed.

  Lemma Proper_bind:
    forall (a b : typ) (f : a -=-> stateT S m b),
      S ~~> m (S × a) ->
      S ->
      Proper (equalE (S × a) ==> equalE (m (S × b)))
              (fun y : S * a => uncurry f @ (snd y, fst y)).
  Proof.
    repeat intro.
    destruct x, y. cbn.
    destruct H. cbn in *. rewrite H, H0. reflexivity.
  Defined.

  Lemma Proper_bind_2:
    forall (a b : typ) (f : a -=-> stateT S m b) (k : S ~~> m (S × a)),
      Proper (equalE S ==> equalE (m (S × b)))
          (fun x : S =>
            let X :=
                (-=->!) (fun y : S * a => uncurry f @ (snd y, fst y))
                        (Proper_bind a b f k x) in
            @bind typ typ_proper m Mm (S × a) (S × b) X @ (k @ x)).
  Proof.
    repeat intro. unfold uncurry. cbn. unfold Proper_bind.
    rewrite H.
    reflexivity.
  Qed.

  Lemma Proper_bind_3:
    forall (a b : typ) (f : a -=-> stateT S m b),
      @Proper (S ~~> m (S × a) -> S ~~> m (S × b))
              (equalE (S ~~> m (S × a)) ==> equalE (S ~~> m (S × b)))
              (fun k : S ~~> m (S × a) =>
                  (-=->!)
                    (fun x : S =>
                      let X :=
                          (-=->!)
                            (fun y : S * a =>
                                @uncurry a S (m (S × b)) f @ (@snd S a y, @fst S a y))
                            (Proper_bind a b f k x) in
                      @bind typ typ_proper m Mm (S × a) (S × b) X @ (k @ x))
                    (Proper_bind_2 a b f k)).
  Proof.
    intros a b f. unfold Proper_bind.
    repeat intro. unfold uncurry. cbn. rewrite H.
    rewrite H0. reflexivity.
  Qed.

  Set Transparent Obligations.
  (* ret and bind definition for stateT. *)
  Program Instance stateT_Monad : Monad typ_proper (stateT S m).
  Next Obligation.
  intros. unfold stateT. refine (-=->! (fun x => _) _).
  Unshelve. 2 : {
      refine (-=->! (fun s => ret @ (s, x)) _). apply Proper_ret.
  } apply Proper_ret_2.
  Defined.
  Next Obligation.
  unfold stateT. intros.
  refine (-=->! (fun k => _) _).
  Unshelve. 2 : {
    refine (-=->! (fun x => _) _).
    Unshelve. 2 : {
      assert ((S × a) -=-> m (S × b)). {
        refine (-=->! (fun y => uncurry f @ (snd y, fst y)) _).
        apply Proper_bind; eauto.
      }
      exact ((bind X) @ (k @ x)).
    }
      apply Proper_bind_2; eauto.
  }
  apply Proper_bind_3; eauto.
  Defined.

  Lemma relate_state_proper:
    forall (A1 : typ) (R : relationH A1 A1),
      Proper (equalE ((S × A1) × (S × A1)) ==> equalE prop_typ)
             (fun p : S * A1 * (S * A1) =>
                fst (fst p) == fst (snd p) /\ R @ (snd (fst p), snd (snd p))).
  Proof.
    repeat intro. destruct x, y. destruct t, t0, t1, t2. cbn.
    split; intro.
    destruct H. cbn in H, H1. destruct H, H0, H1.
    split. rewrite <- H. rewrite <- H1. auto.
    rewrite <- H2. rewrite <- H4. auto.
    destruct H. cbn in H, H1. destruct H, H0, H1.
    split. rewrite H. rewrite H1. auto.
    rewrite H2. rewrite H4. auto.
  Qed.

  Program Definition relate_state {A1 : typ} (R : relationH A1 A1) : relationH (S × A1) (S × A1).
  refine (-=->! (fun (p : (S * A1) * (S * A1)) => fst (fst p) == fst (snd p) /\ R @ (snd (fst p), snd (snd p))) _).
  apply relate_state_proper; auto.
  Defined.


  Lemma relate_state_Symmetric {A1 : typ} (R : relationH A1 A1)
        (RH: SymmetricH R): SymmetricH (relate_state R).
  Proof.
    repeat intro. cbn. destruct p. destruct t, t0. destruct H.
    cbn in *. split. symmetry; auto. apply SymmetricH_Symmetric in RH.
    apply RH. apply H0.
  Qed.

  Lemma relate_state_Transitive {A1 : typ} (R : relationH A1 A1)
        (RH: TransitiveH R) : TransitiveH (relate_state R).
  Proof.
    repeat intro. cbn. destruct p. destruct t, t0. destruct H.
    cbn in *. destruct H0, H1. destruct q, p, p0. cbn in *. split.
    rewrite <- H0. rewrite <- H1. apply H.
    apply TransitiveH_Transitive in RH.
    eapply RH. apply H2. rewrite H4. apply H3.
  Qed.

  Program Definition snd_prj {B} (R: relationH (S × B) (S × B)) (t : S): relationH B B := (-=->! (fun p => R @ ((t, fst p),(t, snd p))) _).
  Next Obligation.
    repeat intro. destruct x, y. cbn in H. destruct H; cbn.
    split. intros. rewrite <- H; rewrite <- H0. auto.
    intros. rewrite H, H0. auto.
  Defined.

  Lemma stateT_inv_equal {A1 A2 : typ} :
    forall (RA : relationH A1 A2) (sma1 : stateT S m A1)
      (sma2 : stateT S m A2),
      eqmR RA @ (sma1, sma2) ->
      forall (ma1 : m A1), exists (ma2 : m A2), eqmR RA @ (ma1, ma2).
  Admitted.


  Lemma stateT_image:
    forall (A : typ) (ma : stateT S m A), eqmR (image (stateT S m) ma) @ (ma, ma).
  Admitted.

  Definition curry_swap' {A B} (k : A -=-> (S ~~> m (S × B))) : (S × A) -> m (S × B) := fun p => k @ (snd p) @ (fst p).

  Lemma curry_swap_Proper:
    forall {A B}
      (k : A -=-> (S ~~> m (S × B))),
  Proper (equalE (S × A) ==> equalE (m (S × B))) (curry_swap' k).
  Proof.
    repeat intro. cbn. destruct x, y. cbn in *. destruct H.
    unfold curry_swap'.
    rewrite H, H0. reflexivity .
  Qed.

  Definition curry_swap {A B} (k : A -=-> (S ~~> m (S × B))) : (S × A) -=-> m (S × B) := (-=->! (curry_swap' k) (curry_swap_Proper k)).


  (* Lemma mayRet_stateT {A:typ} (ma : stateT S m A) (a : A) : *)
  (*   forall s, (ma @ s) <-> mayRet (stateT S m) ma @ a. *)

  Lemma mayRet_stateT_bind :
    forall {A B : typ} (ma : stateT S m A)
      (k : A -=-> stateT S m B) (b : B),
      mayRet (stateT S m) (bind k @ ma) @ b ->
      exists (ma' : m A) (k' : A -=-> m B),
      mayRet m (bind k' @ ma') @ b.
  Proof.
    intros. Admitted.

  (* Lemma stateT_image_refl {A : typ} : *)
  (*   forall (x : m A) (ma' : m A), *)
  (*   eqmR (image m ma') @ (x, x) -> eqmR (image (stateT S m)) @ (x, x). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma eqmR_prod_inv {A : typ}:
    forall (ma' : m A) (ma : stateT S m A) (s : S) (R : relationH A A),
      eqmR R @ (ma', ma') ->
      eqmR (S ⊗ R) @ (ma @ s, ma @ s).
  Admitted.

  Lemma stateT_mayRet_bind :
    forall (A B : typ) (ma : stateT S m A) (k : A -=-> stateT S m B) (b : B),
    mayRet (stateT S m) (bind k @ ma) @ b ->
    exists a : A, mayRet (stateT S m) ma @ a /\ mayRet (stateT S m) (k @ a) @ b.
  Proof.
    intros.
    pose proof mayRet_bind as HMB.
    specialize (HMB m _ _ _).
    pose proof (mayRet_stateT_bind _ _ _ H) as HBind.
    edestruct HBind as (ma' & k' & bind'); clear HBind.
    specialize (HMB A B _ _ _ bind').
    edestruct HMB as (a & prefix & cont); clear HMB.
    exists a. split.
    - eapply prefix. eapply image_PER.
      eapply eqmR_Proper; eauto.
      + Unshelve.
        2 : { exact (image m ma'). }
        split; repeat intro.
        * apply H0; eauto. intro. cbn.
          remember (ma @ s).
          admit.
        * apply H0; eauto. cbn in EQ. admit.
      + admit. 
    - pose proof mayRet_bind as HMB.
      specialize (HMB m _ _ _).
      pose proof (mayRet_stateT_bind _ _ _ H) as HBind.
      edestruct HBind as (? & ? & ?).
      specialize (HMB A B _ _ _ H0).
      edestruct HMB.
      destruct H1.
      intro. cbn. intros. apply H2. 
    (*   intro. intro.  *)
    (*   edestruct HMB as (? & ? & ?). *)

    (*   repeat intro.  *)
    (*   repeat red in H. cbn in H. *)
    (*   cbn.  *)
    (*   unfold stateT in *. *)
    (*   edestruct HMB; eauto. *)
    (*   + repeat red. intros. apply H; eauto. repeat intro. cbn. *)
    (*     eapply eqmR_bind_ProperH; eauto. *)
    (*     * eapply eqmR_equal. cbn. reflexivity. *)
    (*     * cbn. intros. destruct a1, a2. cbn in *. destruct H2. *)
    (*       rewrite H2, H3. *)

    (*       eapply eqmR_Proper_mono; eauto. *)
    (*       eapply image_least. eapply prod_rel_PER; auto. *)
    (*       eapply relationH_PER. *)
    (*       -- admit. *)
    (*       -- eapply image_eqmR; eauto. *)
    (*   + destruct H0. *)
    (*     apply H0.  *)
    (*     repeat intro. *)

    (* - cbn. intros. cbn in H. apply H; eauto. intros. *)
    (*   eapply eqmR_bind_ProperH; eauto. *)
    (*   + eapply eqmR_equal. cbn. reflexivity. *)
    (*   + pose proof mayRet_bind. specialize (EQ s). intros. cbn. *)
    (*     destruct a1, a2. cbn in *. *)
    (*     destruct H3. rewrite H3. rewrite H4. *)

    (*     eapply eqmR_transport_refl; eauto. *)
    (*     red. intro. destruct a. cbn. split. reflexivity. *)
        (* reflexivity.  *)
  Admitted.

  Lemma stateT_eqmR_mayRet_l :
    forall (A1 A2 : typ) (ma1 : stateT S m A1) (ma2 : stateT S m A2)
      (RA : relationH A1 A2),
    eqmR RA @ (ma1, ma2) ->
    forall a1 : A1,
    mayRet (stateT S m) ma1 @ a1 ->
    exists a2 : A2, RA @ (a1, a2) /\ mayRet (stateT S m) ma2 @ a2.
  Proof.
    intros*. intros EQ' a1 HMR.
    pose proof eqmR_mayRet_l as H.
    specialize (H m _ _ _ _ _ RA).
    pose proof @stateT_inv_equal as HI.
    specialize (HI _ _ RA ma1 ma2 EQ').
    edestruct HI.
    edestruct H.
    - cbn in EQ'. apply H0.
    - apply HMR.
      + eapply image_PER.
      + cbn. intros. clear H0.
        clear HI.
        eapply eqmR_transport_refl; eauto.
        repeat intro. cbn. destruct a. split.
        reflexivity. intros.
        eapply eqmR_ret_inv in EQ.
        admit. auto.
    - exists x0. destruct H1. split; auto. apply H2.
      eapply image_PER.
  Admitted.

  Lemma stateT_eqmR_mayRet_r :
    forall (A1 A2 : typ) (ma1 : stateT S m A1) (ma2 : stateT S m A2)
      (RA : relationH A1 A2),
    eqmR RA @ (ma1, ma2) ->
    forall a2 : A2,
    mayRet (stateT S m) ma2 @ a2 ->
    exists a1 : A1, RA @ (a1, a2) /\ mayRet (stateT S m) ma1 @ a1.
  Proof.
  Admitted.

  Instance EqmRMonad_stateT : @EqmRMonad (stateT S m) _ _.
  Proof.
    constructor.
    - admit.
    - apply stateT_mayRet_bind.
    -
    (*   apply stateT_eqmR_mayRet_l. *)
    (* - apply stateT_eqmR_mayRet_r. *)
  Admitted.

(*   Context {Im: Iter (Kleisli m) sum}. *)
(*   Context {Cm: Iterative (Kleisli m) sum}. *)

(*   Definition iso {a b:Type} (sab : S * (a + b)) : (S * a) + (S * b) := *)
(*     match sab with *)
(*     | (s, inl x) => inl (s, x) *)
(*     | (s, inr y) => inr (s, y) *)
(*     end. *)

(*   Definition iso_inv {a b:Type} (sab : (S * a) + (S * b)) : S * (a + b) := *)
(*     match sab with *)
(*     | inl (s, a) => (s, inl a) *)
(*     | inr (s, b) => (s, inr b) *)
(*     end. *)

(*   Definition internalize {a b:Type} (f : Kleisli (stateT S m) a b) : Kleisli m (S * a) (S * b) := *)
(*     fun (sa : S * a) => f (snd sa) (fst sa). *)

(*   Lemma internalize_eq {a b:Type} (f g : Kleisli (stateT S m) a b) : *)
(*     eq2 f g <-> eq2 (internalize f) (internalize g). *)
(*   Proof. *)
(*     split. *)
(*     - intros. *)
(*       repeat red. destruct a0. *)
(*       unfold internalize. cbn.  specialize (H a0 s). unfold eqmR in H. *)
(*       rewrite prod_rel_eq in H. apply H. *)
(*     - intros. *)
(*       repeat red. intros. *)
(*       unfold internalize in H. *)
(*       specialize (H (s, a0)). *)
(*       rewrite prod_rel_eq. *)
(*       apply H. *)
(*   Qed. *)

(*   Lemma internalize_cat {a b c} (f : Kleisli (stateT S m) a b) (g : Kleisli (stateT S m) b c) : *)
(*     (internalize (f >>> g)) ⩯ ((internalize f) >>> (internalize g)). *)
(*   Proof. *)
(*     repeat red. *)
(*     destruct a0. *)
(*     cbn. *)
(*     unfold internalize. *)
(*     unfold cat, Cat_Kleisli. *)
(*     cbn. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma internalize_pure {a b c} (f : Kleisli (stateT S m) a b) (g : S * b -> S * c) : *)
(*     internalize f >>> pure g   ⩯   (internalize (f >>> (fun b s => ret (g (s,b))))). *)
(*   Proof. *)
(*     repeat red. *)
(*     destruct a0. *)
(*     unfold internalize, cat, Cat_Kleisli. cbn. *)
(*     apply Proper_bind; auto. *)
(*     - reflexivity. *)
(*     - repeat red. *)
(*       destruct a1. *)
(*       unfold pure. reflexivity. *)
(*   Qed. *)

(*   Global Instance Iter_stateT : Iter (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*     exact *)
(*       (fun (a b : Type) (f : a -> S -> m (S * (a + b))) (x:a) (s:S) => *)
(*         iter ((internalize f) >>> (pure iso)) (s, x)). *)
(*   Defined. *)

(*   Global Instance Proper_Iter_stateT : forall a b, @Proper (Kleisli (stateT S m) a (a + b) -> (Kleisli (stateT S m) a b)) (eq2 ==> eq2) iter. *)
(*   Proof. *)
(*     destruct Cm. *)
(*     repeat red. *)
(*     intros a b x y H a0 s. *)
(*     rewrite prod_rel_eq. *)
(*     apply iterative_proper_iter. *)
(*     repeat red. *)
(*     destruct a1. *)
(*     cbn. *)
(*     apply Proper_bind. *)
(*     - unfold internalize. cbn. (specialize (H a1 s0)). rewrite prod_rel_eq in H. apply H. *)
(*     - repeat red. destruct a2 as [s' [x1|y1]]; reflexivity. *)
(*   Qed. *)

(*   Global Instance IterUnfold_stateT : IterUnfold (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*   destruct Cm. *)
(*   unfold IterUnfold. *)
(*   intros a b f. *)
(*   repeat red. *)
(*   intros a0 s. *)
(*   unfold cat, Cat_Kleisli. *)
(*   unfold iter, Iter_stateT. *)
(*   rewrite iterative_unfold.  (* SAZ: why isn't iter_unfold exposed here? *) *)
(*   unfold cat, Cat_Kleisli. *)
(*   simpl. *)
(*   rewrite bind_bind. rewrite prod_rel_eq. *)
(*   apply Proper_bind. *)
(*   + reflexivity. *)
(*   + repeat red. destruct a1 as [s' [x | y]]; simpl. *)
(*     * unfold pure. rewrite bind_ret_l. *)
(*       reflexivity. *)
(*     * unfold pure. rewrite bind_ret_l. *)
(*       reflexivity. *)
(*   Qed. *)

(*   Global Instance IterNatural_stateT : IterNatural (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*     destruct Cm. *)
(*     unfold IterNatural. *)
(*     intros a b c f g. *)
(*     repeat red. *)
(*     intros a0 s. *)
(*     setoid_rewrite iterative_natural. rewrite prod_rel_eq. *)
(*     apply iterative_proper_iter. *)
(*     repeat red. *)
(*     destruct a1. *)
(*     unfold cat, Cat_Kleisli. *)
(*     cbn. *)
(*     rewrite! bind_bind. *)
(*     apply Proper_bind. *)
(*     - reflexivity. *)
(*     - repeat red. destruct a2 as [s' [x | y]]; simpl. *)
(*       + unfold pure. rewrite bind_ret_l. *)
(*         cbn. unfold cat, Cat_Kleisli. cbn. *)
(*         rewrite bind_bind. *)
(*         rewrite bind_ret_l. *)
(*         rewrite bind_ret_l. *)
(*         cbn. *)
(*         unfold id_, Id_Kleisli. unfold pure. rewrite bind_ret_l. reflexivity. *)
(*       + unfold pure. rewrite bind_ret_l. *)
(*         cbn. unfold cat, Cat_Kleisli. cbn. *)
(*         rewrite bind_bind. *)
(*         apply Proper_bind. *)
(*         * reflexivity. *)
(*         * repeat red. destruct a2. *)
(*           cbn. *)
(*           rewrite bind_ret_l. reflexivity. *)
(*   Qed. *)

(*   Lemma internalize_pure_iso {a b c} (f : Kleisli (stateT S m) a (b + c)) : *)
(*     ((internalize f) >>> pure iso) ⩯ (fun sa => (bind (f (snd sa) (fst sa))) (fun sbc => ret (iso sbc))). *)
(*   Proof. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma eq2_to_eqm : forall a b (f g : Kleisli (stateT S m) a b) (x:a) (s:S), *)
(*       eq2 f g -> *)
(*       eqm (f x s) (g x s). *)
(*   Proof. *)
(*     intros a b f g x s H. *)
(*     specialize (H x s). rewrite prod_rel_eq in H. *)
(*     apply H. *)
(*   Qed. *)

(*   Lemma iter_dinatural_helper: *)
(*     forall (a b c : Type) (f : Kleisli (stateT S m) a (b + c)) (g : Kleisli (stateT S m) b (a + c)), *)
(*       internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_. *)
(*   Proof. *)
(*     destruct Cm. *)
(*     intros a b c f g. *)
(*     repeat red. *)
(*     destruct a0. *)
(*     unfold cat, Cat_Kleisli, internalize. *)
(*     cbn. *)
(*     repeat rewrite bind_bind. *)
(*     apply Proper_bind. *)
(*     - reflexivity. *)
(*     - repeat red. *)
(*       destruct a1 as [s' [x | y]]. *)
(*       + unfold pure. *)
(*         rewrite bind_ret_l. *)
(*         unfold case_, Case_Kleisli, Function.case_sum. *)
(*         reflexivity. *)
(*       + unfold pure. rewrite bind_ret_l. *)
(*         unfold case_, Case_Kleisli, Function.case_sum. *)
(*           cbn. *)
(*           rewrite bind_ret_l. reflexivity. *)
(*   Qed. *)


(*   Global Instance IterDinatural_stateT : IterDinatural (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*     destruct Cm. *)
(*     unfold IterDinatural. *)
(*     repeat red. *)
(*     intros a b c f g a0 a1. *)
(*     unfold iter, Iter_stateT. *)
(*     eapply transitivity. rewrite prod_rel_eq. *)
(*     eapply iterative_proper_iter. *)
(*     apply iter_dinatural_helper. *)
(*     rewrite iterative_dinatural. *)
(*     cbn. *)
(*     unfold cat, Cat_Kleisli. *)
(*     rewrite bind_bind. *)
(*     unfold internalize. cbn. rewrite prod_rel_eq. *)
(*     apply Proper_bind. *)
(*     - reflexivity. *)
(*     - repeat red. *)
(*       destruct a2 as [s [x | y]]. *)
(*       + unfold pure. *)
(*         rewrite bind_ret_l. *)
(*         cbn. *)
(*         eapply iterative_proper_iter. *)
(*         repeat red. *)
(*         destruct a2. *)
(*         cbn. rewrite! bind_bind. *)
(*         apply Proper_bind. *)
(*         * reflexivity. *)
(*         * repeat red. *)
(*           destruct a2 as [s' [x' | y]]. *)
(*           ** cbn.  rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum. *)
(*              reflexivity. *)
(*           ** cbn.  rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum. *)
(*              rewrite bind_ret_l. reflexivity. *)
(*       + unfold pure. *)
(*         rewrite bind_ret_l. *)
(*         cbn. *)
(*         reflexivity. *)
(*     Qed. *)


(*   Global Instance IterCodiagonal_stateT : IterCodiagonal (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*     destruct Cm. *)
(*     unfold IterCodiagonal. *)
(*     intros a b f. *)
(*     unfold iter, Iter_stateT. *)
(*     repeat red. *)
(*     intros. *)
(*     eapply transitivity. rewrite prod_rel_eq. *)
(*     eapply iterative_proper_iter. *)
(*     eapply Proper_cat_Kleisli. *)

(*     assert (internalize (fun (x:a) (s:S) => iter (internalize f >>> pure iso) (s, x)) *)
(*                        ⩯ *)
(*                        iter (internalize f >>> pure iso)). *)
(*     { repeat red. *)
(*       intros a2. *)
(*       destruct a2. *)
(*       unfold internalize. *)
(*       cbn.  reflexivity. *)
(*     } *)
(*    apply H. *)
(*    reflexivity. *)
(*    eapply transitivity. rewrite prod_rel_eq. *)

(*    eapply iterative_proper_iter. *)
(*    apply iterative_natural. *)
(*    rewrite iterative_codiagonal. rewrite prod_rel_eq. *)
(*    eapply iterative_proper_iter. *)
(*    rewrite internalize_cat. *)
(*    (* SAZ This proof can probably use less unfolding *) *)
(*    repeat red. intros a2. *)
(*    destruct a2. *)
(*    unfold cat, Cat_Kleisli. cbn. *)
(*    repeat rewrite bind_bind. *)
(*    unfold internalize, pure. *)
(*    cbn. *)
(*    apply Proper_bind. *)
(*     - reflexivity. *)
(*     - repeat red. *)
(*       intros a3. *)
(*       destruct a3 as [s' [x | [y | z]]]. *)
(*       + rewrite bind_ret_l. *)
(*         cbn. unfold id_, Id_Kleisli, pure. *)
(*         rewrite bind_ret_l. *)
(*         unfold cat, Cat_Kleisli. *)
(*         rewrite bind_bind. *)
(*         rewrite bind_ret_l. *)
(*         cbn.  unfold inl_, Inl_Kleisli, pure. *)
(*         rewrite bind_ret_l. reflexivity. *)
(*       + rewrite bind_ret_l. *)
(*         cbn. *)
(*         rewrite bind_ret_l. *)
(*         unfold cat, Cat_Kleisli. *)
(*         rewrite bind_bind, bind_ret_l. cbn. *)
(*         unfold inr_, Inr_Kleisli, pure. *)
(*         rewrite bind_ret_l. reflexivity. *)
(*       + rewrite bind_ret_l. *)
(*         cbn. *)
(*         rewrite bind_ret_l. *)
(*         unfold cat, Cat_Kleisli. *)
(*         rewrite bind_bind, bind_ret_l. cbn. *)
(*         unfold inr_, Inr_Kleisli, pure. *)
(*         rewrite bind_ret_l. *)
(*         reflexivity. *)
(*   Qed. *)

(*   Global Instance Iterative_stateT : Iterative (Kleisli (stateT S m)) sum. *)
(*   Proof. *)
(*   constructor; *)
(*   typeclasses eauto. *)
(*   Qed. *)

End StateT.
