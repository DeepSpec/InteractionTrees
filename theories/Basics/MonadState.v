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
    assert (forall s : S, eqmR (S × A) @ (x @ s, y @ s)). {
      intros. eapply eqmR_Proper_mono; eauto.
      apply prod_rel_eq.
    }
    pose proof eqmR_equal.
    eapply H2 in H1. cbn in H1.
    apply H1.
  - eapply eqmR_Proper_mono; eauto.
    2 : { eapply eqmR_equal in H. 2 : reflexivity. apply H. }
    apply prod_rel_eq.
  Defined.

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

  Instance EqmRMonad_stateT (HS: inhabited S) : @EqmRMonad (stateT S m) _ _.
  Proof.
    constructor.
    -  (* admit.  (* SAZ Trying not to need this one *) *)
      (*  intros.
       do 3 red. cbn. intro s.
      assert (s == s) by reflexivity. *)
      admit.

   - intros.
      
  - repeat intro; cbn. pose proof (eqmR_ret _ _ _ _ H).
    assert (s == s) by reflexivity.
    eapply eqmR_ret; eauto. cbn. split; eauto.
  - repeat intro.
    change (eqmR (S ⊗ RB) @ (((bind kb1 @ ma1) @ s), ((bind kb2 @ ma2) @ s))).
    eapply eqmR_bind_ProperH; eauto.
    intros. destruct a1 as (s1 & a1).
    cbn in H.
    pose proof eqmR_mayRet_l as Heq.
    specialize (Heq _ _ _ _ _ _ (ma1 @ s) (ma2 @ s) (S ⊗ RA) (H s) _ H2).
    edestruct Heq as (x & SRA & Hmr).
    exists x. clear Heq.
    split; eauto. split; eauto.
    cbn. destruct x as (s2 & a2). cbn.
    destruct SRA as (Seq & Aeq). cbn in Seq, Aeq.
    rewrite Seq in *. clear Seq.
    + 


      specialize (H0 a1).
      assert (Hma: mayRet (stateT S m) ma1 @ a1). {
        cbn. intros. cbn in H2.
        specialize (H2 (S ⊗ R)).
        assert (SymmetricH (S ⊗ R)). {
          apply SymmetricH_Symmetric.
          eapply prod_rel_sym. repeat intro. rewrite H3. reflexivity.
          apply SymmetricH_Symmetric. apply HS0. }
        assert (TransitiveH (S ⊗ R)). {
          apply TransitiveH_Transitive.
          eapply prod_rel_trans. repeat intro. rewrite H4. auto.
          apply TransitiveH_Transitive. auto. }
        specialize (H2 H3 H4 (EQ s)). cbn in H2. apply H2.
      }
      specialize (H0 Hma).
      edestruct H0 as (a2' & HRA & Hmr' & Heqm); clear H0.
      specialize (H1 a2).
      assert (Hmb: mayRet (stateT S m) ma2 @ a2). {
        cbn. intros. cbn in Hmr.
        specialize (Hmr (S ⊗ R)).
        assert (SymmetricH (S ⊗ R)) as SYM. {
        apply SymmetricH_Symmetric.
        eapply prod_rel_sym. repeat intro. rewrite H0. reflexivity.
        apply SymmetricH_Symmetric. apply HS0. }
        assert (TransitiveH (S ⊗ R)). {
          apply TransitiveH_Transitive.
          eapply prod_rel_trans. repeat intro. rewrite H0. auto.
          apply TransitiveH_Transitive. auto. }
        specialize (Hmr SYM H0 (EQ s)). cbn in Hmr. apply Hmr.
      }
      specialize (H1 Hmb).
      edestruct H1 as (a1' & HRA' & Hmr'' & Heqm'); clear H1.
      assert (TransitiveH (S ⊗ RB)).
      
      

      
      edestruct H1 as (a1' & HRA' & Hmr'' & Heqm'); clear H1.
      repeat red in Heqm'. specialize (Heqm' s2).
      cbn in Heqm'.
      repeat red in Heqm. specialize (Heqm s2). cbn in Heqm.
      
      (* IY: Need to generalize EqmRMonadInverses lemmas to EqmR? *)
  Admitted.


  (* - repeat intro. *)
  (*   change (eqmR (S ⊗ RB) @ (((bind kb1 @ ma1) @ s), ((bind kb2 @ ma2) @ s))). *)
  (*   pose proof eqmR_rel_prod. *)
  (*   specialize (H2 m _ _ _ _ _ _ S RB s s). *)
  (*   eapply eqmR_bind_ProperH; eauto. repeat intro. *)
  (*   (* specialize (H2 _ _ ) *) *)
  (*   destruct a1. specialize (H0 t0). *)
  (*   specialize (H2 (fun x1 s1 => (ret @ (x1, s1))) (fun x1 s1 => (ret @ (x1, s1)))). *)
  (*   specialize (H2 s s a1 a2 H1 H). apply H2. *)
  (*   apply eqmR_ret *)
  (*   repeat intro. *)
  (*   cbn. *)
  (*   pose proof eqmR_ret. *)
  (*   eapply eqmR_Proper; eauto. *)
  (*   destruct RA. cbn in *.  *)
  (*   rewrite <- (eq_id_r S). *)
  (*   rewrite <- (eq_id_r RA). *)
  (*   rewrite prod_compose. reflexivity. *)
  (*   eapply eqmR_rel_trans; eauto.  *)
  (*   rewrite <- prod_rel_eq.  *)
  (*   eapply Proper_typ_proper_app.  *)
  (*   eapply eqmR_Proper; eauto. *)
    
  (*   apply ret_ok. assumption. *)
  (* - intros. *)
  (*   unfold eqmR, EqmR_stateT. *)
  (*   intros s. *)
  (*   eapply eqmR_bind_ProperH. assumption. *)
  (*   apply H. *)
  (*   intros. destruct a1. destruct a2. *)
  (*   cbn. unfold eqmR, EqmR_stateT in H0. *)
  (*   inversion H1; subst. *)
  (*   apply H0. assumption. *)
  (*  - intros A B RA RB. *)
  (*    red. intros k HProper a HRA s. *)
  (*    eapply eqmR_bind_ret_l; auto. *)
  (*    + instantiate (1:=eq ⊗ RA). *)
  (*      do 2 red. *)
  (*      intros sa1 sa2 Hsa. *)
  (*      destruct sa1 as (s1 & a1). simpl. *)
  (*      destruct sa2 as (s2 & a2). simpl. *)
  (*      inversion Hsa. subst. *)
  (*      apply HProper. assumption. *)
  (*    + auto. *)
  (*  - intros. *)
  (*    unfold eqmR, EqmR_stateT in *. intros. *)
  (*    specialize (ma_OK s). *)
  (*    cbn in *. *)
  (*    Typeclasses eauto := 5. *)
  (*    setoid_rewrite <- surjective_pairing. *)
  (*    auto. *)
  (*    eapply eqmR_bind_ret_r; assumption. *)
  (*  - unfold eqmR, EqmR_stateT in *. *)
  (*    intros. *)
  (*    cbn in *. *)
  (*    eapply eqmR_bind_bind; try assumption. *)
  (*    + apply ma_OK. *)
  (*    + repeat red. *)
  (*      intros. destruct x. destruct y. *)
  (*      cbn. inversion H. subst. apply f_OK. assumption. *)
  (*    + repeat red. *)
  (*      intros. destruct x. destruct y. *)
  (*      cbn. inversion H. subst. apply g_OK. assumption. *)
  (* Qed. *)
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

End State.
