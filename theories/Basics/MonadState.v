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
     Basics.HeterogeneousRelations
     Basics.Monad.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Section State.
  Variable m : Type -> Type.
  Variable S : Type.
  Context {EqmRm : EqmR m}.
  Context {Mm : Monad m}.
  Context {EqmROKm : EqmR_OK m}.
  Context {ML : EqmRMonad m}.

  Global Instance EqmR_stateT : EqmR (stateT S m) :=
    {| eqmR :=
         fun A B (R : A -> B -> Prop)
             (f : stateT S m A) (g : stateT S m B) =>
           forall (s : S), eqmR (prod_rel eq R) (f s) (g s) |}.

  Global Instance EqmR_OK_stateT : EqmR_OK (stateT S m).
  Proof.
    split; unfold eqmR, EqmR_stateT; intros.
    - red. reflexivity.
    - red. symmetry; auto.
    - red. intros. eapply transitivity; eauto.
    - (* KS: Cannot unfold *) unfold eqmR. admit.
    - split; unfold subrelationH; unfold transpose in *; intros smb sma Heq s.
      + try pose proof s Heq. (* ?? *)
        admit.
      + admit.
    - do 3 red. intros. split; intros.
         +  specialize (H0 s). specialize (H1 s). specialize (H2 s).
            rewrite eq_rel_prod_eq in H0.
            rewrite eq_rel_prod_eq in H1.
            rewrite <- H0.
            rewrite <- H1.

            admit.
            (* rewrite H in H2. *)
            (* assumption. *)
         + specialize (H0 s). specialize (H1 s). specialize (H2 s).
           rewrite eq_rel_prod_eq in H0.
           rewrite eq_rel_prod_eq in H1.
           assert (eq_rel (prod_rel (@eq S) x) (prod_rel eq y)).
           admit. 
           (* { admit. rewrite H. reflexivity. } *)
           rewrite H3. rewrite H1. rewrite H0. assumption.
Admitted. 

  (* Global Instance EqMProps_stateT : @EqMProps (stateT S M) _ EqM_stateT. *)
  (* Proof. *)
  (* constructor. *)
  (* - repeat red. *)
  (*   reflexivity. *)
  (* - repeat red. intros. symmetry. apply H. *)
  (* - repeat red. intros. etransitivity; eauto. apply H.  apply H0. *)
  (* Qed. *)

  Lemma ret_ok :  forall (HS: inhabited S) {A1 A2} (RA : A1 -> A2 -> Prop) (a1:A1) (a2:A2),
      RA a1 a2 <-> (eqmR RA (ret a1) (ret a2)).
  Proof.
    unfold eqmR, EqmR_stateT.
    split; intros.
    - repeat red. apply eqmR_ret. assumption.
        constructor; auto.
    - inversion HS.
      specialize (H X).
      apply eqmR_ret in H. inversion H. assumption. assumption.
  Qed.

  Instance EqmRMonad_stateT (HS: inhabited S) : @EqmRMonad (stateT S m) _ _.
  Proof.
  constructor.
  - apply ret_ok. assumption.
  - intros.
    unfold eqmR, EqmR_stateT.
    intros s.
(*     eapply eqmR_bind. assumption. *)
(*     apply H. *)
(*     intros. destruct a1. destruct a2. *)
(*     cbn. unfold eqmR, EqmR_stateT in H0. *)
(*     inversion H1; subst. *)
(*     apply H0. assumption. *)
(*   - intros A B RA RB. *)
(*     do 5 red. intros x y H x0 y0 H0 s. *)
(*     unfold eqmR, EqmR_stateT. *)
(*     eapply eqmR_Proper_bind. *)
(*     + assumption. *)
(*     + apply H. *)
(*     + red. intros. *)
(*       destruct x1. destruct y1. simpl. *)
(*       inversion H1. subst. apply H0 in H7. apply H7. *)
(*   - intros. *)
(*     unfold eqmR, EqmR_stateT. *)
(*     intros. unfold eqmR. *)
(*     eapply eqmR_bind_ret_l. *)
(*     3: { eapply prod_morphism. reflexivity. apply a_OK. } *)
(*     assumption. *)
(*     repeat red. intros. destruct x. destruct y. simpl. *)
(*     inversion H. subst. apply f_OK. assumption. *)
(*   - unfold eqmR, EqmR_stateT in *. *)
(*     intros. *)
(*     unfold bind, Monad_stateT. *)
(*     cbn. *)
(*     assert (forall (x:S * A), EQmR _ _ eq ((fun (sa : S * A) => ret (fst sa, snd sa)) x)  ((fun (sa : S * A) => ret sa) x)). *)
(*     { intros. destruct x. cbn. apply eqmR_ret. assumption. reflexivity. } *)
(*     setoid_rewrite H. *)
(*     eapply eqmR_bind_ret_r. assumption. *)
(*     apply ma_OK. *)
(*   - intros A B C RA RB RC f f_OK g g_OK ma ma_OK. *)
(*     unfold eqmR, EqmR_stateT in *. cbn in *. *)
(*     intros. *)
(*     eapply eqmR_bind_bind. *)
(*     4 : apply ma_OK. *)
(*     + assumption. *)
(*     + repeat red. *)
(*       intros. destruct x. destruct y. *)
(*       cbn. inversion H. subst. apply f_OK. assumption. *)
(*     + repeat red. *)
(*       intros. destruct x. destruct y. *)
(*       cbn. inversion H. subst. apply g_OK. assumption. *)
(* Qed. *)
Admitted. 

  Context {Im: Iter (Kleisli m) sum}.
  Context {Cm: Iterative (Kleisli m) sum}.

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

  Definition internalize {a b:Type} (f : Kleisli (stateT S m) a b) : Kleisli m (S * a) (S * b) :=
    fun (sa : S * a) => f (snd sa) (fst sa).

  Lemma internalize_eq {a b:Type} (f g : Kleisli (stateT S m) a b) :
    eq2 f g <-> eq2 (internalize f) (internalize g).
  Proof.
    split.
    - intros.
      repeat red. destruct a0.
      unfold internalize. cbn.  specialize (H a0 s). unfold eqmR in H.
      rewrite eq_rel_prod_eq in H. apply H.
    - intros.
      repeat red. intros.
      unfold internalize in H.
      specialize (H (s, a0)).
      rewrite eq_rel_prod_eq.
      apply H.
  Qed.


  Lemma internalize_cat {a b c} (f : Kleisli (stateT S m) a b) (g : Kleisli (stateT S m) b c) :
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


  Lemma internalize_pure {a b c} (f : Kleisli (stateT S m) a b) (g : S * b -> S * c) :
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


  Global Instance Iter_stateT : Iter (Kleisli (stateT S m)) sum.
  Proof.
    exact
      (fun (a b : Type) (f : a -> S -> m (S * (a + b))) (x:a) (s:S) =>
        iter ((internalize f) >>> (pure iso)) (s, x)).
  Defined.

  Global Instance Proper_Iter_stateT : forall a b, @Proper (Kleisli (stateT S m) a (a + b) -> (Kleisli (stateT S m) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct Cm.
    repeat red.
    intros a b x y H a0 s.
    rewrite eq_rel_prod_eq.
    apply iterative_proper_iter.
    repeat red.
    destruct a1.
    cbn.
    apply Proper_bind.
    - unfold internalize. cbn. (specialize (H a1 s0)). rewrite eq_rel_prod_eq in H. apply H.
    - repeat red. destruct a2 as [s' [x1|y1]]; reflexivity.
 Qed.

  Global Instance IterUnfold_stateT : IterUnfold (Kleisli (stateT S m)) sum.
  Proof.
  destruct Cm.
  unfold IterUnfold.
  intros a b f.
  repeat red.
  intros a0 s.
  unfold cat, Cat_Kleisli.
  unfold iter, Iter_stateT.
  rewrite iterative_unfold.  (* SAZ: why isn't iter_unfold exposed here? *)
  unfold cat, Cat_Kleisli.
  simpl.
  rewrite bind_bind. rewrite eq_rel_prod_eq.
  apply Proper_bind.
  + reflexivity.
  + repeat red. destruct a1 as [s' [x | y]]; simpl.
    * unfold pure. rewrite bind_ret_l.
      reflexivity.
    * unfold pure. rewrite bind_ret_l.
      reflexivity.
  Qed.

  Global Instance IterNatural_stateT : IterNatural (Kleisli (stateT S m)) sum.
  Proof.
    destruct Cm.
    unfold IterNatural.
    intros a b c f g.
    repeat red.
    intros a0 s.
    setoid_rewrite iterative_natural. rewrite eq_rel_prod_eq.
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

  Lemma internalize_pure_iso {a b c} (f : Kleisli (stateT S m) a (b + c)) :
    ((internalize f) >>> pure iso) ⩯ (fun sa => (bind (f (snd sa) (fst sa))) (fun sbc => ret (iso sbc))).
  Proof.
    reflexivity.
  Qed.


  Lemma eq2_to_eqm : forall a b (f g : Kleisli (stateT S m) a b) (x:a) (s:S),
      eq2 f g ->
      eqm (f x s) (g x s).
  Proof.
    intros a b f g x s H.
    specialize (H x s). rewrite eq_rel_prod_eq in H.
    apply H.
  Qed.


  Lemma iter_dinatural_helper:
    forall (a b c : Type) (f : Kleisli (stateT S m) a (b + c)) (g : Kleisli (stateT S m) b (a + c)),
      internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_.
  Proof.
    destruct Cm.
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


  Global Instance IterDinatural_stateT : IterDinatural (Kleisli (stateT S m)) sum.
  Proof.
    destruct Cm.
    unfold IterDinatural.
    repeat red.
    intros a b c f g a0 a1.
    unfold iter, Iter_stateT.
    eapply transitivity. rewrite eq_rel_prod_eq.
    eapply iterative_proper_iter.
    apply iter_dinatural_helper.
    rewrite iterative_dinatural.
    cbn.
    unfold cat, Cat_Kleisli.
    rewrite bind_bind.
    unfold internalize. cbn. rewrite eq_rel_prod_eq.
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


  Global Instance IterCodiagonal_stateT : IterCodiagonal (Kleisli (stateT S m)) sum.
  Proof.
    destruct Cm.
    unfold IterCodiagonal.
    intros a b f.
    unfold iter, Iter_stateT.
    repeat red.
    intros.
    eapply transitivity. rewrite eq_rel_prod_eq.
    eapply iterative_proper_iter.
    eapply Proper_cat_Kleisli.

    assert (internalize (fun (x:a) (s:S) => iter (internalize f >>> pure iso) (s, x))
                       ⩯
                       iter (internalize f >>> pure iso)).
    { repeat red.
      intros a2.
      destruct a2.
      unfold internalize.
      cbn.  reflexivity.
    }
   apply H.
   reflexivity.
   eapply transitivity. rewrite eq_rel_prod_eq.

   eapply iterative_proper_iter.
   apply iterative_natural.
   rewrite iterative_codiagonal. rewrite eq_rel_prod_eq.
   eapply iterative_proper_iter.
   rewrite internalize_cat.
   (* SAZ This proof can probably use less unfolding *)
   repeat red. intros a2.
   destruct a2.
   unfold cat, Cat_Kleisli. cbn.
   repeat rewrite bind_bind.
   unfold internalize, pure.
   cbn.
   apply Proper_bind.
    - reflexivity.
    - repeat red.
      intros a3.
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

  Global Instance Iterative_stateT : Iterative (Kleisli (stateT S m)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

End State.
