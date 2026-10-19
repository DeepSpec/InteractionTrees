From Coinduction Require Import all. 
From Stdlib Require Import Morphisms.
From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecureEqProgInsens
     Secure.SecureEqProgInsensFacts
     Secure.StrongBisimProper
     Secure.SecureStateHandler
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section GeneralStateHandler.

Context (S : Type).
Context (RS : S -> S -> Prop).
Context (RS_Eq: Equivalence RS).

Context (E1 E2 : Type -> Type).

Context (handler : E1 ~> stateT S (itree E2) ).

Context (Label : Preorder).
Context (priv1 : forall A, E1 A -> L).
Context (priv2 : forall A, E2 A -> L).
Context (l : L).

Definition state_pi_eqit_secure {R1 R2 : Type} (b1 b2 : bool) (RR : R1 -> R2 -> Prop)
           (m1 : stateT S (itree E2) R1) (m2 : stateT S (itree E2) R2) :=
  forall s1 s2, RS s1 s2 -> pi_eqit_secure Label priv2 (prod_rel RS RR) b1 b2 l (m1 s1) (m2 s2).

Definition top2 {R1 R2} (r1 : R1) (r2 : R2) : Prop := True.

Definition secure_in_nonempty_context {R} (m : stateT S (itree E2) R) :=
   forall r' : R, state_pi_eqit_secure true true top2 m (ret r').

Definition secure_in_empty_context  {R} (m : stateT S (itree E2) R) :=
   state_pi_eqit_secure true true (@top2 R R) m (fun s => ITree.spin).

Lemma diverges_with_spin : forall E A P,
    diverges_with P (@ITree.spin E A).
Proof.
  intros. icoinduction c CIH. cbn. etau. 
Qed.

Lemma pi_eqit_secure_silent_divergel : forall A B RR (t1 : itree E2 A) (t2 : itree E2 B),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t1 ->
    pi_eqit_secure Label priv2 RR true true l t1 t2.
Proof.
  intros A B RR. coinduction c CIH. intros.
  step in H. all : try apply mono_diverges_with. 
  inversion H; use_simpobs; try rewrite H0; try rewrite H1.
  - etau. 
  - destruct (classic_empty B0).
    + step. 
      apply pi_eqit_secure_sym.
      apply pi_eqit_secure_private_halt; auto.
    + icbn. evis. eapply CIH; eauto. apply H1.
 Qed.

Lemma pi_eqit_secure_silent_diverger : forall A B RR (t1 : itree E2 A) (t2 : itree E2 B),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t2 ->
    pi_eqit_secure Label priv2 RR true true l t1 t2.
Proof.
  intros. apply pi_eqit_secure_sym. apply pi_eqit_secure_silent_divergel; auto.
Qed.


Lemma silent_terminates_eqit_secure_ret : forall R (m : stateT S (itree E2) R), nonempty R ->
      (forall s, terminates S RS E2 s (fun B e => ~ leq (priv2 _ e) l /\ nonempty B) (m s) ) -> forall r' : R, state_pi_eqit_secure true true top2 m (ret r').
Proof.
  red. intros. specialize (H0 s1).
  cbn. induction H0.
  - step; constructor. split; try constructor. cbn. etransitivity; [symmetry|]; eauto.
  - step; constructor; auto. apply IHterminates; auto. 
  - apply pi_eqit_secure_priv_visl; auto. destruct H3. auto.
Qed.


Variant handler_respects_priv (A : Type) (e : E1 A) : Prop :=
| respect_private' (SECCHECK : ~ leq (priv1 _ e) l)
                 (RESCHECK : state_pi_eqit_secure true true top2 (handler A e) (ret tt) )
| respect_public'' (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_pi_eqit_secure true true eq (handler A e) (handler A e))
.

Context (Hhandler : forall A (e : E1 A), handler_respects_priv A e).


Lemma diverges_with_bind : forall E R S P (t : itree E R) (k : R -> itree E S),
    diverges_with P t -> diverges_with P (ITree.bind t k).
Proof.
  intros E R1 R2 P. icoinduction c CIH.
  intros t k Ht. step in Ht. 
  unfold observe. inv Ht; cbn; simpobs. 
  - etau.
  - evis. eapply CIH; eauto. apply H0.
Qed.

Lemma interp_pi_eqit_secure_state : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E1 R2),
    pi_eqit_secure Label priv1 RR true true l t1 t2 ->
    state_pi_eqit_secure true true RR (interp_state handler t1) (interp_state handler t2).
Proof.

  intros R1 R2 RR. coinduction c CIH. intros t1 t2 Ht s1 s2 Hs. step in Ht.
  inv Ht; intros; use_simpobs.
  - rewrite H, H0. repeat rewrite interp_state_ret. eret. 
  - rewrite H, H0. repeat rewrite interp_state_tau. etau. 
  - rewrite H. rewrite interp_state_tau. etau. 
    eapply CIH; eauto. apply simpobs in H0. rewrite <- itree_eta in H0.
    rewrite H0. auto.
  - rewrite H0. rewrite interp_state_tau. etau. 
    eapply CIH; eauto. apply simpobs in H. rewrite <- itree_eta in H.
    rewrite H. auto.
  - rewrite H, H0.
    repeat rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction.
    eapply pi_eqit_secure_bind; eauto.
    intros. destruct H2; destruct r1; destruct r2; cbn in *; subst.
    constructor. eapply CIH; eauto. apply H1.
  - rewrite H, H0.  rewrite interp_state_tau.
    constructor; auto. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction.
    red in RESCHECK. apply RESCHECK in Hs as He.
    remember (handler A e s1) as t3. clear Heqt3.
    generalize dependent t3. accumulate CIH'. 
    intros t3 Ht3. cbn in Ht3. sinv Ht3; use_simpobs; subst.
    + destruct H4. destruct r1. cbn in *|-.
      rewrite H2. rewrite bind_ret_l. constructor; auto.
      eapply CIH; eauto. cbn. apply H1.
    + rewrite H2. rewrite bind_tau. constructor; auto.
      eapply CIH'; eauto. symmetry in H3. use_simpobs.
      rewrite <- H3. auto.
    + rewrite H2. rewrite bind_vis. constructor; auto.
      intros. eapply CIH'; eauto. symmetry in H3.
      use_simpobs. rewrite <- H3. apply H4.
 - rewrite H, H0.  rewrite interp_state_tau.
    constructor; auto. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction.
    red in RESCHECK. symmetry in Hs. apply RESCHECK in Hs as He.
    remember (handler A e s2) as t3. clear Heqt3.
    cbn in He. generalize dependent t3. accumulate CIH'.
    intros t3 Ht3. sinv Ht3; use_simpobs; subst.
    + destruct H4. destruct r1. cbn in *|-.
      rewrite H2. rewrite bind_ret_l. constructor; auto.
      eapply CIH; eauto. cbn. apply H1.
      symmetry. auto.
    + rewrite H2. rewrite bind_tau. constructor; auto.
      eapply CIH'; eauto. symmetry in H3. use_simpobs.
      rewrite <- H3. auto.
    + rewrite H2. rewrite bind_vis. constructor; auto.
      intros. eapply CIH'; eauto. symmetry in H3.
      use_simpobs. rewrite <- H3. apply H4.
 -  rewrite H, H0. repeat rewrite interp_state_vis.
   specialize (Hhandler A e1) as He1. specialize (Hhandler B e2) as He2.
   inv He1; inv He2; try contradiction.
   eapply pi_eqit_secure_bind with (RR := prod_rel RS top2); eauto.
   + intros [? ?] [? ?] [? ?]. constructor.
     eapply CIH; eauto. apply H1.
   + apply pi_eqit_secure_RR_imp with
                   (RR1 := rcompose (prod_rel RS (@top2 A unit)) (prod_rel RS top2) ).
     { intros. inv H2. destruct REL1. destruct REL2. split; auto.
       etransitivity; eauto. }
     cbn in *. eapply pi_eqit_secure_trans_ret; eauto.
     apply pi_eqit_secure_sym. apply pi_eqit_secure_RR_imp with
                                   (RR1 := prod_rel RS top2).
     { intros. inv H2.  }
     eapply RESCHECK0. reflexivity.
 - apply simpobs in H0. rewrite <- itree_eta in H0. 
   rewrite H. rewrite H0. rewrite interp_state_vis.
   specialize (Hhandler A e). inv Hhandler; try contradiction.
   red in RESCHECK. apply RESCHECK in Hs as He.
    remember (handler A e s1) as t3. clear Heqt3.
    (* TOUR: PROBLEM
    The proof we want: 
    cbn in He. generalize dependent t3. accumluate CIH'.
    intros t3 Ht3. sinv Ht3; use_simpobs; subst.
    + destruct H4. cbn in *. destruct r1. cbn in *.
      rewrite H2. rewrite bind_ret_l. gstep. constructor; auto.
      eapply CIH; eauto. cbn. apply H1.
    + rewrite H2. rewrite bind_tau. gstep; constructor; auto.
      eapply CIH'; eauto. symmetry in H3. use_simpobs.
      rewrite <- H3. auto.
    + rewrite H2. rewrite bind_vis. gstep. constructor; auto.
      intros. eapply CIH'; eauto. symmetry in H3.
      use_simpobs. rewrite <- H3. apply H4.

      or coinduction instead of accumulate. problem: 
      we are at b (elem c), not elem c, so we cannot use accumulate. 
    *)
    cbn in *|-. step in He. 
    remember (observe (Ret (s2, tt))).
    icbn. rewrite observe_bind. 
    hinduction He before CIH; intros; try easy.
    + inv H. inv Heqi. cbn in *. constructor; auto. cbn. 
    eapply CIH; eauto. simpobs_subst. apply H1.  
    + constructor 3; auto. step in H. rewrite Heqi in H. clear Heqi. 
    generalize dependent t1. 
    accumulate CIH'. 
    intros t1 H. icbn.
      rewrite observe_bind. inv H. 
      * constructor; auto. 
        inv H5. cbn in *. 
        eapply CIH; eauto. apply H1. 
      * constructor; auto. eapply CIH'. rewrite <- H4. rewrite <- itree_eta'. now unstep.  
      * constructor; auto; intro. eapply CIH'; eauto. rewrite <- H4. rewrite <- itree_eta'. now unstep.  
    + constructor 9; auto. intros.
      rename t4 into t5. 
      remember (k1 a) as t4.
      specialize (H a). step in H. 
      rewrite <- Heqt4 in H. clear Heqt4. 
      generalize dependent t4. 
      accumulate CIH'. 
      intros t4 H.
      icbn. rewrite observe_bind. 
      dependent induction H; simpobs; try easy. 
      * constructor; auto. 
        inv H. inv Heqi. cbn in *. 
        eapply CIH; eauto. apply H1. 
      * constructor; auto. eapply CIH'. unstep. apply H.  
      * constructor; auto; intro. eapply CIH'. unstep. apply H. 
      
 - apply simpobs in H. rewrite <- itree_eta in H. 
   rewrite H0. rewrite H. rewrite interp_state_vis.
   specialize (Hhandler A e). inv Hhandler; try contradiction.
   red in RESCHECK. symmetry in Hs. apply RESCHECK in Hs as He.
    remember (handler A e s1) as t3. clear Heqt3.
    (* TOUR: PROBLEM
    The proof we want: 
    cbn in He. generalize dependent t3. accumluate CIH'.
    intros t3 Ht3. sinv Ht3; use_simpobs; subst.
    + destruct H4. cbn in *. destruct r1. cbn in *.
      rewrite H2. rewrite bind_ret_l. gstep. constructor; auto.
      eapply CIH; eauto. cbn. apply H1.
    + rewrite H2. rewrite bind_tau. gstep; constructor; auto.
      eapply CIH'; eauto. symmetry in H3. use_simpobs.
      rewrite <- H3. auto.
    + rewrite H2. rewrite bind_vis. gstep. constructor; auto.
      intros. eapply CIH'; eauto. symmetry in H3.
      use_simpobs. rewrite <- H3. apply H4.

      or coinduction instead of accumulate. problem: 
      we are at b (elem c), not elem c, so we cannot use accumulate. 
    *)
    cbn in *|-. step in He. 
    remember (observe (Ret (s1, tt))).
    icbn. rewrite observe_bind. 
    hinduction He before CIH; intros; try easy.
    + inv H. inv Heqi. cbn in *. constructor; auto. cbn. 
    eapply CIH; eauto. simpobs_subst. apply H1. now symmetry.   
    + constructor 4; auto. step in H. rewrite Heqi in H. clear Heqi. 
    generalize dependent t1. 
    accumulate CIH'. 
    intros t1 H. icbn.
      rewrite observe_bind. inv H. 
      * constructor; auto. 
        inv H5. cbn in *. 
        eapply CIH; eauto. apply H1. now symmetry.  
      * constructor; auto. eapply CIH'. rewrite <- H4. rewrite <- itree_eta'. now unstep.  
      * constructor; auto; intro. eapply CIH'; eauto. rewrite <- H4. rewrite <- itree_eta'. now unstep.  
    + constructor 10; auto. intros.
      rename t4 into t5. 
      remember (k1 a) as t4.
      specialize (H a). step in H. 
      rewrite <- Heqt4 in H. clear Heqt4. 
      generalize dependent t4. 
      accumulate CIH'. 
      intros t4 H.
      icbn. rewrite observe_bind. 
      dependent induction H; simpobs; try easy. 
      * constructor; auto. 
        inv H. inv Heqi. cbn in *. 
        eapply CIH; eauto. apply H1. now symmetry.  
      * constructor; auto. eapply CIH'. unstep. apply H.  
      * constructor; auto; intro. eapply CIH'. unstep. apply H. 
Qed. 
End GeneralStateHandler.
