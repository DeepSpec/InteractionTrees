From Coinduction Require Import all.
From Stdlib Require Import Morphisms.

From ITree Require Import
     Basics.HeterogeneousRelations
     Axioms
     ITree
     ITreeFacts
     EqAxiom
     Events.State
     Events.StateFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqBind
     Secure.SecureEqEuttHalt
     Secure.StrongBisimProper
     Secure.SecureEqWcompat
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac use_simpobs :=
  repeat match goal with
         | H : TauF _ = observe ?t |- _ => apply simpobs in H
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

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

Definition state_eqit_secure {R1 R2 : Type} (b1 b2 : bool) (RR : R1 -> R2 -> Prop)
           (m1 : stateT S (itree E2) R1) (m2 : stateT S (itree E2) R2) :=
  forall s1 s2, RS s1 s2 -> eqit_secure Label priv2 (prod_rel RS RR) b1 b2 l (m1 s1) (m2 s2).

Definition top2 {R1 R2} (r1 : R1) (r2 : R2) : Prop := True.


Definition secure_in_nonempty_context {R} (m : stateT S (itree E2) R) :=
   forall r' : R, state_eqit_secure true true top2 m (ret r').

Definition secure_in_empty_context  {R} (m : stateT S (itree E2) R) :=
   state_eqit_secure true true (@top2 R R) m (fun s => ITree.spin).

Inductive terminates (s1 : S) (P : forall A, E2 A -> Prop) : forall {A : Type}, itree E2 (S * A) -> Prop :=
| terminates_ret {R : Type} : forall (r : R) (s2 : S), RS s1 s2 -> terminates s1 P (Ret (s2, r))
| terminates_tau : forall A (t : itree E2 (S * A)) , terminates s1 P t -> terminates s1 P (Tau t)
| terminates_vis {A R : Type} : forall (e : E2 A) (k : A -> itree E2 (S * R)) , (forall v, terminates s1 P (k v)) -> P A e -> terminates s1 P (Vis e k)
.

Variant diverges_with' {E : Type -> Type} (P : forall A, E A -> Prop) (A : Type) (F : itree E A -> Prop) : itree' E A -> Prop :=
  | diverges_tau (t : itree E A): F t -> diverges_with' P A F (TauF t)
  | diverges_vis {B : Type} (e : E B) (k : B -> itree E A) : (forall a, F (k a)) -> P _ e -> diverges_with' P A F (VisF e k).

Definition diverges_with_  {E} (P : forall A, E A -> Prop) {A : Type} (F : itree E A -> Prop) :  itree E A -> Prop :=
  fun t => diverges_with' P A F (observe t).

Hint Constructors diverges_with' : itree.
Hint Unfold diverges_with_ : itree.

Lemma diverges_with_mono (E : Type -> Type) P A :
  Proper (respectful Coinduction.lattice.leq Coinduction.lattice.leq)
    (@diverges_with_ E P A).
Proof.
  intros F G HFG t Ht. red; red in Ht.
  inversion Ht; subst.
  - apply diverges_tau. apply HFG. auto.
  - apply diverges_vis; auto. intros a; apply HFG; auto.
Qed.

Definition diverges_with_mon {E} (P : forall A, E A -> Prop) (A : Type) :
  mon (itree E A -> Prop) := Build_mon (diverges_with_mono E P A).

Definition diverges_with {E} (P : forall A, E A -> Prop) {A : Type} : itree E A -> Prop :=
  gfp (diverges_with_mon P A).

#[global] Instance proper_diverges_with {E A} {P : forall A, E A -> Prop} : Proper (eq_itree eq ==> iff ) (@diverges_with E P A).
Proof.
  do 2 red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.


#[global] Instance proper_diverges_with_elem {E A} {P : forall A, E A -> Prop}
  (c : Chain (@diverges_with_mon E P A)) :
  Proper (eq_itree eq ==> iff) (elem c).
Proof.
  do 2 red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.

#[global] Instance proper_terminate {R s} {P : forall A, E2 A -> Prop} : Proper (eq_itree (@eq (S *R )) ==> iff) (terminates s P).
Proof.
  red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.


Lemma diverges_with_bind : forall E (P : forall A, E A -> Prop) (A B : Type) (k : A -> itree E B) (t : itree E A) ,
    diverges_with P t -> diverges_with P (ITree.bind t k).
Proof.
  intros E P A B k. coinduction c CIH. intros t Hdiv.
  step in Hdiv. cbn in Hdiv. inversion Hdiv; subst.
  - (* Tau case *)
    apply simpobs in H. rewrite H.
    rewrite bind_tau. apply diverges_tau. apply CIH; auto.
  - (* Vis case *)
    apply simpobs in H. rewrite H.
    rewrite bind_vis. cbn.
    apply diverges_vis; auto.
    intros a. apply CIH. apply H0.
Qed.

Lemma diverges_with_halt : forall E (A B : Type) (e : E A) (k : A -> itree E B) (P : forall A, E A -> Prop),
    P A e -> empty A -> diverges_with P (Vis e k).
Proof.
  intros. step. constructor; auto. intros; contra_size.
Qed.

Lemma diverges_secure_equiv_halt_r : forall A R1 R2 RR (e : E1 A) (k : A -> itree E1 R1) (t : itree E1 R2),
    empty A ->
    ~ leq (priv1 _ e) l ->
    eqit_secure Label priv1 RR true true l (Vis e k) t ->
    diverges_with (fun _ e => ~ leq (priv1 _ e) l) t.
Proof.
  intros A R1 R2 RR e k t Hemp Hsec. revert t. coinduction c CIH.
  intros. step in H. icbn. 
  cbn in *. remember (VisF e k) as ov.
  remember (observe t) as ot.
  hinduction H before S; intros; inv Heqov; ddestruction; subst; try discriminate;  try contradiction;
    try contra_size; use_simpobs.
  - etau. eapply CIH. now step.
  - evis. eapply CIH. now step. 
  - etau.
  - evis. eapply CIH; eauto. apply H.
  - evis. contra_size.
Qed.

Lemma diverges_secure_equiv_halt_l : forall A R1 R2 RR (e : E1 A) (k : A -> itree E1 R1) (t : itree E1 R2),
    empty A ->
    ~ leq (priv1 _ e) l ->
    eqit_secure Label priv1 RR true true l t (Vis e k) ->
    diverges_with (fun _ e => ~ leq (priv1 _ e) l) t.
Proof.
  intros A R1 R2 RR e k t Hemp Hsec. revert t. icoinduction c CIH.
  intros. step in H.  
  cbn in *. remember (VisF e k) as ov. remember (observe t) as ot.
  hinduction H before S; intros; inv Heqov; subst; ddestruction; subst; try discriminate;  try contradiction;
    try contra_size; use_simpobs.
  - etau. eapply CIH. now step.
  - evis. eapply CIH. now step.
  - etau. 
  - evis. contra_size. 
  - evis. eapply CIH; eauto. apply H.
Qed.

Lemma diverges_with_spin : forall E A P,
    diverges_with P (@ITree.spin E A).
Proof.
  intros. icoinduction c CIH. cbn. constructor.
  exact CIH. 
Qed.


Lemma eqit_secure_silent_diverge : forall A B RR (t1 : itree E2 A) (t2 : itree E2 B),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t1 ->
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t2 ->
    eqit_secure Label priv2 RR true true l t1 t2.
Proof.
  intros A B RR. coinduction c CIH. intros.
  step in H; step in H0.
  inversion H; inversion H0; use_simpobs; try rewrite H1; try rewrite H3. 
  - etau.  
  - destruct (classic_empty B0).
    + constructor; auto. step. clear H1. clear CIH.
    (* TOUR annoying: need coinduction bug fix *)
    change (gfp (diverges_with_mon (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) A) t)
    with (diverges_with (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) t) in H2. 
    generalize dependent t. coinduction c' CIH'. intros.
      sinv H2; use_simpobs.
      * rewrite H1. icbn; cbn. 
      unpriv_halt.  
      * rewrite H1. icbn; cbn. unpriv_halt. eapply CIH'; eauto. apply H7. 
    + cbn. unpriv_co. eapply CIH; eauto. apply H4.
  -  destruct (classic_empty B0).
    +  clear H4. clear CIH. step. 
       change (diverges_with' (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) B
(gfp (diverges_with_mon (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e)
l) B)) (observe t2)) with (diverges_with' (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) B (diverges_with (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l)) (observe t2)) in H0.
      generalize dependent t2. coinduction c' CIH. intros.
      inversion H0; use_simpobs.
      * rewrite H4. icbn; cbn. unpriv_halt. eapply CIH; eauto. now step in H7. 
      * rewrite H4. icbn; cbn. unpriv_halt. eapply CIH; eauto. unfold diverges_with. unstep. apply H7.  
    + rewrite H4. icbn; cbn. unpriv_co. eapply CIH; eauto. apply H2.
  -  rewrite H4.
    destruct (classic_empty B0); destruct (classic_empty B1).
    + icbn; cbn. unpriv_halt. contra_size.
    + assert (diverges_with (fun _ e => ~ leq (priv2 _ e) l) (Vis e0 k0)) by 
       (step; constructor; auto). 
      rewrite <- H4. rewrite <- H4 in H9. clear H4. clear H1 CIH. step.
      change (diverges_with' (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) B
      (gfp (diverges_with_mon (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) B)) (observe t2))
      with 
      (diverges_with' (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l) B
      (diverges_with (fun (A : Type) (e : E2 A) => ~ leq (priv2 A e) l)) (observe t2)) in H0. 
      generalize dependent t2.
      coinduction c0 CIH. intros. sinv H9; use_simpobs.
      * rewrite H1. icbn; cbn. unpriv_halt. eapply CIH; eauto. now step in H4.  
      * rewrite H1. icbn; cbn. unpriv_halt. eapply CIH; eauto. 
      specialize (H4 b). now step in H4. apply H4. 
    + assert (diverges_with (fun _ e => ~ leq (priv2 _ e) l) (Vis e k)) by 
       (step; constructor; auto). 
      rewrite <- H1. rewrite <- H1 in H9. clear H1. clear H CIH. step. generalize dependent t1.
      coinduction c0 CIH. intros. sinv H9; use_simpobs.
      * rewrite H. icbn; cbn. unpriv_halt.
      * rewrite H. icbn; cbn. unpriv_halt. eapply CIH; eauto. apply H1.
    + icbn; cbn. unpriv_co. eapply CIH; eauto. apply H2. apply H5.
Qed.

Lemma silent_diverges_eqit_secure_spin : forall A B (RR : A -> B -> Prop) (t : itree E2 A),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t <-> eqit_secure Label priv2 RR true true l t (ITree.spin).
Proof.
  intros. split.
  { intros. eapply eqit_secure_silent_diverge; eauto. apply diverges_with_spin. }
  revert t. coinduction c CIH.
  intros t Ht. step in Ht. remember (observe t) as ot.
  remember (observe ITree.spin) as otspin.
  hinduction Ht before S; intros; subst; try discriminate; use_simpobs.
  -  rewrite Heqot. constructor. eapply CIH; eauto. rewrite Heqotspin.
    step; constructor; auto. now unstep.
  - rewrite Heqot. constructor. step. eapply IHHt; eauto.
  - eapply IHHt; eauto. assert (ITree.spin ≅ t2) by now sinv Heqotspin. 
    apply EqAxiom.bisimulation_is_eq in H. subst; auto.
  - rewrite Heqot. constructor; auto; intros. eapply CIH; eauto. rewrite Heqotspin.
    step; etau. now unstep. 
  - rewrite Heqot. evis. step. eapply H0; eauto.
  - rewrite Heqot. evis. eapply CIH; eauto.
    rewrite Heqotspin. step; constructor; auto. unstep. eapply unpriv_e_eqit_secure; eauto.
Qed.


Lemma silent_terminates_eqit_secure_ret : forall R (m : stateT S (itree E2) R), nonempty R ->
      (forall s, terminates s (fun B e => ~ leq (priv2 _ e) l /\ nonempty B) (m s) ) <-> forall r' : R, state_eqit_secure true true top2 m (ret r').
Proof.
  split; intros.
  - red. intros. specialize (H0 s1).
    cbn. induction H0.
    + step; constructor. split; try constructor. cbn. etransitivity; [symmetry|]; eauto. 
    + step; constructor; auto. unstep. eapply IHterminates; eauto.
    + destruct H3. step. cbn. timeout 10 setoid_rewrite itree_eta' at 2.  unpriv_ind.
      unstep. eapply H2; eauto.
  - cbn in *. red in H0. assert (RS s s). reflexivity.
    inv H.
    specialize (H0 a s s H1). remember (m s) as t. clear Heqt.
    step in H0. cbn in H0. remember (RetF (s,a) ) as oret. remember (observe t) as ot.
    hinduction H0 before E1; intros; try discriminate; use_simpobs.
    + rewrite Heqot. injection Heqoret; intros; subst. destruct r1, H. cbn in *.
      constructor. symmetry. auto.
    + rewrite Heqot. constructor. eapply IHsecure_eqitF; eauto.
    + rewrite Heqot. constructor; eauto.
Qed.

Variant handler_respects_priv (A : Type) (e : E1 A) : Prop :=
| respect_private (SECCHECK : ~ leq (priv1 _ e) l)
                  (FINCHECK : forall s, terminates s (fun _ e' => ~ leq (priv2 _ e') l) (handler A e s))
| respect_public (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e))
.

Variant handler_respects_priv' (A : Type) (e : E1 A) : Prop :=
| respect_private_ne (SECCHECK : ~ leq (priv1 _ e) l) (SIZECHECK : nonempty A)
                  (FINCHECK :  forall s, terminates s (fun B e' => ~ leq (priv2 _ e') l /\ nonempty B ) (handler A e s) )
| respect_private_e (SECCHECK : ~ leq (priv1 _ e) l) (SIZECHECK : empty A)
                  (DIVCHECK : forall s, diverges_with (fun _ e' => ~ leq (priv2 _ e') l ) (handler A e s) )
| respect_public' (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e))
.

Context (Hhandler : forall A (e : E1 A), handler_respects_priv' A e).

Lemma diverge_with_respectful_handler : forall (R : Type) (t : itree E1 R),
    diverges_with (fun _ e => ~ leq (priv1 _ e) l ) t ->
    forall s, diverges_with (fun _ e => ~ leq (priv2 _ e) l) (interp_state handler t s).
Proof.
  intro R. coinduction c CIH. intros t Hdiv s. sinv Hdiv; use_simpobs.
  - rewrite H. rewrite interp_state_tau. constructor. eapply CIH; eauto.
  - rewrite H. rewrite interp_state_vis.
    destruct (classic_empty B).
    + specialize (Hhandler _ e). destruct Hhandler; try contradiction; try contra_size.
      specialize (DIVCHECK s). step. eapply diverges_with_bind; eauto.
    + specialize (Hhandler _ e). destruct Hhandler; try contradiction; try contra_size.
      specialize (FINCHECK s). induction FINCHECK.
      * rewrite bind_ret_l. cbn. etau. eapply CIH; eauto. apply H0.
      * rewrite bind_tau. etau. step. eapply IHFINCHECK; eauto.
      * destruct H5. rewrite bind_vis. evis. step. eapply H4; eauto.
Qed.

Lemma interp_eqit_secure_state : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E1 R2),
    eqit_secure Label priv1 RR true true l t1 t2 ->
    state_eqit_secure true true RR (interp_state handler t1) (interp_state handler t2).
Proof.
  intros R1 R2 RR. coinduction c CIH. intros t1 t2 Ht s1 s2 Hs. step in Ht.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Ht before l; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. rewrite 2 interp_state_ret. eret.
  - rewrite Heqot1. rewrite Heqot2. rewrite 2 interp_state_tau. etau.
  - rewrite Heqot1. rewrite interp_state_tau. constructor; auto. eapply IHHt; eauto.
  - rewrite Heqot2. rewrite interp_state_tau. constructor; auto. eapply IHHt; eauto.
  - rewrite Heqot1. rewrite Heqot2. rewrite 2 interp_state_vis.
    specialize (Hhandler A e). repeat rewrite bind_tau.
    repeat setoid_rewrite <- interp_state_tau. inv Hhandler; try contradiction.
    specialize (RESCHECK s1 s2 Hs).
    eapply secure_eqit_bind_chain; eauto. intros [] [] []. simpl in *. subst.
    rewrite 2 interp_state_tau. constructor. eapply CIH; eauto. apply H.
  - rewrite Heqot1. rewrite Heqot2. rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. constructor. apply CIH. apply H. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. constructor 3; auto. eapply IHFINCHECK; eauto.
    + rewrite bind_vis. destruct H2. constructor 9; auto. intros. eapply H1; eauto.
  - rewrite Heqot1. rewrite Heqot2. rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. constructor. apply CIH. apply H. etransitivity; eauto.
    + rewrite bind_tau. constructor 4; auto. eapply IHFINCHECK; eauto.
    + rewrite bind_vis. destruct H2. constructor 10; auto. intros. eapply H1; eauto.
  - rewrite Heqot1. rewrite Heqot2. rewrite 2 interp_state_vis.
    specialize (Hhandler _ e1) as He1. specialize (Hhandler _ e2) as He2.
    inv He1; inv He2; try contradiction; try contra_size.
    eapply secure_eqit_bind_chain with (RR := prod_rel RS (fun _ _ => True)).
    2: { intros [s1' a1] [s2' a2] [Hs' Hgar]. simpl in *. constructor. apply CIH. apply H. apply Hs'. }
    specialize (FINCHECK s1). specialize (FINCHECK0 s2). induction FINCHECK.
    + induction FINCHECK0.
      * simpl. step. constructor. split; auto. simpl. transitivity s2; eauto. etransitivity; [symmetry |]; eauto.
      * step. constructor; auto. unstep. eapply IHFINCHECK0; eauto.
      * step. destruct H3. constructor; auto. intros. unstep. eapply H2; eauto.
    + step. constructor; auto. unstep. eapply IHFINCHECK; eauto.
    + step. destruct H2. constructor; auto. intros. unstep. eapply H1; eauto.
  - rewrite Heqot1. rewrite interp_state_vis. pose proof (Hhandler _ e) as He.
    inv He; try contradiction; try contra_size.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. constructor; auto. eapply H0; eauto. simpl. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. constructor 3; auto. eapply IHFINCHECK; eauto.
    + rewrite bind_vis. destruct H3. constructor 9; auto. intros. eapply H2; eauto.
  - rewrite Heqot2. rewrite interp_state_vis. pose proof (Hhandler _ e) as He.
    inv He; try contradiction; try contra_size.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. constructor 4; auto. eapply H0; eauto. simpl. etransitivity; eauto.
    + rewrite bind_tau. constructor 4; auto. eapply IHFINCHECK; eauto.
    + rewrite bind_vis. destruct H3. constructor 10; auto. intros. eapply H2; eauto.
  - rewrite Heqot1. rewrite interp_state_vis. rewrite Heqot2. rewrite interp_state_tau.
    pose proof Hhandler as Hhandler'. specialize (Hhandler' _ e). inv Hhandler'; try contradiction; try contra_size.
    step. eapply eqit_secure_silent_diverge.
    + eapply diverges_with_bind; eauto.
    + step. constructor. eapply diverge_with_respectful_handler; eauto. eapply diverges_secure_equiv_halt_r; eauto.
  - rewrite Heqot1. rewrite interp_state_tau. rewrite Heqot2. rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'. specialize (Hhandler' _ e). inv Hhandler'; try contradiction; try contra_size.
    step. eapply eqit_secure_silent_diverge.
    + step. constructor. eapply diverge_with_respectful_handler; eauto. eapply diverges_secure_equiv_halt_l; eauto.
    + eapply diverges_with_bind; eauto.
  - rewrite Heqot1. rewrite Heqot2. rewrite 2 interp_state_vis.
    pose proof Hhandler as Hhandler'. pose proof Hhandler as Hhandler''.
    specialize (Hhandler'' _ e2). inv Hhandler''; try contradiction; try contra_size.
    { specialize (Hhandler' _ e1). inv Hhandler'; try contradiction; try contra_size.
     step. eapply eqit_secure_silent_diverge.
      - eapply diverges_with_bind; eauto.
      - specialize (FINCHECK s2). induction FINCHECK.
        + rewrite bind_ret_l. step. constructor. cbn. eapply diverge_with_respectful_handler; eauto. eapply diverges_secure_equiv_halt_r; eauto. apply H.
        + rewrite bind_tau. step. constructor. eapply IHFINCHECK; eauto.
        + rewrite bind_vis. step. constructor; auto. intros. eapply H1; eauto. destruct H2; auto. }
        { specialize (Hhandler' _ e1). inv Hhandler'; try contradiction; try contra_size.
        step. eapply eqit_secure_silent_diverge.
        + eapply diverges_with_bind; eauto.
        + eapply diverges_with_bind; eauto. }
  - rewrite Heqot1, Heqot2. rewrite 2 interp_state_vis. 
    pose proof Hhandler as Hhandler'. pose proof Hhandler as Hhandler''.
    specialize (Hhandler'' _ e2). specialize (Hhandler' _ e1).   
    inv Hhandler'; try contradiction; try contra_size.
    { inv Hhandler''; try contradiction; try contra_size. 
     step. eapply eqit_secure_silent_diverge.
      - specialize (FINCHECK s1). induction FINCHECK.
        + rewrite bind_ret_l. step. constructor. cbn. eapply diverge_with_respectful_handler; eauto. eapply diverges_secure_equiv_halt_l; eauto.  apply H.
        + rewrite bind_tau. step. constructor. eapply IHFINCHECK; eauto.
        + rewrite bind_vis. step. constructor; auto. intros. eapply H1; eauto. destruct H2; auto.
      - eapply diverges_with_bind; eauto.   
        }
        { inv Hhandler''; try contradiction; try contra_size.
        step. eapply eqit_secure_silent_diverge.
        + eapply diverges_with_bind; eauto.
        + eapply diverges_with_bind; eauto. }
Qed. 

End GeneralStateHandler.
