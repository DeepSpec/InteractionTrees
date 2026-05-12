From Coinduction Require Import all. 

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
    
     Secure.SecureEqHalt
     Secure.SecureEqWcompat
     Secure.SecureEqEuttHalt
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma eqit_bind_shalt_aux1:
  forall (E : Type -> Type) (S2 S1 R1 R2 : Type) (RR : R1 -> R2 -> Prop)
    (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (k1 : R1 -> itree E S1)
    (k2 : R2 -> itree E S2) (A : Type) (e : E A) (k0 : A -> itree E R1)
    (t2 : itree E R2),
    ~ leq (priv A e) l ->
    empty A ->
    eqit_secure Label priv RR b1 b2 l (Vis e k0) t2 ->
    forall (t1 : itree E R1),
      VisF e k0 = observe t1 ->
      eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros E S2 S1 R1 R2 RR RS b1 b2 Label priv l k1 k2 A e k0 t2 SECCHECK SIZECHECK H0 t1 Heqot1.
  step. unfold ITree.bind at 1, observe at 1. cbn. simpobs.
  cbn. rewrite itree_eta' at 1. unstep. 
  generalize dependent t2. coinduction c CIH. intros t2 Ht2.
  step in Ht2. icbn.  
  unfold ITree.bind at 1. unfold observe at 2. cbn in *.
  inv Ht2; ddestruction; subst; try contra_size; try contradiction; try rewrite <- H; cbn;
  try unpriv_halt; eapply CIH; eauto;
  try solve [step; rewrite H in H1; apply H1].
  - now step. 
  - apply H0. 
  - contra_size. 
Qed.

Lemma eqit_bind_shalt_aux2:
  forall (E : Type -> Type) (S2 S1 R1 R2 : Type) (RR : R1 -> R2 -> Prop)
    (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (k1 : R1 -> itree E S1)
    (k2 : R2 -> itree E S2) (A : Type) (e : E A) (k0 : A -> itree E R2)
    (t1 : itree E R1) (t2 : itree E R2),
    ~ leq (priv A e) l ->
    empty A ->
    eqit_secure Label priv RR b1 b2 l t1 (Vis e k0) ->
    VisF e k0 = observe t2 ->
    eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros E S2 S1 R1 R2 RR RS b1 b2 Label priv l k1 k2 A e k0 t1 t2 SECCHECK SIZECHECK H0 Heqot1.
  step. unfold ITree.bind at 2, observe at 2. cbn. simpobs.
  cbn. rewrite itree_eta'. unstep.
  generalize dependent t1. coinduction c CIH. intros t1 Ht1.
  step in Ht1. icbn.  
  unfold ITree.bind at 1, observe at 1. cbn in *.
  inv Ht1; ddestruction; subst; try contra_size; try contradiction; cbn;
  try unpriv_halt; try contra_size; try (eapply CIH; eauto).
  - now step. 
  - rewrite <- H0. step. apply H1. 
  - apply H1.  
Qed.

#[local] Ltac to_mon_s := 
match goal with 
| |- secure_eqitF ?Label ?priv ?RR ?b1 ?b2 ?l ?sim (observe ?t1) (observe ?t2) =>
  change (secure_eqit_mon Label priv RR b1 b2 l sim t1 t2)
  end.

Lemma secure_eqit_bind' : forall E R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)
                           b1 b2 Label priv l
    (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2),
    (forall r1 r2, RR r1 r2 -> eqit_secure Label priv RS b1 b2 l (k1 r1) (k2 r2) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. revert H0. revert t1 t2. icoinduction c CIH. intros t1 t2 Ht12.
  step in Ht12.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before E; intros.
  - unfold ITree.bind, observe; cbn. 
    simpobs. step. now apply H0. 
  - unfold ITree.bind, observe. 
    cbn; simpobs; cbn. 
 constructor. now eapply CIH.  
  - unfold ITree.bind at 1, observe at 1. 
    cbn; simpobs; cbn. 
 constructor; auto.
    apply IHHt12; eauto.  
  - unfold ITree.bind at 2, observe at 2. 
    cbn; simpobs; cbn. 
 constructor; auto. apply IHHt12; eauto.
  - unfold ITree.bind, observe. 
    cbn; simpobs; cbn.
    evis.  
    eapply CIH, H.
  - unfold ITree.bind, observe. 
    cbn; simpobs; cbn. 
    unpriv_co.
    eapply CIH, H.
  - unfold ITree.bind, observe. 
    cbn; simpobs; cbn. 
    unpriv_co.
    eapply CIH, H.
  - unfold ITree.bind, observe. 
    cbn; simpobs; cbn. 
    unpriv_co.
    eapply CIH, H.
  - unfold ITree.bind at 1, observe at 1. 
    cbn. rewrite <- Heqot1. cbn. 
    unpriv_ind. eapply H0; eauto.
  - unfold ITree.bind at 2, observe at 2. 
    cbn; rewrite <- Heqot2; cbn. 
    unpriv_ind. eapply H0; eauto. 
  - step. 
    eapply eqit_bind_shalt_aux1; eauto. step. simpobs.
    cbn. unpriv_halt. eauto.
  - step. 
    eapply eqit_bind_shalt_aux2; eauto. step. cbn. simpobs.
    unpriv_halt. eauto.
  - step. 
    eapply eqit_bind_shalt_aux1 with (A := A); eauto.
    step. simpobs. cbn. unpriv_halt.
  - step. 
    eapply eqit_bind_shalt_aux2; eauto. step. cbn. simpobs.
    unpriv_halt.
Qed.

Lemma secure_eqit_bind : forall E R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)
                           b1 b2 Label priv l
    (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2),
    (forall r1 r2, RR r1 r2 -> eqit_secure Label priv RS b1 b2 l (k1 r1) (k2 r2) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros.
  eapply secure_eqit_bind'; eauto.
Qed.

Lemma iter_bind_shalt_aux1:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) (r : itree E B1 -> itree E B2 -> Prop)
    (A : Type) (e : E A) (k1 : A -> itree E (A1 + B1)) (t0 : itree E (A2 + B2)),
    ~ leq (priv A e) l ->
    empty A ->
    eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l
          (Vis e k1) t0 ->
    eqit_secure Label priv RB b1 b2 l
          (Vis e
               (fun x : A =>
                  ITree.bind (k1 x)
                             (fun lr : A1 + B1 =>
                                match lr with
                                | inl l0 => Tau (ITree.iter body1 l0)
                                | inr r0 => Ret r0
                                end)))
          (ITree.bind t0
                      (fun lr : A2 + B2 =>
                         match lr with
                         | inl l0 => Tau (ITree.iter body2 l0)
                         | inr r0 => Ret r0
                         end)).
Proof.
  intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 r A e k1 t0 SECCHECK SIZECHECK H.
  generalize dependent t0. coinduction c CIH. intros t0 Ht0.
  icbn. step in Ht0. rewrite observe_bind.   
   cbn in *. inv Ht0; inv_vis_secure; cbn;  unpriv_halt; try contra_size;
    eauto.
  all: 
  eapply CIH; eauto. 
  - now step.
  - simpobs. now step. 
  - apply H0. 
Qed.

Lemma iter_bind_shalt_aux2:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) 
    (* (r : itree E B1 -> itree E B2 -> Prop) *)
    (A : Type) (e : E A) (t0 : itree E (A1 + B1)) (k2 : A -> itree E (A2 + B2)),
    ~ leq (priv A e) l ->
    empty A ->
    eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l t0
          (Vis e k2) ->
    eqit_secure Label priv RB b1 b2 l
          (ITree.bind t0
                      (fun lr : A1 + B1 =>
                         match lr with
                         | inl l0 => Tau (ITree.iter body1 l0)
                         | inr r0 => Ret r0
                         end))
          (Vis e
               (fun x : A =>
                  ITree.bind (k2 x)
                             (fun lr : A2 + B2 =>
                                match lr with
                                | inl l0 => Tau (ITree.iter body2 l0)
                                | inr r0 => Ret r0
                                end))).
Proof.
  intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 A e t0 k2 SECCHECK SIZECHECK H.
  generalize dependent t0. coinduction c CIH. intros t0 Ht0.
  icbn. step in Ht0.
  rewrite observe_bind.   
   cbn in *. inv Ht0; inv_vis_secure; cbn;  unpriv_halt; try contra_size;
    eauto.
  all: 
  eapply CIH; eauto.
  - now step.
  - simpobs. now step. 
  - apply H1.
Qed.

Lemma iter_bind_aux:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) 
    (r : itree E B1 -> itree E B2 -> Prop)
    (t1 : itree E (A1 + B1)) (t2 : itree E (A2 + B2)),
    eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l t1 t2 ->
    (forall (a1 : A1) (a2 : A2), RA a1 a2 -> r (ITree.iter body1 a1) (ITree.iter body2 a2)) ->
    eqit_secure Label priv RB b1 b2 l 
          (ITree.bind t1
                      (fun lr : A1 + B1 =>
                         match lr with
                         | inl l0 => Tau (ITree.iter body1 l0)
                         | inr r0 => Ret r0
                         end))
          (ITree.bind t2
                      (fun lr : A2 + B2 =>
                         match lr with
                         | inl l0 => Tau (ITree.iter body2 l0)
                         | inr r0 => Ret r0
                         end)).
Proof.
Admitted.
  (* intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 r t1 t2 H CIH0.
  generalize dependent t2. revert t1. coinduction c CIH1.
  intros t1 t2 Ht12. step in Ht12. pstep. red.
   cbn.
  hinduction Ht12 before r; intros; cbn; eauto; 
  try (unpriv_co; fail);
  try (constructor; auto;  right; eapply CIH1; eauto with itree; fail).
  - inv H; cbn; eauto with itree.
  - unpriv_ind. unfold observe at 1. cbn. eapply H0; eauto with itree.
  - unpriv_ind. unfold observe at 3. cbn. eapply H0; eauto with itree.
  - unpriv_halt. left. eapply iter_bind_shalt_aux1; eauto with itree.
  - unpriv_halt. left. eapply iter_bind_shalt_aux2; eauto with itree.
  - unpriv_halt. specialize (H b). left. eapply iter_bind_shalt_aux1; eauto with itree.
  - unpriv_halt. specialize (H a). left. eapply iter_bind_shalt_aux2; eauto with itree.
Qed. *)


Lemma secure_eqit_iter : forall E A1 A2 B1 B2 (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
                           b1 b2 Label priv l
                           (body1 : A1 -> itree E (A1 + B1) ) (body2 : A2 -> itree E (A2 + B2) )
                           (a1 : A1) (a2 : A2),
    RA a1 a2 ->
    (forall a1 a2, RA a1 a2 -> eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l (body1 a1) (body2 a2) ) ->
    eqit_secure Label priv RB b1 b2 l (ITree.iter body1 a1) (ITree.iter body2 a2).
Proof.
  intros. rename H0 into Hbody. generalize dependent a2. revert a1.
  (* gcofix CIH. intros. setoid_rewrite unfold_iter.
  guclo eqit_bind_clo. *)

  (* look into the more general secure_eqitC closure, see if that is weakly compatible, *)
  icoinduction c CIH.
  intros a1 a2 Ha. specialize (Hbody a1 a2 Ha) as Hbodya.
  step in Hbodya. 
   (* write lemmas for unfolding the observe of iter *) cbn.
   rewrite unfold_iter.   
  hinduction Hbodya before E; intros; cbn; auto with itree.
  - inv H; cbn; eauto with itree.
  - cbn.  constructor.
    left. eapply iter_bind_aux; eauto.
  - constructor; auto.  left. eapply iter_bind_aux; eauto.
  - unpriv_co.  left. eapply iter_bind_aux; eauto.
  -  unpriv_co.  left. eapply iter_bind_aux; eauto.
  - unpriv_co.  left. eapply iter_bind_aux; eauto.
  - unpriv_ind. (* here is  where it gets bad, I am pretty sure H0 does match up but could
                  take very particular *) unfold observe at 1. cbn.
    eauto.
  - unpriv_ind. unfold observe at 3. cbn. eauto.
  -  unpriv_halt.
    left. eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt.  left. eapply iter_bind_shalt_aux2; eauto.
  - unpriv_halt.  specialize (H b). left.
    eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt.  specialize (H a). left. eapply iter_bind_shalt_aux2; eauto.
Qed.

Lemma secure_eqit_ret : forall (E : Type -> Type) Label priv l b1 b2 (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (r1 : R1) (r2 : R2),
    RR r1 r2 -> @eqit_secure E R1 R2 Label priv RR b1 b2 l (Ret r1) (Ret r2).
Proof.
  intros. step. constructor. auto.
Qed.
