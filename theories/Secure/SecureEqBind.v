From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section gstep_reverse.

Lemma gpaco2_step_reverse T0 T1 gf clo r rg
      (MON: monotone2 gf)
      (WCMP: wcompatible2 gf clo):
  @gpaco2 T0 T1 gf clo r rg <2= gf (gpaco2 gf clo rg rg).
Proof.
  intros.
  inv WCMP. gunfold PR.
  induction PR.
  - destruct IN.
    + (* need to add constraints that should hold *) admit.
    + apply wcompat2_wcompat. (* does not seem to hold *) admit.
  - apply H. (* also don't see why this should hold *) admit.
  (* gpaco2_intro and gpaco2_dist *)
(* apply wcompat2_wcompat.

  apply wcompat2_wcompat.



eapply MON with (r := gupaco2 gf clo r); auto.
  apply wcompat2_wcompat.
  induction PR.
  - destruct IN.
    + admit.
    + eapply MON with (r := gupaco2 gf clo r).
      *  apply wcompat2_wcompat. admit.
         (* what if the clo is strictly increasing *)
         (* what if the gf is strictly increasing *)
      * intros. red in PR. auto.
  - apply wcompat2_wcompat. eapply wcompat2_mon; eauto.
    intros. apply H in PR. eapply MON; eauto. intros. inv PR0.


      unfold monotone2 in *. admit.
  -


apply gpaco2_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco2_final. apply gf_mon. right. apply H.
Qed.
 *) Abort.
End gstep_reverse.


(*

Inductive
rclo2 (T0 : Type) (T1 : T0 -> Type) (clo : rel2 T0 T1 -> rel2 T0 T1)
(r : rel2 T0 T1) : rel2 T0 T1 :=
    rclo2_base : forall (x0 : T0) (x1 : T1 x0), r x0 x1 -> rclo2 clo r x0 x1
  | rclo2_clo' : forall (r' : forall x : T0, T1 x -> Prop) (x0 : T0) (x1 : T1 x0),
                 (forall (x2 : T0) (x3 : T1 x2), (r' x2 x3 : Prop) -> rclo2 clo r x2 x3 : Prop) ->
                 clo r' x0 x1 -> rclo2 clo r x0 x1


Lemma gpaco2_unfold_bot' gf clo
      (WCMP: wcompatible2 gf clo):
  gpaco2 gf clo bot2 bot2 <2= gf (gpaco2 gf clo bot2 bot2).
Proof.
  intros. apply gpaco2_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco2_final. apply gf_mon. right. apply H.
Qed.
*)
(* try to write a proof that mirrors the gstepreverse thing you want
   see if, where, something goes wrong come to yannick with that,
   possibly he or gil or paul would understand
   do this next week
*)

(*
   Possible ways forward
   1. try to prove secure_eqit_bind "dumbly" just paco no gpaco
   2. prove weak compatibility for secure_eqitC
      2 a. define a secure_bindC closure and prove the relavant relation to secure_eqitC
   3. find a way to work with gpaco inductive steps

*)

Lemma eqit_bind_shalt_aux1:
  forall (E : Type -> Type) (S2 S1 R1 R2 : Type) (RR : R1 -> R2 -> Prop)
    (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (k1 : R1 -> itree E S1)
    (k2 : R2 -> itree E S2) (A : Type) (e : E A) (k0 : A -> itree E R1)
    (t2 : itree E R2),
    ~ leq (priv A e) l ->
    empty A ->
    paco2 (secure_eqit_ Label priv RR b1 b2 l id) bot2 (Vis e k0) t2 ->
    forall (t1 : itree E R1),
      VisF e k0 = observe t1 ->
      paco2 (secure_eqit_ Label priv RS b1 b2 l id) bot2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros E S2 S1 R1 R2 RR RS b1 b2 Label priv l k1 k2 A e k0 t2 SECCHECK SIZECHECK H0 t1 Heqot1.
  pstep. red. unfold ITree.bind at 1, observe at 1. cbn. rewrite <- Heqot1.
  cbn. rewrite itree_eta' at 1. pstep_reverse.
  generalize dependent t2. pcofix CIH. intros t2 Ht2.
  pstep. red.
  punfold Ht2. red in Ht2.
  unfold ITree.bind at 1, observe at 3. cbn in *.
  inv Ht2; ITrace.inj_existT; subst; try contra_size; try contradiction; try rewrite <- H; cbn;
  try unpriv_halt; right; eapply CIH;  pclearbot; eauto;
  try (pfold; rewrite H in H1; apply H1).
  contra_size.
Qed.

Lemma eqit_bind_shalt_aux2:
  forall (E : Type -> Type) (S2 S1 R1 R2 : Type) (RR : R1 -> R2 -> Prop)
    (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (k1 : R1 -> itree E S1)
    (k2 : R2 -> itree E S2) (A : Type) (e : E A) (k0 : A -> itree E R2)
    (t1 : itree E R1) (t2 : itree E R2),
    ~ leq (priv A e) l ->
    empty A ->
    paco2 (secure_eqit_ Label priv RR b1 b2 l id) bot2 t1 (Vis e k0) ->
    VisF e k0 = observe t2 ->
    paco2 (secure_eqit_ Label priv RS b1 b2 l id) bot2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros E S2 S1 R1 R2 RR RS b1 b2 Label priv l k1 k2 A e k0 t1 t2 SECCHECK SIZECHECK H0 Heqot1.
  pstep. red. unfold ITree.bind at 2, observe at 2. cbn. rewrite <- Heqot1.
  cbn. rewrite itree_eta'. pstep_reverse.
  generalize dependent t1. pcofix CIH. intros t1 Ht1.
  pstep. red.
  punfold Ht1. red in Ht1.
  unfold ITree.bind at 1, observe at 1. cbn in *.
  inv Ht1; ITrace.inj_existT; subst; try contra_size; try contradiction; cbn;
  try unpriv_halt; try contra_size; try (right; eapply CIH; pclearbot; eauto).
  pfold. rewrite H0 in H1. auto. apply H1.
Qed.

Lemma secure_eqit_bind' : forall E R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)
                           b1 b2 Label priv l r
    (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2),
    (forall r1 r2, RR r1 r2 -> paco2 (secure_eqit_ Label priv RS b1 b2 l id) r (k1 r1) (k2 r2) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    paco2 (secure_eqit_ Label priv RS b1 b2 l id) r (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. revert H0. revert t1 t2. pcofix CIH. intros t1 t2 Ht12.
  punfold Ht12. red in Ht12.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before r; intros; eauto.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. pstep_reverse.
    eapply paco2_mon; eauto.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. constructor. right. eapply CIH. pclearbot.
    auto.
  - pstep. red. unfold ITree.bind at 1, observe at 1. cbn.
    rewrite <- Heqot1. cbn. constructor; auto. pstep_reverse.
  - pstep. red. unfold ITree.bind at 2, observe at 2. cbn.
    rewrite <- Heqot2. cbn. constructor; auto. pstep_reverse.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. pclearbot.
    constructor; auto. right. eapply CIH; eauto. apply H.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H.
  - pstep. red. unfold ITree.bind at 1, observe at 1. cbn.
    rewrite <- Heqot1. cbn. unpriv_ind. pstep_reverse. eapply H0; eauto.
  - pstep. red. unfold ITree.bind at 2, observe at 2. cbn.
    rewrite <- Heqot2. cbn. unpriv_ind. pstep_reverse. eapply H0; eauto.
  - pclearbot.
    eapply paco2_mon with (r := bot2); intros; try contradiction.
    eapply eqit_bind_shalt_aux1; eauto. pfold. red. rewrite <- Heqot2.
    cbn. unpriv_halt. left. eauto.
  - pclearbot.
    eapply paco2_mon with (r := bot2); intros; try contradiction.
    eapply eqit_bind_shalt_aux2; eauto. pfold. red. cbn. rewrite <- Heqot1.
    unpriv_halt. left. eauto.
  - pclearbot.
    eapply paco2_mon with (r := bot2); intros; try contradiction.
    eapply eqit_bind_shalt_aux1 with (A := A); eauto.
    pfold. red. rewrite <- Heqot2. cbn. unpriv_halt.
  - pclearbot.
    eapply paco2_mon with (r := bot2); intros; try contradiction.
    eapply eqit_bind_shalt_aux2; eauto. pfold. red. cbn. rewrite <- Heqot1.
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
    paco2 (secure_eqit_ Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l id) bot2
          (Vis e k1) t0 ->
    paco2 (secure_eqit_ Label priv RB b1 b2 l id) r
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
  generalize dependent t0. pcofix CIH. intros t0 Ht0.
  pstep. red. cbn. unfold observe. cbn. punfold Ht0.
  red in Ht0. cbn in *. inv Ht0; inv_vis_secure; cbn; pclearbot; unpriv_halt; try contra_size.
  right. eapply CIH; eauto.
  rewrite H in H1. pfold. red. auto.
Qed.

Lemma iter_bind_shalt_aux2:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) (r : itree E B1 -> itree E B2 -> Prop)
    (A : Type) (e : E A) (t0 : itree E (A1 + B1)) (k2 : A -> itree E (A2 + B2)),
    ~ leq (priv A e) l ->
    empty A ->
    paco2 (secure_eqit_ Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l id) bot2 t0
          (Vis e k2) ->
    paco2 (secure_eqit_ Label priv RB b1 b2 l id) r
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
  intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 r A e t0 k2 SECCHECK SIZECHECK H.
  generalize dependent t0. pcofix CIH. intros t0 Ht0.
  pstep. red. cbn. unfold observe. cbn. punfold Ht0.
  red in Ht0. cbn in *. inv Ht0; inv_vis_secure; cbn; pclearbot; unpriv_halt; try contra_size.
  right. eapply CIH; eauto.
  rewrite H0 in H1. pfold. red. auto.
Qed.

Lemma iter_bind_aux:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) (r : itree E B1 -> itree E B2 -> Prop)
    (t1 : itree E (A1 + B1)) (t2 : itree E (A2 + B2)),
    paco2 (secure_eqit_ Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l id) bot2 t1 t2 ->
    (forall (a1 : A1) (a2 : A2), RA a1 a2 -> r (ITree.iter body1 a1) (ITree.iter body2 a2)) ->
    paco2 (secure_eqit_ Label priv RB b1 b2 l id) r
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
  intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 r t1 t2 H CIH0.
  generalize dependent t2. revert t1. pcofix CIH1.
  intros t1 t2 Ht12. punfold Ht12. pstep. red.
  unfold observe. cbn.
  hinduction Ht12 before r; intros; cbn; eauto; pclearbot;
  try (unpriv_co; fail);
  try (constructor; auto; pclearbot; right; eapply CIH1; eauto; fail).
  - inv H; cbn; eauto.
  - unpriv_ind. unfold observe at 1. cbn. eapply H0; eauto.
  - unpriv_ind. unfold observe at 3. cbn. eapply H0; eauto.
  - unpriv_halt. left. eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt. left. eapply iter_bind_shalt_aux2; eauto.
  - unpriv_halt. specialize (H b). left. eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt. specialize (H a). left. eapply iter_bind_shalt_aux2; eauto.
Qed.


(*

    t1 ≈ t2 -> interp h t1 ≈ interp h t2

    t ≈ t -> interp h t ≈ interp h t

interp h := iter (interp_step h)
   A := itree E R
   B := R

  RA := eqit_secure RR
  RB := RR
  body := interp_step


  way to assign relations to individual events that

  RX x1 x2 -> eqit_secure l RR (k x1) (k x2)

  RX e1 e2 := if l <= priv e then ⊥ else

*)


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
  pcofix CIH.
  intros a1 a2 Ha. specialize (Hbody a1 a2 Ha) as Hbodya.
  punfold Hbodya. red in Hbodya. pfold. red.
  unfold observe. (* write lemmas for unfolding the observe of iter *) cbn.
  hinduction Hbodya before r; intros; cbn; auto.
  - inv H; cbn; eauto.
  - cbn. pclearbot. constructor.
    left. eapply iter_bind_aux; eauto.
  - constructor; auto. pclearbot. left. eapply iter_bind_aux; eauto.
  - unpriv_co. pclearbot. left. eapply iter_bind_aux; eauto.
  -  unpriv_co. pclearbot. left. eapply iter_bind_aux; eauto.
  - unpriv_co. pclearbot. left. eapply iter_bind_aux; eauto.
  - unpriv_ind. (* here is  where it gets bad, I am pretty sure H0 does match up but could
                  take very particular *) unfold observe at 1. cbn.
    eauto.
  - unpriv_ind. unfold observe at 3. cbn. eauto.
  - pclearbot. unpriv_halt.
    left. eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt. pclearbot. left. eapply iter_bind_shalt_aux2; eauto.
  - unpriv_halt. pclearbot. specialize (H b). left.
    eapply iter_bind_shalt_aux1; eauto.
  - unpriv_halt. pclearbot. specialize (H a). left. eapply iter_bind_shalt_aux2; eauto.
Qed.
