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
     Dijkstra.DijkstraMonad
     Dijkstra.ITrace
     Dijkstra.ITraceBind
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
     Dijkstra.StateSpecT
     Dijkstra.StateIOTrace
     ITreeSpec.ITreeSpecDefinition
     ITreeSpec.SatisfiesFacts
     ITreeSpec.ITreeSpecObservation
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac prove_arg H :=
  let H' := fresh H in
  match type of H with ?P -> _ => assert (H' : P); try (specialize (H H'); clear H') end.

Lemma traces_refines_obs : forall E R (t : itree E R) tr, tr ⊑ t -> tr ⊧ (obs t).
Proof.
  intros E R. pcofix CIH. intros. pfold. red. punfold H0.
  red in H0. unfold observe at 1. cbn. dependent induction H0; subst.
  - rewrite <- x. cbn. rewrite <- x0. auto.
  - rewrite <- x. rewrite <- x0. cbn. constructor. pclearbot. right. eapply CIH; eauto.
  - rewrite <- x. constructor. eapply IHeuttEvF; auto.
  - rewrite <- x. cbn.  constructor. unfold observe at 1. cbn. eapply IHeuttEvF; eauto.
  - rewrite <- x. rewrite <- x0. cbn. clear x x0. inversion H; inj_existT; subst; inj_existT; subst.
    + rewrite itree_eta'. constructor. exists true. left. pfold. red. cbn.
      rewrite itree_eta'. constructor. exists a. left. pfold. red. cbn.
      constructor. intros [] . right.
      specialize (H0 tt a). prove_arg H0; auto. pclearbot.
      apply CIH; auto.
    + clear H0. rewrite itree_eta'. constructor. exists false.
      left. pfold. red. cbn. rewrite itree_eta'. constructor; auto.
      exists Hempty.
      left. pfold. red. cbn. rewrite itree_eta'. constructor.
      intros [].
Qed.

Lemma obs_ret_inv: forall (E : Type -> Type) (R : Type)
                     (r : R) (t : itree E R),
    RetF r = observe (obs t) -> (observe t) = RetF r.
Proof.
  intros E R r t H. unfold observe in H. cbn in H.
  destruct (observe t); try discriminate. injection H. intros; subst; auto.
Qed.
  
Lemma obs_tau_inv:
  forall (E : Type -> Type) (R : Type) (phi : itree_spec E R) (t : itree E R),
    TauF phi = observe (obs t) -> exists t0 : itree E R, observe t = TauF t0.
Proof.
  intros E R phi t x0.
  unfold observe in x0. cbn in x0. destruct (observe t); try discriminate.
  eauto.
Qed.
  
Lemma obs_spec_vis_inv_contra: forall (E : Type -> Type) (R A : Type) (e : EvAns E A) 
                            (kphi : A -> itree_spec E R)
             (t : itree E R), ~ VisF (Spec_Vis e) kphi = observe (obs t).
Proof.
  intros E R A e kphi t Hcontra.
  unfold observe in Hcontra. cbn in *. destruct (observe t); discriminate.
Qed.

Lemma obs_spec_forall_vis_inv_contra:
  forall (E : Type -> Type) (R A : Type) (kphi : A -> itree_spec E R) (t : itree E R),
    VisF Spec_forall kphi = observe (obs t) -> False.
Proof.
  intros E R A kphi t Hcontra.
  unfold observe in Hcontra. cbn in *. destruct (observe t); discriminate.
Qed.

Lemma obs_vis_ev_inv: 
  forall (E : Type -> Type) (R A : Type) (kphi : A -> itree_spec E R) (t : itree E R),
    VisF Spec_exists kphi = observe (obs t) ->
    exists (X : Type) (e : E X) (k : X -> itree E R), observe t = VisF e k.
Proof.
  intros E R A kphi t Hcontra.
  unfold observe in Hcontra. cbn in *. destruct (observe t) eqn : Ht; try discriminate.
  cbn in *. eauto.
Qed.
Lemma obs_contains_only_traces: forall E R (t : itree E R) tr, tr ⊧ (obs t) -> tr ⊑ t.
Proof.
  intros E R. pcofix CIH. intros t tr Hmodels. pfold. red.
  punfold Hmodels. red in Hmodels. dependent induction Hmodels.
  - apply obs_ret_inv in x0. rewrite x0. rewrite <- x. constructor. auto.
  - pclearbot. rewrite <- x.
    assert (phi ≈ obs t)%itree.
    { apply simpobs in x0. rewrite x0. rewrite tau_eutt. reflexivity. }
    apply obs_tau_inv in x0 as [t0 Ht].
    rewrite Ht. constructor. right. eapply CIH.
    symmetry in Ht. apply simpobs in Ht.
    rewrite Ht in H0.
    assert (t0 ≈ t). { rewrite Ht. rewrite tau_eutt. reflexivity. }
    rewrite obs_tau in H0. rewrite tau_eutt in H0.
    rewrite <- H0. auto.

  - specialize obs_tau_inv with (phi := phi) (t := t) as Ht.
    specialize (Ht x) as [t0 Ht]. rewrite Ht. constructor. eapply IHHmodels; eauto.
    unfold observe in x. cbn in x. rewrite Ht in x. cbn in x. injection x; intros; subst.
    auto.
  - rewrite <- x. constructor. eapply IHHmodels; eauto.
  - exfalso. eapply obs_spec_vis_inv_contra; eauto.
  - exfalso. eapply obs_spec_forall_vis_inv_contra; eauto.
  - destruct H as [a Ha]. pclearbot. rewrite <- x. clear x tr.
    unfold observe in x0. cbn in x0. destruct (observe t); try discriminate.
    cbn in x0.
    injection x0; intros; subst; inj_existT.
    clear x0 H1. rewrite H in Ha. clear H kphi.
    punfold Ha. red in Ha. destruct a; dependent induction Ha.
    + rewrite <- x. constructor. eapply IHHa; eauto.
    + destruct H as [a Ha]. pclearbot. rewrite <- x.
      clear tr0 x. (* another layer of induction ?*)
      punfold Ha. red in Ha. cbn in Ha.
      dependent induction Ha.
      * rewrite <- x. constructor. eapply IHHa; eauto.
      * rewrite <- x. pclearbot. specialize (H tt).
        constructor; auto. intros [] b Hans.
        inversion Hans; subst. inj_existT; subst.
        right. eapply CIH; eauto.
    + rewrite <- x. constructor. eapply IHHa; eauto.
    + destruct H as [f Hf]. pclearbot. punfold Hf.
      inj_existT. subst. red in Hf. cbn in Hf.
      (* wtf is this x1 term*) clear x1.
      rewrite <- x. clear x tr0. dependent induction Hf.
      * rewrite <- x. constructor. eapply IHHf; eauto.
      * rewrite <- x. constructor; auto.
        intros [].
Qed.      

(* reorganize some of this *)
Lemma obs_least_spec : forall E R (t : itree E R) (phi : itree_spec E R),
    (forall tr, tr ⊑ t -> tr ⊧ phi) -> refines (obs t) phi.
Proof.
  intros. red. intros. apply H. apply obs_contains_only_traces.
  auto.
Qed.

Lemma obs_bind_strong : forall E R U (t : itree E R) (k : R -> itree E U),
    obs (t >>= k) ≅ obs t >>= (fun r => obs (k r) ). 
Proof.
  intros E R U. intros t k. revert t. pcofix CIH. intros.
  pfold. red. cbn. destruct (observe t) eqn : Ht.
  - unfold observe. cbn. unfold observe. cbn. rewrite Ht. cbn.
    pstep_reverse. eapply paco2_mon with (r := bot2); intros; try contradiction.
    match goal with |- paco2 _ _ ?t1 ?t2 => enough (t1 ≅ t2); auto end.
    reflexivity.
  - unfold observe. cbn. unfold observe. cbn. rewrite Ht. cbn. constructor.
    clear Ht. right.
    match goal with |- r ?t1 _ => assert (t1 = obs (ITree.bind t0 k) ) end.
    { unfold obs. unfold observe at 2. cbn. auto. }
    rewrite H. eapply CIH.
  - unfold observe. cbn. unfold observe. cbn. rewrite Ht. cbn.
    constructor. intros [ | ].
    + left. pfold. red. cbn. constructor. left. pfold. red.
      cbn. constructor. right.
      match goal with |- r ?t1 _ => assert (t1 = obs (ITree.bind (k0 v) k) ) end.
      { unfold obs. unfold observe. cbn. auto. }
      rewrite H. eapply CIH.
    + left. pfold. red. cbn. constructor. intros. left. pfold.
      red. cbn. constructor. intros [].
Qed.

Lemma obs_monad_morph : forall E R U (t : itree E R) (k : R -> itree E U),
    (obs (t >>= k) ≈ obs t >>= (fun r => obs (k r) ))%itree. 
Proof.
  intros. rewrite obs_bind_strong. reflexivity.
Qed.
