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
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma satisfiesF_TauL:
  forall (E : Type -> Type) (A : Type) (t1 : itree (SpecEv E) A) (tr : itrace E A),
    satisfiesF (upaco2 satisfies_ bot2) (TauF t1) (observe tr) ->
    satisfiesF (upaco2 satisfies_ bot2) (observe t1) (observe tr).
Proof.
  intros E A t1 tr H.
  dependent induction H; pclearbot; auto.
  - rewrite <- x. constructor.
    punfold H.
  -  rewrite <- x. constructor. eapply IHsatisfiesF; eauto.
Qed.

Lemma satisfies_eutt_spec_l E A (P1 P2:itree_spec E A) tree :
  satisfies P1 tree -> eutt eq P1 P2 -> satisfies P2 tree.
Proof.
  revert P1 P2 tree. pcofix CIH. intros P1 P2 tree HP HP12.
  punfold HP. red in HP. pfold. red. punfold HP12. red in HP12.
  dependent induction HP.
  - rewrite <- x. rewrite <- x0 in HP12. dependent induction HP12; auto.
    + rewrite <- x. constructor.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
  - pclearbot.
    remember (observe P2) as oP2. clear HeqoP2 P2.
    assert ((exists P2', oP2 = TauF P2') \/ (forall P2', oP2 <> TauF P2') ).
    { destruct oP2; eauto; right; repeat intro; discriminate. }
    rewrite <- x. rewrite <- x0 in HP12. clear x0 x.
    destruct H0 as [ [P2' HP2'] | HP2' ].
    + subst. constructor. right. eapply CIH; eauto. 
      rewrite <- tau_eutt. setoid_rewrite <- tau_eutt at 3.
      pfold. auto.
    + inversion HP12; try (exfalso; eapply HP2'; eauto; fail); subst.
       clear HP12. punfold H. red in H. 
       dependent induction REL; intros; subst; 
       try (exfalso; eapply HP2'; eauto; fail).
       * constructor. rewrite <- x in H.
         clear CIH HP2' x. dependent induction H; try constructor.
         ++ rewrite <- x. constructor.
         ++ rewrite <- x. constructor. apply IHsatisfiesF; auto.
       * rewrite <- x in H. constructor. pclearbot. 
         dependent induction H.
         ++ rewrite <- x. constructor. eapply IHsatisfiesF; eauto.
         ++ rewrite <- x. constructor. right. eapply CIH; eauto.
            pclearbot. apply H.
        (* ++ rewrite <- x. constructor. auto. *)
         ++ rewrite <- x. constructor. right. pclearbot.
            eapply CIH; eauto. apply H.
         ++ rewrite <- x. constructor. destruct H as [a Ha]. pclearbot.
            exists a. right. eapply CIH; eauto.
       * eapply IHREL; auto. rewrite <- x in H.
         apply satisfiesF_TauL; auto.
  - eapply IHHP; eauto. rewrite <- x in HP12. 
    assert (Tau phi ≈ P2)%itree;
    try (pfold; auto; fail).
    rewrite tau_eutt in H. punfold H.
  - rewrite <- x. constructor. eapply IHHP; eauto.
  - rewrite <- x. rewrite <- x0 in HP12. dependent induction HP12.
    + rewrite <- x. constructor. pclearbot. intros.  right. eapply CIH; eauto.
      apply H.
    + rewrite <- x. constructor. eapply IHHP12; eauto. 
(*  - rewrite <- x0 in HP12. dependent induction HP12.
    + rewrite <- x. constructor.  auto.
    + rewrite <- x. constructor. eapply IHHP12; eauto. *)
  - rewrite <- x0 in HP12. rewrite <- x. clear x tree. dependent induction HP12.
    + rewrite <- x. constructor. intros.
      pclearbot. right. eapply CIH; eauto. apply H; auto.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
  - destruct H as [a H]. pclearbot. rewrite <- x0 in HP12. rewrite <- x. clear x x0 tree.
    dependent induction HP12.
    + rewrite <- x. constructor. exists a. right. eapply CIH; eauto.
      pclearbot. apply REL; auto.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
Qed.
(*might require coinduction*)
Lemma satisifes_TauR_aux: forall (E : Type -> Type) (A : Type) (m1 : itree (EvAns E) A)
                            (phi : itree_spec E A),
    (Tau m1) ⊧ phi -> m1 ⊧ phi.
Proof.
  intros E A. pcofix CIH.
  intros. punfold H0. red in H0. cbn in *.
  pfold. red. dependent induction H0; pclearbot; auto.
  - rewrite <- x. constructor; pstep_reverse. eapply paco2_mon; eauto.
    intros; contradiction.
  - rewrite <- x. constructor. eapply IHsatisfiesF; eauto.
  - pstep_reverse. assert (satisfies phi m1); try (pfold; auto; fail).
    eapply paco2_mon; eauto. intros; contradiction.
  - rewrite <- x0. constructor. intros. right. eapply CIH; eauto.
    specialize (H a). punfold H. pfold. red. cbn. rewrite <- x. auto.
  - rewrite <- x0. constructor. destruct H as [a Ha]. pclearbot.
    exists a. right. eapply CIH; eauto. pfold. red. cbn. rewrite <- x.
    pstep_reverse.
Qed.
  
Lemma satisfies_eutt_spec_r E A (P:itree_spec E A) (t1 t2 : itrace E A) :
  satisfies P t1 -> (t1 ≈ t2)%itree -> satisfies P t2.
Proof.
  revert P t1 t2. pcofix CIH. intros P t1 t2 HP Ht12.
  pfold. red. punfold Ht12. red in Ht12. punfold HP. red in HP.
  dependent induction Ht12.
  - rewrite <- x. rewrite <- x0 in HP. clear x x0.
    dependent induction HP; auto;
    try (rewrite <- x; auto).
    + rewrite <- x0. pclearbot. constructor.
      intros. right. eapply CIH; try apply H. reflexivity.
    + rewrite <- x0. constructor. destruct H as [x' Hx']. pclearbot.
      exists x'. right. eapply CIH; eauto. reflexivity.
      (* Tau Tau case *)
  - pclearbot. remember (observe P) as oP. clear HeqoP P.
    assert ( (exists P, oP = TauF P) \/ (forall P, oP <> TauF P) ).
    { destruct oP; eauto; right; repeat intro; discriminate. }
    destruct H as [ [P HoP] | HoP].
    + subst. rewrite <- x. constructor. right. eapply CIH with (t1 := t1); auto.
      * pfold. apply satisfiesF_TauL. auto.
      * apply simpobs in x0. rewrite x0. rewrite tau_eutt. auto.
    + rewrite <- x. rewrite <- x0 in HP.
      inversion HP; try (exfalso; eapply HoP; eauto; fail).
      * subst. clear HP. clear x x0. punfold REL. red in REL. constructor.
        dependent induction H1; try (exfalso; eapply HoP; eauto; fail).
        ++ rewrite <- x in REL. clear x. dependent induction REL;
           try (rewrite <- x; auto).
        ++ eapply IHsatisfiesF; auto. pstep_reverse. 
           assert (m1 ≈ m2); try (pfold; auto; fail). apply simpobs in x. rewrite x in H.
           rewrite tau_eutt in H. auto.
        ++ rewrite <- x in REL. clear x. dependent induction REL.
           ** rewrite <- x; auto. constructor. right. 
              pclearbot. eapply CIH; eauto. apply H.
           ** rewrite <- x. constructor. eapply IHREL; eauto.
        ++ pclearbot. constructor. right. eapply CIH; eauto. pfold. red.
           rewrite <- x. pstep_reverse.
        ++ constructor. destruct H as [x' Hx']. pclearbot. exists x'. right.
           eapply CIH; eauto. apply simpobs in x. rewrite <- itree_eta in x. rewrite <- x.
           pfold. auto.
      * constructor. constructor. right. pclearbot. eapply CIH; eauto.
        assert ((Tau m1) ⊧ (kphi a) ).
        { pfold. red. cbn. rewrite <- H. pstep_reverse. }
        eapply satisifes_TauR_aux; eauto.
      * constructor. constructor. destruct H1 as [x' Hx' ]. pclearbot.
        exists x'. right. eapply CIH; eauto. symmetry in H. apply simpobs in H.
        rewrite H. rewrite tau_eutt. auto.
  - rewrite <- x. rewrite <- x0 in HP. clear x x0. dependent induction HP.
    + rewrite <- x. constructor. eapply IHHP; eauto.
    + rewrite <- x. constructor. intros. right. 
      pclearbot. eapply CIH; eauto. apply H.
    + rewrite <- x0. pclearbot. 
      assert (VisF e k2 = observe (Vis e k2) ); auto. rewrite H0.
      constructor. intros. right. eapply CIH; try apply H.
      symmetry in x. apply simpobs in x. rewrite x.
      pfold. red. constructor. auto.
    + rewrite <- x0. assert (VisF e k2 = observe (Vis e k2) ); auto.
      rewrite H0. constructor. destruct H as [x' Hx']. pclearbot.
      exists x'. right. eapply CIH; eauto. symmetry in x. apply simpobs in x.
      rewrite x. pfold. constructor. left. auto.
  - eapply IHHt12; auto. rewrite <- x in HP. pstep_reverse.
    eapply satisifes_TauR_aux; eauto. pfold. auto.
  - rewrite <- x. constructor. 
    eapply IHHt12; eauto.
Qed. 

Global Instance proper_refine_eutt {E R} : Proper (eutt eq ==> eutt eq ==> iff) (@satisfies E R).
Proof.
  intros phi psi Heutt1 t1 t2 Heutt2. split; intros.
  - eapply satisfies_eutt_spec_l; eauto.
    eapply satisfies_eutt_spec_r; eauto.
  - symmetry in Heutt1. symmetry in Heutt2. 
    eapply satisfies_eutt_spec_l; eauto.
    eapply satisfies_eutt_spec_r; eauto.
Qed.
