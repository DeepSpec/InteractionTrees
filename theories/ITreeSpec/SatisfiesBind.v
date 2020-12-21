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

Lemma bind_monot_aux : forall E R U (tr : itrace E R) (ktr : R -> itrace E U) phi kphi,
  tr ⊧ phi -> (forall r, (ktr r) ⊧ (kphi r)) -> (tr >>= ktr) ⊧ (phi >>= kphi). 
Proof.
  intros. generalize dependent tr. generalize dependent phi.
  rename H0 into Hkmodels. pcofix CIH. intros. pfold. red. cbn.
  unfold observe. cbn. punfold H0. red in H0. induction H0; pclearbot.
  - pstep_reverse. eapply paco2_mon; try apply Hkmodels. intros; contradiction.
  - cbn. constructor. right. eapply CIH; eauto.
  - constructor. unfold observe. cbn. auto.
  - constructor. unfold observe. cbn. auto.
  - cbn. constructor. right. eapply CIH. apply H.
  - cbn.
    match goal with |- satisfiesF _ _ ?otr => assert (otr = observe (ITree.bind tr0 ktr) ) end.
    { unfold observe at 2. cbn. auto. }
    rewrite H0. clear H0.
    constructor. right. apply CIH. apply H.
  - cbn. destruct H as [a Ha]. pclearbot. 
    match goal with |- satisfiesF _ _ ?otr => assert (otr = observe (ITree.bind tr0 ktr) ) end.
    { unfold observe at 2. cbn. auto. }
    rewrite H. clear H. constructor. exists a. right.

      
    apply CIH. apply Ha.
Qed.
    
Section SpecPeel.
  CoFixpoint spec_peel_ {E R S} (otr : itrace' E R) (ophi : itree_spec' E S) : itrace E S :=
    match otr, ophi with
    | TauF tr, TauF phi => Tau (spec_peel_ (observe tr) (observe phi))
    | _, RetF s => Ret s
    | otr, TauF phi => Tau (spec_peel_ otr (observe phi) )
    | TauF tr, ophi => Tau (spec_peel_ (observe tr) ophi )
    (* forall and exists cases cause problems 
       may need to, once again use strong LEM
       also probably need to use it for event case as well with peel_vis
    | otr, VisF (Spec_forall ) *)
    | _, _ => ITree.spin end.

End SpecPeel.

Lemma satisfies_Ret:
      forall (E : Type -> Type) (R : Type) (r : R), @satisfies E R (Ret r) (Ret r).
Proof.
  intros E R r. pfold. red. cbn. auto.
Qed.

Lemma satisfies_Ret_inv: forall (E : Type -> Type) (R : Type) (r : R) (tr : itrace E R),
    tr ⊧ (Ret r) -> (tr ≈ Ret r)%itree.
Proof.
  intros E R r tr Hmodels.
  punfold Hmodels. red in Hmodels. cbn in *.
  dependent induction Hmodels.
  - apply simpobs in x. rewrite x. reflexivity.
  - apply simpobs in x. rewrite x. rewrite tau_eutt.
    apply IHHmodels; auto.
Qed.

Lemma ret_refines_inv:
        forall (E : Type -> Type) (R : Type) (r1 r2 : R),
          (forall tr : itrace E R, tr ⊧ (Ret r1) -> tr ⊧ (Ret r2)) -> r1 = r2.
Proof.
  intros E R r1 r2 Href.
  specialize (Href (Ret r1)).
  prove_arg Href; try apply satisfies_Ret.
  pinversion Href; auto.
Qed.

Lemma satisfies_forall: forall (E : Type -> Type) (R A : Type) 
        (kphi : A -> itree_spec E R) (tr : itrace E R),
        tr ⊧ (Vis Spec_forall kphi) -> forall a : A, tr ⊧ (kphi a).
Proof.
  intros E R A kphi. 
  intros tr Hsat a. pfold. red.
  punfold Hsat. red in Hsat. cbn in *. dependent induction Hsat.
  - rewrite <- x. constructor. eapply IHHsat; eauto.
  - pclearbot. rewrite <- x. pstep_reverse.
Qed.

Lemma satisfies_exists: forall (E : Type -> Type) (R A : Type) 
        (kphi : A -> itree_spec E R) (tr : itrace E R),
        tr ⊧ (Vis Spec_exists kphi) -> exists a : A, tr ⊧ (kphi a).
Proof.
  intros E R A kphi.  
  intros tr Hsat. punfold Hsat. red in Hsat.
  cbn in *. dependent induction Hsat.
  - apply simpobs in x. setoid_rewrite x. setoid_rewrite tau_eutt.
    eapply IHHsat; eauto.
  - apply simpobs in x. setoid_rewrite <- itree_eta in x.
    setoid_rewrite x. destruct H as [a Ha]; pclearbot.
    exists a. auto.
Qed.

Infix "<=" := refines (at level 70).


Lemma bind_monot_ret_aux :  
  forall E R U (kpsi : R -> itree_spec E U ) r phi (psi : itree_spec E R), 
    (Ret r <= psi) -> (phi <= kpsi r) -> phi <= (psi >>= kpsi).
Proof. 
  intros E R U kpsi. pcofix CIH. intros r0 u psi Hpsi Hkpsi tr Hmodels.
  unfold refines in Hpsi, Hkpsi. cbn in *. 
  specialize (Hkpsi _ Hmodels) as Hkpsi'.
  specialize (Hpsi (Ret r0) ) as Hpsi'.
  prove_arg Hpsi'; try apply satisfies_Ret.
  pfold. red.
  unfold observe at 1. cbn. punfold Hpsi'. red in Hpsi'.
  cbn in Hpsi'. dependent induction Hpsi'.
  - rewrite <- x. pstep_reverse. eapply paco2_mon; eauto. intros; contradiction.
  - rewrite <- x. cbn. constructor. unfold observe at 1. cbn.
    eapply IHHpsi'; eauto.
    apply simpobs in x. setoid_rewrite x in Hpsi.
    setoid_rewrite tau_eutt in Hpsi. auto.
  - rewrite <- x0. cbn. constructor. intros. right.
    eapply CIH; eauto. pclearbot. red.
    apply simpobs in x0. setoid_rewrite x0 in Hpsi.
    intros tr1 Htr1. specialize (Hpsi tr1 Htr1).
    eapply satisfies_forall. auto.
  - rewrite <- x0. cbn. constructor. destruct H as [a Ha ]; pclearbot.
     apply simpobs in x0. 
    setoid_rewrite x0 in Hpsi. 
    assert (Hexists : forall tr, tr ⊧ (Ret r0) -> exists a, tr ⊧ (kphi a) ).
    { intros. apply satisfies_exists. auto. }
    exists a. right. eapply CIH; eauto. red.
    symmetry in x. apply simpobs in x.
    intros. assert (tr1 ≈ Ret r0)%itree.
    { apply satisfies_Ret_inv; auto. }
    rewrite H0. rewrite <- x. auto.
Qed.

(* forall left case?*)

(* exists left case?*)

(* spec_vis left case?*)

Lemma bind_monot : forall E R U (phi psi : itree_spec E R) (kphi kpsi : R -> itree_spec E U),
    phi <= psi -> (forall r,  (kphi r) <= (kpsi r) ) -> (phi >>= kphi) <= (psi >>= kpsi).
Proof.
  unfold refines. intros. cbn in *.


  unfold refines. intros. cbn in *. generalize dependent phi. generalize dependent psi. 
  generalize dependent tr.
  pcofix CIH. intros tr psi phi Href Hmodels. pfold. red. unfold observe at 1. cbn.
  punfold Hmodels. red in Hmodels. unfold observe at 1 in Hmodels. cbn in Hmodels.
  (* maybe if I come up with a better reasoning principle these proofs become easier?*)
  (* think carefully about how to structure proof *)
  dependent induction Hmodels; pclearbot.

  - (* destruct (observe phi) eqn : Hphi; try discriminate.
    apply simpobs in x0. apply simpobs in x. 
    symmetry in Hphi. apply simpobs in Hphi.
    setoid_rewrite Hphi in Href.
    specialize (H0 r1).
    setoid_rewrite x0 in H0.
    specialize (bind_monot_ret_ret_aux E R U kpsi r1 r0 psi) as Hbind.
    do 2 prove_arg Hbind; auto. cbn in Hbind.
    match goal with |- satisfiesF _ ?ot _ => 
    assert (ot = observe (ITree.bind psi kpsi) ) end; auto.
    rewrite H; clear H. pstep_reverse. auto.
    apply paco2_mon with (r := bot2); intros; try contradiction.
    apply Hbind. rewrite x. apply satisfies_Ret. *) admit.
  - 
    destruct (observe phi) eqn : Hphi; try discriminate.
    + (* might be able to apply that ret lemma I made *) admit.
    + (* tau tau cases a weird because it is not the right tau tau*)
      (* there is some example code which somehow restricts where taus appear *)
      cbn in *. admit.
 (* - destruct (observe phi) eqn : Hphi; destruct (observe psi) eqn : Hpsi; try discriminate.
    + pstep_reverse. eapply paco2_mon with (r := bot2); intros; try contradiction.
      apply H0. apply simpobs in x. (* show r1 = r0 using Href*) admit.
    + cbn. constructor. unfold observe at 1. cbn.
      (* phi0 ~= bind phi kphi*)
      eapply IHHmodels with (phi := kphi r0 ) ; eauto. admit. cbn.
    specialize (IHHmodels) with (phi := phi). (* apply with tau phi *) eapply IHHmodels; auto. eauto.
    + intros. eapply CIH.  apply H1. auto.
    + setoid_rewrite <- tau_eutt in Href at 1. apply Href; auto.
    + (* went wrong way? *) cbn.
    (* can I use Tau phi0 in place of phi0? *)
    admit.
  - rewrite <- x. constructor. eapply IHHmodels; eauto. 
  - admit.
  - admit.
  - admit.
*)
  Admitted.


(* find a better place for this proof *)
Lemma trace_iter_refine : forall E A B 
(trbody : A -> itree (EvAns E) (A + B)) (body : A -> itree E (A + B) ),
    (forall a, trbody a ⊑ body a) -> forall a, iter trbody a ⊑ iter body a.
Proof. 
  intros E A B. ginit.
  { intros. apply cpn2_wcompat. auto with paco. }
  gcofix CIH. intros ? ? Href a.
  specialize (Href a) as Hrefa. 
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  gstep. red. unfold observe. cbn.
 (*
  (* look into gpaco properness stuff *)
  setoid_rewrite unfold_iter.

  admit. gcofix CIH. intros ? ? Href a. specialize (Href a) as Hrefa.
  pfold. red. punfold Hrefa. red in Hrefa. unfold observe.
  cbn. dependent induction Hrefa; try rewrite <- x; try rewrite <- x0;
  pclearbot.
  - destruct r2 as [a' | b].
    + cbn. constructor. right. eapply CIH. auto.
    + cbn. constructor. auto.
  - cbn. 
    constructor. left. pfold. red. admit.
  - Locate eq_itree_iter'. eapply IHHrefa.
*) Admitted.   

 (* can you rewrite obs with iter instead of a cofixpoint*)
 (* is it worth it*)
 (* do we have mon*)
