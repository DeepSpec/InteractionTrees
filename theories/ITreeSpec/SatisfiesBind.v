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


Infix "<=" := refines (at level 70).

Lemma bind_monot : forall E R U (phi psi : itree_spec E R) (kphi kpsi : R -> itree_spec E U),
    phi <= psi -> (forall r,  (kphi r) <= (kpsi r) ) -> (phi >>= kphi) <= (psi >>= kpsi).
Proof.
  unfold refines. intros. cbn in *.


  unfold refines. intros. cbn in *. generalize dependent phi. generalize dependent psi. 
  pcofix CIH. intros psi phi Href Hmodels. pfold. red. unfold observe at 1. cbn.
  punfold Hmodels. red in Hmodels. unfold observe at 1 in Hmodels. cbn in Hmodels.
  dependent induction Hmodels.
  - destruct (observe phi) eqn : Hphi; try discriminate. 
    destruct (observe psi) eqn : Hpsi; cbn.
    +
      

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
