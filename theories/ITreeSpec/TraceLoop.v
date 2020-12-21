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
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac prove_arg H :=
  let H' := fresh H in
  match type of H with ?P -> _ => assert (H' : P); try (specialize (H H'); clear H') end.
(* begin delete *)
Module TraceWithPredAndEv.

Variant SpecEv (E : Type -> Type) : Type -> Type :=
  | top : SpecEv E void
  | immEv (PE : forall A, EvAns E A -> Prop) : SpecEv E unit
  (* handle in a different way | immRet *)
  (* The continuation k is the φ so Vis (exEv A) (fun a => k a) 
     exists a : A, φ(a)
     same for forall
 *)
  | exEv (A : Type) : SpecEv E A
  | forallEv (A : Type) : SpecEv E A
  (* eventually predicates*)
  | evEv (PE : forall A, EvAns E A -> Prop) : SpecEv E unit

  (* eventually ret cannot be continued*)
  | evRet {R : Type} (PR : R -> Prop) : SpecEv E void


 .
Arguments top {E}.
Arguments immEv {E}.
Arguments evEv {E}.
Arguments evRet {E} {R}.
Arguments exEv {E}.
Arguments forallEv {E}.

Definition itree_spec E A := itree (SpecEv E) (A -> Prop).
Definition itree_spec' E A := itree' (SpecEv E) (A -> Prop).

Inductive satisfiesF {E R} (F : itrace E R -> itree_spec E R -> Prop) : 
  itrace' E R -> itree_spec' E R -> Prop :=
  (* Basic ITree nodes*)
  | satisfies_ret (r : R) (PR : R -> Prop) : PR r -> satisfiesF F (RetF r) (RetF PR)
  | satisfies_tau tr phi : F tr phi -> satisfiesF F (TauF tr) (TauF phi)
  | satisfies_taur otr1 tr2 : satisfiesF F otr1 (observe tr2) -> satisfiesF F otr1 (TauF tr2)
  | satisfies_taul tr1 otr2 : satisfiesF F (observe tr1) otr2 -> satisfiesF F (TauF tr1) otr2
  (* inductive tau cases *)
  (* trivial spec events*)
  | satisfies_top tr (kphi : void -> itree_spec E R) : satisfiesF F (observe tr) (VisF top kphi)
  (* immediate spec events*)
  | satisfies_immEv (A : Type) (e : EvAns E A) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : A -> itrace E R) kphi : 
      (forall a : A, F (ktr a) (kphi tt)) -> (PE A e) -> satisfiesF F (VisF e ktr) (VisF (immEv PE) kphi) 
  (* eventual spec events*)
  | satisfies_evEv_pass  (e : EvAns E unit) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : unit -> itrace E R) kphi :
      satisfiesF F (observe (ktr tt)) (VisF (evEv PE) kphi )  -> satisfiesF F (VisF e ktr) (VisF (evEv PE) kphi )
  | satisfies_evEv (A : Type) (e : EvAns E A) (PE : forall A, EvAns E A -> Prop) 
                    (ktr : A -> itrace E R) kphi :
      (forall a : A, F (ktr a) (kphi tt) ) -> (PE A e) -> satisfiesF F (VisF e ktr) (VisF (evEv PE) kphi) 
  | satisfies_evRet_pass (e : EvAns E unit) (PR : R -> Prop) (ktr : unit -> itrace E R) (kphi : void -> itree_spec E R) :
    satisfiesF F (observe (ktr tt) ) (VisF (evRet PR) kphi ) -> satisfiesF F (VisF e ktr) (VisF (evRet PR) kphi)
  | satisfies_evRet (r : R) (PR : R -> Prop) (kphi : void -> itree_spec E R) :
      PR r -> satisfiesF F (RetF r) (VisF (evRet PR) kphi)
  (* quantifiers*)
  (* currently coinductive constructors, so forall a, forall b, forall c, ... is a trivially true spec
     this seems harmless but worth keeping an eye on
*)
  | satisfies_exEv (A : Type) (a : A) tr kphi :
    F tr (kphi a) -> satisfiesF F (observe tr) (VisF (exEv A) kphi )
  | satisfies_forallEv (A : Type) tr kphi :
      (forall a : A, F tr (kphi a) ) -> satisfiesF F (observe tr) (VisF (forallEv A) kphi)
    
.

Hint Constructors satisfiesF.
Definition satisfies_ {E R} (F : itrace E R -> itree_spec E R -> Prop) (tr : itrace E R) (phi : itree_spec E R) := 
  satisfiesF F (observe tr) (observe phi).
Hint Unfold satisfies_.

Lemma monot_satisfies {E R} : monotone2 (@satisfies_ E R).
Proof.
  red. intros. red. red in IN. induction IN; eauto.
Qed.
Hint Resolve monot_satisfies : paco.

Definition satisfies {E R} (tr : itrace E R) (phi : itree_spec E R) : Prop := paco2 satisfies_ bot2 tr phi.

Definition and_spec {E R} (phi psi : itree_spec E R) := Vis (forallEv bool) (fun b => if b : bool then phi else psi). 
Definition or_spec {E R} (phi psi : itree_spec E R) := Vis (exEv bool) (fun b => if b : bool then phi else psi). 

Definition lift_left {E A B}: (A -> itree E B) -> (A + B) -> itree E B :=
  fun f x => 
    match x with
    | inl a' => f a'
    | inr b => Ret b end.

Instance itrace_monad {E} : Monad (itrace E) := Monad_itree.

Section LoopInvar.
  Context (E : Type -> Type).
  Context (A B : Type).
  Context (corec : (A -> itree E B) -> A -> itree E B).

  Context (body : A -> itree E (A + B) ).
  Context (a : A).

  Context (inv : A -> Prop).
  (*coind functor so the target is cofix G a := Tau (F G a) *)
  Context (F : (A -> itree_spec E B) -> A -> itree_spec E B ).
  Context (R : itrace E B -> Prop).
  Context (Hresp_eutt : forall tr tr', (tr ≈ tr')%itree -> R tr -> R tr').
  (*R respects eutt*)



  Definition parametric_pres : Prop :=
    forall (ktr : A -> itrace E B), (forall a, inv a -> R (ktr a) ) -> forall a', inv a -> 
          forall (tr : itrace E (A + B)), tr ⊑ (body a') ->  R (tr >>= (lift_left ktr) ).

  Definition loop_invar_goal : Prop := forall tr, tr ⊑ iter body a -> R tr.

  Definition loop_invar := parametric_pres -> loop_invar_goal.
  (* Not confident this is enough *)





  (* Check cofix G a := Tau (F G a). *)
  

End LoopInvar.

End TraceWithPredAndEv.
(* end delete *)
Module TraceBareBones.
(* begin itree_spec_definition *)
Variant SpecEv (E : Type -> Type) : Type -> Type :=
  | Spec_Vis {A : Type} (e : EvAns E A) : SpecEv E A
  | Spec_forall { A : Type} : SpecEv E A
  | Spec_exists {A : Type} : SpecEv E A
.
Arguments Spec_forall {E} {A}.
Arguments Spec_exists {E} {A}.
Arguments Spec_Vis {E} {A}.


Definition itree_spec E R := itree (SpecEv E) R.
Definition itree_spec' E R := itree' (SpecEv E ) R.

Instance itree_spec_monad {E} : Monad (itree_spec E) := Monad_itree.

Inductive satisfiesF {E R} (F : itree_spec E R -> itrace E R -> Prop) : 
  itree_spec' E R -> itrace' E R -> Prop :=
  | satisfies_Ret (r : R) : satisfiesF F (RetF r) (RetF r)
  | satisfies_TauLR (phi : itree_spec E R) (tr : itrace E R) :
      F phi tr -> satisfiesF F (TauF phi) (TauF tr)
  | satisfies_TauL phi otr :
      satisfiesF F (observe phi) otr -> satisfiesF F (TauF phi) otr
  | satisfies_TauR ophi tr :
      satisfiesF F ophi (observe tr) -> satisfiesF F ophi (TauF tr)
  | satisfies_Spec_Vis A (e : EvAns E A) kphi ktr :
      (forall a : A, F (kphi a) (ktr a) ) -> satisfiesF F (VisF (Spec_Vis e ) kphi) (VisF e ktr)
  | satisfies_forall A kphi tr :
      (forall a : A, F (kphi a) tr) -> satisfiesF F (VisF Spec_forall kphi) (observe tr)
  | satisfies_exists A kphi tr :
      (exists a : A, F (kphi a) tr) -> satisfiesF  F (VisF Spec_exists kphi) (observe tr)
.

Hint Constructors satisfiesF.
Definition satisfies_ {E R} (F : itree_spec E R -> itrace E R -> Prop) (phi : itree_spec E R) (tr : itrace E R) := 
  satisfiesF F (observe phi) (observe tr).
Hint Unfold satisfies_.

Lemma monot_satisfies {E R} : monotone2 (@satisfies_ E R).
Proof.
  red. intros. red. red in IN. induction IN; eauto.
  destruct H as [a Ha]. eauto.
Qed.
Hint Resolve monot_satisfies : paco.

Definition satisfies {E R} (phi : itree_spec E R) (tr : itrace E R): Prop :=
  paco2 satisfies_ bot2 phi tr.

Notation "tr ⊧ phi" := (satisfies phi tr ) (at level 5).


Definition refines {E R} (phi psi : itree_spec E R) : Prop :=
  forall tr, tr ⊧ phi -> tr ⊧ psi.
(* end itree_spec_definition *)

(* begin satisfaction_facts *)
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
(* end satisfaction_facts *)


(* put in definitions file *)
Definition and_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_forall (fun b : bool => if b then phi else psi).

Definition or_spec {E R} (phi psi : itree_spec E R) :=
  Vis Spec_exists (fun b : bool => if b then phi else psi).

Definition empty_cont {A : Type} (v : void) : A :=
  match v with end.

Definition top {E R} : itree_spec E R :=
  Vis Spec_forall empty_cont.

Definition bot E R : itree_spec E R :=
  Vis Spec_exists empty_cont.

Definition forall_non_empty A {E R} (kphi : A -> itree_spec E R) : itree_spec E R :=
  and_spec (Vis Spec_forall kphi) (Vis Spec_exists (fun _ : A => top) ).

Definition show_empty {E} (A : Type) : itree_spec E (A -> void) :=
  Vis Spec_exists (fun H => Ret H).

(* end *)


(* begin itree_spec_observation *)
CoFixpoint obs_trace_ {E R} (otr : itrace' E R) : itree_spec E R :=
  match otr with
  | RetF r => Ret r
  | TauF t => Tau (obs_trace_ (observe t))
  | VisF (evans _ e a) k => 
    Vis (Spec_Vis (evans _ e a)) (fun _ => obs_trace_ (observe (k tt) ) ) 
  | VisF (evempty _ H e) k => 
    Vis (Spec_Vis (evempty _ H e) ) (empty_cont)
  end.

Definition obs_trace {E R} (tr : itrace E R) :=
  obs_trace_ (observe tr).



CoFixpoint obs_ {E R} (ot : itree' E R) : itree_spec E R :=
  match ot with 
  | RetF r => Ret r
  | TauF t => Tau ( obs_ (observe t) )
  | @VisF _ _ _ A e k => 
    (* Note that which branch you will need to take is not computable
       but the information is contained *)
    or_spec
      (Vis Spec_exists (fun a => Vis (Spec_Vis (evans _ e a)) (fun _ => (obs_ (observe (k a))  ) ) ) )
      (show_empty A >>= ( fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont))
      (* (Vis Spec_empty (fun H => Vis (Spec_Vis (evempty _ H e) ) empty_cont) ) *)


  end.

Definition obs {E R} (t : itree E R) :=
  obs_ (observe t).

Global Instance proper_obs {E R}: Proper (@eq_itree E R R eq ==> eq_itree eq) obs.
Proof.
  red. red. pcofix CIH. intros t1 t2 Heutt. pfold. red. cbn.
  punfold Heutt. red in Heutt. unfold observe. cbn. inversion Heutt; subst; cbn; auto; pclearbot;
  try (inversion CHECK).
  - constructor. right. eapply CIH; eauto.
  - constructor. intros [ | ].
    + left. pfold. red. cbn. constructor. intros. left. pfold.
      constructor. intros. right.
      eapply CIH; eauto.
    + left. pfold. red. cbn. constructor. intros. left.
      pfold. red. cbn. constructor. intros; contradiction.
Qed.

Lemma obs_tau : forall E R (t : itree E R), obs (Tau t) ≅ Tau (obs t).
Proof.
  intros. pfold. red. cbn. constructor. left.
  enough (obs t ≅ obs t); auto. reflexivity.
Qed.

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

(*
 tr ⊧ phi ->  (forall a, ktr a ⊧ kphi a ) -> 
 tr >>= ktr ⊧ phi >>= kphi TRUE

 t ⊧ phi >>= kphi -> exists t' k, t >>= k ≈ t /\ tr' ⊧ phi /\ forall a, kphi

  (forall a, invar a <= invar' a) -> iter invar a <= iter invar' a

  obs (body a) <= invar a -> iter body a <= iter invar a

*)

End TraceBareBones.
