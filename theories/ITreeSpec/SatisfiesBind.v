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

(* forall left case? might be way less general than *)

(* exists left case?*)

(* spec_vis left case?*)

Ltac simpobs H := apply simpobs in H.

Definition sat_equiv {E R} (phi psi : itree_spec E R) := forall tr, tr ⊧ phi <-> tr ⊧ psi.

Global Instance equiv_sat_equiv {E R} : Equivalence (@sat_equiv E R).
Proof.
  constructor; constructor; unfold sat_equiv in *; auto; try apply H.
  - rewrite H. apply H0.
  - rewrite H. apply H0.
Qed.

(* proving this equivalence is respected by bind is what I am trying to prove *)
(* is it possible this bind_true_true doesn't hold*)
(* like suppose psi branches into infinitely many paths,m1 for each*)
(* let E := Void, R :*)
Section bind_true_true_counter.

  Variant Void : Type -> Type := .

  Definition btt_counter_psi : itree_spec Void bool := or_spec (ITree.spin) (Vis (Spec_exists) (fun b: bool => Ret b)).

  Lemma btt_counter_psi_is_true : forall tr, tr ⊧ btt_counter_psi.
  Proof.
    intros.
    destruct (classic_converge _ _ tr).
    - destruct H as [b Hb]. unfold btt_counter_psi. induction Hb.
      + rewrite H. pfold. red. econstructor. exists false.
        left. pfold. constructor. exists b. left. pfold. constructor.
      + destruct e; destruct ev.
    - unfold btt_counter_psi. pfold. constructor. exists true. left. generalize dependent tr.
      pcofix CIH. intros. pfold. red. punfold H0. red in H0. inversion H0; subst.
      + cbn. constructor. pclearbot. right.  eauto.
      + destruct e; destruct ev.
  Qed.
 
(* Universe inconsistency problem
  Definition of_pred {E R} (P : itree E R -> Prop ) : itree_spec E R := 
    Vis (@Spec_exists E (itree E R) ) (fun (t : itree E R) => Vis (@Spec_exists E (P t)) (fun _ : P t => obs t) ).
*)

  Definition btt_counter_kpsi : bool -> itree_spec Void bool := fun _ => ITree.spin.

  Lemma btt_counter_is_counter : ~ (Ret true) ⊧ (btt_counter_psi >>= btt_counter_kpsi).
  Proof.
    intro Hcontra. cbn in *. unfold btt_counter_psi, btt_counter_kpsi in Hcontra.
    unfold or_spec in *. setoid_rewrite bind_vis in Hcontra.
    pinversion Hcontra; subst; inj_existT; subst. destruct H0 as [b Hb]. pclearbot.
    clear Hcontra. destruct b.
    - punfold Hb. red in Hb. rewrite H3 in Hb. dependent induction Hb; eauto.
    - punfold Hb. red in Hb. rewrite H3 in Hb. unfold observe in Hb. cbn in *. inversion Hb; subst; inj_existT; subst. 
      destruct H0 as [ [] Hspin ]; pclearbot.
      + punfold Hspin. red in Hspin. cbn in *. rewrite H5 in Hspin. dependent induction Hspin; eauto.
      + punfold Hspin. red in Hspin. cbn in *. rewrite H5 in Hspin. dependent induction Hspin; eauto.
  Qed.

  Lemma not_bind_true_true: ~ (forall (E : Type -> Type) (U R : Type) (kpsi : R -> itree_spec E U) 
                        (tr : itrace E U) (psi : itree_spec E R),
    (forall tr : itrace E R, tr ⊧ psi) -> tr ⊧ (ITree.bind psi kpsi)).
  Proof.
    intros Hcontra. specialize (btt_counter_psi_is_true) as Hbtt. 
    eapply btt_counter_is_counter. cbn. eapply Hcontra; eauto.
  Qed.
  Arguments bot {E} {R}.
  Arguments top {E} {R}.

  Lemma top_leq_btt_counter : top <= btt_counter_psi.
  Proof.
    red. intros. apply btt_counter_psi_is_true.
  Qed.

  Definition bind_monot_counter_kphi (b : bool) : itree_spec Void bool := bot. 

  Lemma counter_psi_leq_self : forall b, bind_monot_counter_kphi b <= bind_monot_counter_kphi b.
  Proof. red. auto. Qed.

  Lemma bind_btt_counter_bind_monot_counter : ~ (Ret true) ⊧ (btt_counter_psi >>= bind_monot_counter_kphi).
  Proof.
    cbn. unfold btt_counter_psi, bind_monot_counter_kphi, or_spec. setoid_rewrite bind_vis.
    intro Hcontra. pinversion Hcontra; subst; inj_existT; subst. destruct H0 as [ [ | ] Hb ]; pclearbot.
    - punfold Hb. red in Hb. cbn in *. rewrite H3 in Hb. clear H3 H1 Hcontra.
      dependent induction Hb; eauto.
    - punfold Hb. red in Hb. cbn in *. rewrite H3 in Hb. inversion Hb; subst; inj_existT; subst.
      clear Hb Hcontra. destruct H0 as [ [ | ] Hb].
      + pclearbot. punfold Hb. red in Hb. cbn in *. rewrite H5 in Hb. inversion Hb; subst; inj_existT; subst.
        destruct H0 as [ [] _ ].
      + pclearbot. punfold Hb. red in Hb. cbn in *. rewrite H5 in Hb. inversion Hb; subst; inj_existT; subst.
        destruct H0 as [ [] _ ].
  Qed.

  Lemma n_bind_monot : ~ (forall E R U (phi psi : itree_spec E R) (kphi kpsi : R -> itree_spec E U),
    phi <= psi -> (forall r,  (kphi r) <= (kpsi r) ) -> (phi >>= kphi) <= (psi >>= kpsi)).
  Proof.
    intro Hcontra. eapply bind_btt_counter_bind_monot_counter. cbn in *. unfold refines in *.
    eapply Hcontra with (phi := top) (kphi := bind_monot_counter_kphi); eauto.
    - apply top_leq_btt_counter.
    - unfold top. rewrite bind_vis. pfold. constructor. intros [].
  Qed.
  

End bind_true_true_counter.

 Lemma bind_monot_ret_bind_aux:
forall (E : Type -> Type) (U R : Type) (kpsi : R -> itree_spec E U)
    (r : itree_spec E U -> itrace E U -> Prop) (r0 : R) (psi : itree_spec E R),
  (Ret r0) ⊧ psi ->
  forall tr : itrace E U,
  tr ⊧ (kpsi r0) ->
  gpaco2 satisfies_ (EuttEv.eqitC_euttEv eq true true) bot2 r (ITree.bind psi kpsi) tr.
Proof.
  intros E U R kpsi r.
  gcofix CIH. intros a psi Hpsi tr Htr.
  punfold Hpsi. red in Hpsi. cbn in *.
  match type of Hpsi with satisfiesF _ _ ?t => remember t as ora end.
  genobs psi opsi. hinduction Hpsi before r; intros; subst; try inv Heqora.
  - simpobs Heqopsi. rewrite Heqopsi. rewrite bind_ret_l.
    gfinal. right. eapply paco2_mon; try apply Htr; intros; contradiction.
  - simpobs Heqopsi. rewrite Heqopsi. rewrite bind_tau. rewrite tau_euttge.
    eapply IHHpsi; eauto.
  - pclearbot. simpobs Heqopsi. rewrite Heqopsi. rewrite bind_vis.
    gstep. red. constructor. intros a'.
    symmetry in H1. simpobs H1. setoid_rewrite H1 in H.
    gfinal. left. eapply CIH; eauto. apply H.
  - destruct H as [a' Ha' ]. pclearbot. symmetry in H1. simpobs H1.
    setoid_rewrite H1 in Ha'. simpobs Heqopsi. rewrite Heqopsi.
    rewrite bind_vis. gstep. constructor. exists a'.
    gfinal. left. eapply CIH; eauto.
Qed.
(*
(* turns out this is false, see n_bind_monot *)
Lemma bind_monot : forall E R U (phi psi : itree_spec E R) (kphi kpsi : R -> itree_spec E U),
    phi <= psi -> (forall r,  (kphi r) <= (kpsi r) ) -> (phi >>= kphi) <= (psi >>= kpsi).
Proof.
  intros E R U phi psi kphi kpsi Hrefphi Hrefkphi.
  unfold refines in *. intros tr Htr. cbn in *.
  ginit. generalize dependent tr. generalize dependent psi.
  generalize dependent phi. gcofix CIH0. intros. 
  remember (ITree.bind phi kphi) as phi'. punfold Htr. red in Htr.
  genobs tr otr. genobs phi' ohpi'. hinduction Htr before r; intros; subst;
  try inv Heqphi'; try inv Heqotr; try inv Heqohpi'.
  - simpobs H0. simpobs H1. rewrite H0.
    (* phi is Ret a where kphi a = Ret r0, can find or write a lemma proving this*)
    admit.
  - pclearbot. (*unclear how to make progress in this case, but there are 
                 some tricks I can look intro *) admit.
  - (* H0 tells us phi0 starts with a Tau or it is a Ret a where kphi a starts with a Tau *)
    assert (forall A (e : SpecEv E A) k, VisF e k <> (observe phi0) ).
    { intros. intro Hcontra. unfold observe in H0. cbn in *. 
      destruct (observe phi0); try inv H0; try inv Hcontra. }
    destruct (observe phi0) eqn : Hphi0; try contradiction.
    + unfold observe in H0. cbn in H0. rewrite Hphi0 in H0.
      simpobs H0. symmetry in Hphi0. simpobs Hphi0.
      setoid_rewrite Hphi0 in Hrefphi.
      assert ((Ret r0) ⊧ psi).
      { apply Hrefphi. pfold. constructor. }
      (* Ret r0 ⊧ psi is the key evidence, maybe I should drop IHHtr, coinduct again
         based on that restriction
         the reason I want to coinduct is because I define forall and exists
         coinductively (which may have been a mistake :( , perhaps at some point I 
         should float a refact that makes them inductive )
       *)
      (*should be true tr ≈ Ret r0 >>= fun _ => tr *)
      clear H Hphi0 phi0.
      assert ( tr ⊧ (kphi r0) ).
      { rewrite H0. rewrite tau_eutt. pfold. auto. }
      clear H0 Htr IHHtr phi.
      apply Hrefkphi in H as Htr. clear H Hrefphi Hrefkphi.
      generalize dependent tr. generalize dependent psi. revert r0.
      clear CIH0. eapply bind_monot_ret_bind_aux; eauto.
    + eapply IHHtr with (phi0 := t); eauto.
      * intros. symmetry in Hphi0. simpobs Hphi0.
        setoid_rewrite Hphi0 in Hrefphi. setoid_rewrite tau_eutt in Hrefphi.
        eauto.
      * unfold observe in H0. cbn in H0.
        rewrite Hphi0 in H0. cbn in *. injection H0; intros; subst. auto.
   + specialize (H X e k). contradiction.
  - simpobs H0. rewrite H0. rewrite tau_euttge.
    eapply IHHtr; eauto.
 
  - simpobs H1. rewrite H1. pclearbot.
    assert (forall t, observe phi <> TauF t ).
    { unfold observe in H2. cbn in H2. 
      destruct (observe phi); try inv H2; repeat intro; discriminate. }
    destruct  (observe phi) eqn : Hphi; try contradiction.
    + symmetry in Hphi. simpobs Hphi. setoid_rewrite Hphi in Hrefphi.
      assert ((Ret r0) ⊧ psi).
      { apply Hrefphi; eauto. pfold. constructor. }
      simpobs H2. rewrite Hphi in H2. rewrite bind_ret_l in H2.
      eapply bind_monot_ret_bind_aux; eauto. 
      apply Hrefkphi. rewrite H2. pfold. constructor. left. apply H.
    + specialize (H0 t); contradiction.
    + symmetry in Hphi. simpobs Hphi.
      simpobs H2. rewrite Hphi in H2. rewrite bind_vis in H2.
      pinversion H2; inj_existT; subst; inj_existT; subst.
      setoid_rewrite Hphi in Hrefphi. clear H2 (* possibly a mistake*).
      (* this is maybe like the ret case in a sense, likely I will need to coinduct again*)
      (* like by Hrefphi I know that psi either gets to Vis (Spec_Vis e) eventually
         or it has an inf forall, exist stream *)
      clear Hphi phi H1 tr H0.
      assert (forall a, (ITree.bind (k a) kphi  ≅ (kphi0 a) ) ); auto.
      assert (forall a, (ktr a) ⊧ (kphi0 a)  ); auto.
      setoid_rewrite <- H0 in H1. clear H H0 REL. 
      generalize dependent psi. generalize dependent kpsi.
      gcofix CIH1. intros kpsi Hrefkpsi CIH psi Hrefpsi.
      (* psi ≈ Ret a \/ psi ≈ Vis e k*)
      (* not sure exactly how to prove, also likely requires a little non classical logic *)
      admit.

  - pclearbot.
    unfold observe in H2. cbn in H2. destruct (observe phi) eqn : Hphi.
    + simpobs H2. symmetry in Hphi. simpobs Hphi. setoid_rewrite Hphi in Hrefphi.
      assert ((Ret r0) ⊧ psi).
      { apply Hrefphi; pfold; constructor. }
      eapply bind_monot_ret_bind_aux; eauto. simpobs H1. setoid_rewrite H1.
      rewrite <- itree_eta. apply Hrefkphi. rewrite H2.
      pfold. red. constructor. left. auto.
    + inv H2.
    + cbn in H2. inv H2; inj_existT; subst; inj_existT.
      simpobs H1. rewrite <- itree_eta in H1. symmetry in Hphi. simpobs Hphi.
      setoid_rewrite Hphi in Hrefphi. rewrite H1. clear H1 tr0.
      (* find a way to induct on H *)
      destruct (classic (exists a : X, True) ) as [ [a _ ] | HX].
      * admit.
      * assert (forall a : X, False). 
        { intros. apply HX. eauto. }
        assert (forall tr, tr ⊧ psi).
        { intros. apply Hrefphi. pfold. constructor. intros; contradiction. }
        (* in this branch we find that psi is equivalent to true under the 
           satisfies relation
           
         *)
        enough (tr ⊧ (ITree.bind psi kpsi )).
        { gfinal. right. eapply paco2_mon; try apply H2. intros; contradiction. }
        (* turns out the bind_bind_true lemma is false, need to re-eval, may be what I am trying to prove 
           in this branch is false *)
        
         
                            


    assert (exists k X, VisF (@Spec_forall E X) k = observe phi ).
    { unfold observe in H2. cbn in H2. 
      destruct (observe phi); try inv H2; repeat intro; discriminate. }
    destruct  (observe phi) eqn : Hphi; try contradiction.

(* Spec_forall case*) admit.
  - (* Spec_exists case*) admit.
                                                              
    { unfold observe in H0. cbn in H0. destruct (observe phi0).

    eapply IHHtr; auto.
  
  punfold Htr. red in Htr. unfold observe at 1 in Htr. cbn in Htr.
  


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
*)

 (* can you rewrite obs with iter instead of a cofixpoint*)
 (* is it worth it*)
 (* do we have mon*)
