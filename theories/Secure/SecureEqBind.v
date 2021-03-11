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

Lemma secure_eqit_bind : forall E R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
                           b1 b2 Label priv l 
    (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2),
    (forall r1 r2, RR r1 r2 -> eqit_secure Label priv RS b1 b2 l (k1 r1) (k2 r2) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. revert H0. revert t1 t2. pcofix CIH. intros t1 t2 Ht12.
  punfold Ht12. red in Ht12.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before r; intros; eauto.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. pstep_reverse. eapply paco2_mon with (r := bot2); intros; try contradiction.
    apply H; auto.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. constructor. right. eapply CIH. pclearbot.
    auto.
  - pstep. red. unfold ITree.bind at 1, observe at 1. cbn.
    rewrite <- Heqot1. cbn. constructor; auto. pstep_reverse.
  - pstep. red. unfold ITree.bind at 2, observe at 2. cbn.
    rewrite <- Heqot2. cbn. constructor; auto. pstep_reverse.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. pclearbot.
    constructor; auto. right. eapply CIH; eauto. apply H0.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H0.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H0.
  - pstep. red. unfold ITree.bind, observe. unfold observe in *. cbn.
    rewrite <- Heqot1. rewrite <- Heqot2. cbn. unpriv_co.
    right. pclearbot. eapply CIH; apply H0.
  - pstep. red. unfold ITree.bind at 1, observe at 1. cbn.
    rewrite <- Heqot1. cbn. unpriv_ind. pstep_reverse.
  - pstep. red. unfold ITree.bind at 2, observe at 2. cbn.
    rewrite <- Heqot2. cbn. unpriv_ind. pstep_reverse.
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
    left. generalize dependent t2. revert t1. pcofix CIH. intros. 
    

Locate eutt_iter'.
    (* my choices seem to be nested induction/coinduction or figure out eqit_bind_clo thing *)
    admit. (* confusing case but probably will come up a lot *)
  - constructor; auto. right. pclearbot.
  - cbn. auto. constructor; auto.
  - cbn. constructor; auto.

    
    
    

(*
(*  eqit_bind' *)
Lemma secure_eqit_bind : forall E R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
                           b1 b2 Label priv l 
    (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2),
    (forall r1 r2, RR r1 r2 -> eqit_secure Label priv RS b1 b2 l (k1 r1) (k2 r2) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 ->
    eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. revert H0. revert t1 t2. ginit.
  gcofix CIH. intros t1 t2 Ht12. punfold Ht12. red in Ht12.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before r; intros; eauto.
  - apply simpobs in Heqot1. setoid_rewrite Heqot1. apply simpobs in Heqot2.
    setoid_rewrite Heqot2. repeat rewrite bind_ret_l.
    gfinal. right. eapply paco2_mon with (r := bot2); intros; try contradiction.
    apply H. auto.
  - apply simpobs in Heqot1. setoid_rewrite Heqot1. apply simpobs in Heqot2.
    setoid_rewrite Heqot2. pclearbot. repeat rewrite bind_tau.
    gstep. constructor. gfinal. left. eapply CIH; eauto.
  - apply simpobs in Heqot1. rewrite Heqot1. rewrite bind_tau. admit.
(* gpaco2_intro and gpaco2_dist *) (*
    apply gpaco2_intro. constructor. left. pfold.
    constructor; auto. 
    assert (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) bot2 r 
                   (ITree.bind t1 k1) (ITree.bind t2 k2) ).
    { eapply IHHt12; eauto. }
    eapply gpaco2_dist in H0; auto with paco.
    destruct H0.
    + punfold H0. red in H0. unfold compose. eapply H0.

pstep_reverse.
    assert ()

    (* would be nice to have the geutt rewrite rules here *)
    admit. *)
  - apply simpobs in Heqot2. rewrite Heqot2. rewrite bind_tau.
    admit.
  - apply simpobs in Heqot1. apply simpobs in Heqot2. 
    rewrite Heqot1. rewrite Heqot2. repeat rewrite bind_vis.
    gstep. pclearbot. constructor; auto. intros.
    gfinal. left. eapply CIH; eauto. apply H0.
  - apply simpobs in Heqot1. apply simpobs in Heqot2. 
    rewrite Heqot1. rewrite Heqot2. rewrite bind_vis. rewrite bind_tau.
    pclearbot.
    gstep. unpriv_co. gfinal. left. eapply CIH; eauto. apply H0.
  - apply simpobs in Heqot1. apply simpobs in Heqot2. 
    rewrite Heqot1. rewrite Heqot2. rewrite bind_vis. rewrite bind_tau.
    pclearbot.
    gstep. unpriv_co. gfinal. left. eapply CIH; eauto. apply H0.
  - pclearbot. apply simpobs in Heqot1. apply simpobs in Heqot2. 
    rewrite Heqot1. rewrite Heqot2. repeat rewrite bind_vis.
    gstep. unpriv_co. gfinal. left. eapply CIH; eauto. apply H0.
  - apply simpobs in Heqot1. rewrite Heqot1. rewrite bind_vis.

    gstep. red. cbn. unpriv_ind. 
        assert (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) bot2 r (ITree.bind (k0 a) k1) (ITree.bind t0 k2) ).
    { eapply H1; eauto. }
    gunfold H2. 
    (* getting euttge style rewrites here won't help, because we can only remove
       private events from well behaved trees, not arbitrary ones,
       that makes it a weaker reasoning principle than Tau t >= t*)
    apply gpaco2_intro. constructor. left.
    pfold. red. red. cbn. unpriv_ind.
    unfold compose.

    apply gpaco2_dist in H2; auto with paco.
    destruct H2.
    + punfold H2. red in H2. eapply secure_eqit_mono; eauto.
      intros. pclearbot. destruct PR.
      * constructor. left. (* equivalent to H3 by eta expansion ?*) admit.
      * induction H3.
        -- constructor. right. auto.
        -- eapply rclo2_clo'; eauto.
    + remember (ITree.bind (k0 a) k1 ) as x.
      remember (ITree.bind t0 k2) as y.
      clear Heqx Heqy.
      induction H2; try contradiction. admit.
    (* gfinal. right. pfold. red. cbn. unpriv_ind.
    pstep_reverse. specialize (H1 a CIH (k0 a) t0). *)
    (*
    (* gpaco2_step*)
    gstep. unpriv_ind. 

        assert (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) bot2 r (ITree.bind (k0 a) k1) (ITree.bind t0 k2) ).
    { eapply H1; eauto. }
    (* write a fold secure_eqit_ ltac *)
    match goal with 
      | |- (secure_eqitF ?L ?p ?RR ?b1 ?b2 ?l id) (gpaco2 ?gf' ?clo ?rg ?rg ) (observe ?t1) (observe ?t2) => 
        enough (secure_eqit_ L p RR b1 b2 l id (gpaco2 gf' clo rg rg) t1 t2  ); eauto end. 
    (* how does this relate to weak compatibility? *)

    (* shows the structure that I want *)
      (*  match goal with 
      | H : gpaco2 ?gf' ?clo ?r ?rg ?t1 ?t2 |- ?gf (gpaco2 ?gf' ?clo ?rg ?rg ) (observe ?t1) (observe ?t2) => idtac gf' end. *)
    (* gpaco2_unfold is probably where to start *)
    (* wtf is rclo2 
       r \2/ (forall r')
       

     *)

    (* gpaco2 gf clo r rg <2= gf  *)
    remember (ITree.bind (k0 a) k1 ) as x.
    remember (ITree.bind t0 k2) as y.
    clear Heqx Heqy.
    apply gpaco2_unfold in H2; auto with paco.
    specialize (eqit_secureC_wcompat_id b1 b2 E S1 S2 RS Label priv l) as Hwcompat.
    inv Hwcompat. 
    induction H2; eauto.
    + destruct IN; try contradiction. 
      eapply secure_eqit_mono; eauto; intros; eauto with paco.
      red in PR. eapply gpaco2_mon; eauto. intros. inv PR0; auto; try contradiction.
      intros. inv PR0; auto. contradiction.
    + apply wcompat2_wcompat. eapply eqitC_mon; eauto. 
      intros. apply H2 in PR as H3.

(* *) *)
    econstructor; try reflexivity.
    all : intros; try subst; auto.
    (* go rid of  *)
    pstep_reverse.
    induction H2.
    + destruct IN; try contradiction. 
      admit.
    +  inv IN. inv CHECK.
       specialize (H2 _ _ REL).
       (* swap in t1' for x0 and x1 for t2'
          then apply H2 and 
          this should hold but uggh
*)
      (* gpaco2 should be monotonic *)
      (* gupaco2 should be monotonic *) admit.
    + inv IN. apply LE in REL.
 inv H2. 
    destruct IN; try contradiction.
    + red in H2. admit.
    + admit.
    fold (@secure_eqit_ E R1 R2).
    eapply gpaco2_clo in H2; eauto.
    eapply gpaco2_dist in H2; eauto with paco.
    destruct H2.
    + punfold H2. admit.
    + induction H2; try contradiction. 

    Locate gpaco2_unfold_bot.
    eapply gpaco2_unfold_bot with (clo  := eqitC RS b1 b2) (x0 := ITree.bind (k0 a) k1 ) 
    (x1 := ITree.bind t0 k2) ; eauto with paco.
    admit.
    { constructor; auto with paco.
      

    { eapply eqit_secureC_wcompat_id.

(* either want something like gstep_reverse or the 
                          equivalent of geutt rewriting for this functor
*)
     enough (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) bot2 r
         (ITree.bind (k0 a) k1) (ITree.bind t0 k2) ).
    { gunfold H2. Locate Ltac pfold_reverse.  inv H2. destruct IN; try contradiction.
      - eapply secure_eqit_mono; eauto. intros. eapply gpaco2_gupaco; eauto.
      -
      red in H2.
      eapply secure_eqit_mono; eauto. *)
(*
   admit.
  - apply simpobs in Heqot2. rewrite Heqot2. rewrite bind_vis.
    gstep. unpriv_ind. admit.
  - pclearbot. apply simpobs in Heqot1. apply simpobs in Heqot2.
    rewrite Heqot1. rewrite Heqot2. rewrite bind_vis. rewrite bind_tau.
    gstep. red. cbn. unpriv_halt. rewrite <- bind_vis. gfinal. left.
    eapply CIH; eauto.
  - pclearbot. apply simpobs in Heqot1. apply simpobs in Heqot2.
    rewrite Heqot1. rewrite Heqot2. rewrite bind_vis. rewrite bind_tau.
    gstep. red. cbn. unpriv_halt. rewrite <- bind_vis. gfinal. left.
    eapply CIH; eauto.
  - pclearbot.  apply simpobs in Heqot1. apply simpobs in Heqot2.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite bind_vis.
    gstep. red. cbn. unpriv_halt. red. rewrite <- bind_vis. gfinal. left.
    eapply CIH; eauto. apply H0.
  - pclearbot.  apply simpobs in Heqot1. apply simpobs in Heqot2.
    rewrite Heqot1. rewrite Heqot2. repeat rewrite bind_vis.
    gstep. red. cbn. unpriv_halt. red. rewrite <- bind_vis. gfinal. left.
    eapply CIH; eauto. apply H0.Admitted.
*)
    
