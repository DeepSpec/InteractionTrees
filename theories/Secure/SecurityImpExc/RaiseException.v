From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
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
     Events.Exception
     Events.ExceptionFacts
     Core.Divergence
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityImpHandler
     Secure.StrongBisimProper
     Secure.SecurityImpExc.ITreeForall
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

Instance sense_preorder_in : Preorder := sense_preorder.

Definition join (s1 s2 : sensitivity) :=
  match s1 with
  | Public => s2
  | Private => Private end.

Ltac case_leq l1 l2 := destruct (classic (@leq sense_preorder l1 l2) ).

Lemma leq_sense_trans (l1 l2 l3 : sensitivity) : leq l1 l2 -> leq l2 l3 -> leq l1 l3.
Proof.
  intros. destruct l1; auto.
  destruct l2; destruct l3; auto.
Qed.

Lemma leq_sense_join_l (l1 l2 : sensitivity) : leq l1 (join l1 l2).
Proof.
  destruct l1; destruct l2; cbn; auto.
Qed.

Lemma leq_sense_join_r (l1 l2 : sensitivity) : leq l2 (join l1 l2).
Proof.
  destruct l1; destruct l2; cbn; auto.
Qed.


Definition raises_exception {R : Type} (e : impExcE void ) (t : itree (impExcE +' IOE) R) : Prop :=
  exists (t' : itree (impExcE +' IOE) unit) , can_converge tt t' /\ t ≈ (u <- t';; v <- trigger e;; match v : void with end).

Instance proper_raises_exception {R e} : Proper (eutt eq ==> iff) (@raises_exception R e).
Proof.
  repeat intro. unfold raises_exception. setoid_rewrite H. tauto.
Qed.

Lemma raises_exception_ret e R (r : R) : ~ raises_exception e (Ret r).
Proof.
  intro. red in H. destruct H as [t' [_ Ht'] ].
  cbn in Ht'. setoid_rewrite bind_trigger in Ht'. punfold Ht'. red in Ht'. cbn in *.
  remember (RetF r) as x. remember  (observe
             (ITree.bind t'
                (fun _ : unit =>
                 Vis (subevent void e)
                   (fun x : void =>
                    match x return (itree (impExcE +' IOE) R) with
                    end)))) as y.
  hinduction Ht' before r; intros; inv Heqx; inv Heqy; try discriminate.
  - unfold observe in H0. cbn in H0. destruct (observe t'); try discriminate.
  - unfold observe in H0. cbn in H0. destruct (observe t'); try discriminate. cbn in H0.
    injection H0 as H0. apply IHHt' with (t' := t); eauto. subst. auto.
Qed.

Lemma try_catch_raise_exception {R} (t1 : itree (impExcE +' IOE) R) k2 : 
  forall e t', can_converge tt t' /\ t1 ≈ (u <- t';; v <- trigger (Throw _ e);; match v : void with end) -> 
          try_catch t1 k2 ≈ u <- t';; (k2 e).
Proof.
  intros e t' [Hconv Heq]. setoid_rewrite Heq. clear Heq.
  induction Hconv.
  - rewrite H. setoid_rewrite bind_ret_l. setoid_rewrite bind_trigger.
    setoid_rewrite try_catch_exc. reflexivity.
  - rewrite H. setoid_rewrite bind_vis.
    destruct e0.
    + destruct e0; contradiction.
    + setoid_rewrite try_catch_ev. apply eqit_Vis. intros. rewrite tau_eutt.
      destruct i. destruct u. destruct b. apply IHHconv.
Qed.

Lemma raises_exception_ev:
  forall (R : Type) 
      (k : unit ->
           itree (impExcE +' IOE) R)
    (ev : IOE unit),
    (forall e : impExcE void,
        ~ raises_exception e (Vis (inr1 ev) k ) ) ->

      forall (e : impExcE void),
      ~ raises_exception e (k tt).
Proof.
   intros. intro Hcontra.
   red in Hcontra. destruct Hcontra as [t' Ht'].
   destruct Ht'. apply (H e). red. cbn in *.
   exists (Vis (inr1 ev) (fun _ => t') ).
   split.
   - eapply conv_vis. reflexivity. cbn. apply H0. Unshelve. apply tt.
   - rewrite bind_vis. apply eqit_Vis. intros []. auto.
Qed.

Lemma try_catch_not_raise_exception {R} (t1 : itree (impExcE +' IOE) R) k2 :
  (forall e, ~ raises_exception e t1) -> try_catch t1 k2 ≈ t1.
Proof.
  revert t1. unfold try_catch. ginit. gcofix CIH. intros. 
  setoid_rewrite unfold_iter. destruct (observe t1) eqn : Ht1.
  - setoid_rewrite Ht1. setoid_rewrite bind_ret_l. symmetry in Ht1. use_simpobs.
    rewrite Ht1. gfinal. right. pfold; constructor; auto.
  - setoid_rewrite Ht1. setoid_rewrite bind_ret_l. symmetry in Ht1; use_simpobs.
    rewrite Ht1. gstep. constructor. gfinal. left. eapply CIH; eauto.
    assert (t1 ≈ t). rewrite Ht1. apply tau_eutt. setoid_rewrite <- H.
    auto.
  - setoid_rewrite Ht1. destruct e.
    + destruct i. exfalso. clear CIH. symmetry in Ht1. use_simpobs.
      setoid_rewrite Ht1 in H0. eapply H0 with (e :=  (Throw _ s)  ). red. exists (Ret tt).
      split; try (constructor; reflexivity; fail).
      tau_steps. apply eqit_Vis. intros [].
    + cbn. setoid_rewrite bind_bind. setoid_rewrite bind_trigger.
      symmetry in Ht1. use_simpobs. rewrite Ht1. gstep. constructor.
      intros. red. rewrite bind_ret_l. rewrite tau_euttge. gfinal. left. apply CIH.
      intros. destruct i. destruct v. eapply raises_exception_ev. 
      setoid_rewrite Ht1 in H0. eauto.
Qed.

Lemma classic_raise_exception {R} (t : itree (impExcE +' IOE) R) :
  (forall e, ~ raises_exception e t) \/ (exists e, raises_exception e t).
Proof.
  destruct (classic (exists e, raises_exception e t) ); eauto.
Qed.

Lemma try_catch_ret {R} (t : itree (impExcE +' IOE) R) k :
  (exists r, can_converge r t) -> try_catch t k ≈ t.
Proof.
  intro Hconv. destruct Hconv as [r Hconv].
  induction Hconv.
  - rewrite H. rewrite try_catch_ret. reflexivity.
  - destruct e.
    + destruct i; contradiction.
    + destruct i.  destruct b. rewrite H.
      rewrite try_catch_ev. apply eqit_Vis. intros []. rewrite tau_eutt.
      auto.
Qed.


Definition can_raise_exception {R} (e : impExcE void ) (m : stateT map (itree (impExcE +' IOE)) R  ) : Prop :=
  exists s, raises_exception e (m s).


Definition max_exception_label {R} l (m: stateT map (itree (impExcE +' IOE)) R)  := forall l', can_raise_exception (Throw _ l') m -> leq l' l.

Lemma seq_max_exception {R1 R2} lexn1 lexn2 (m1 : stateT map (itree (impExcE +' IOE)) R1) (m2 : stateT map (itree (impExcE +' IOE)) R2) :
  max_exception_label lexn1 m1 -> max_exception_label lexn2 m2 -> max_exception_label (join lexn1 lexn2) (m1 ;; m2).
Proof.
  intros Hm1 Hm2. red. intros lmax Hexc. red in Hm1, Hm2.
  red in Hexc. destruct Hexc as [s Hs]. red in Hs.
  destruct Hs as [t' [Hconv Ht'] ]. generalize dependent m1. generalize dependent m2.
  induction Hconv; intros.
  - rewrite H in Ht'. cbn in Ht'. rewrite bind_ret_l in Ht'. rewrite bind_trigger in Ht'.
    apply eqit_inv_bind_vis in Ht'.
    destruct Ht' as [Ht' | Ht'].
    + destruct Ht' as [kxa [Hkxa _ ] ]. 
      enough (leq lmax lexn1). eapply leq_sense_trans; eauto. apply leq_sense_join_l.
      apply Hm1. red. exists s. rewrite Hkxa. red. exists (Ret tt). split.
      constructor; reflexivity. setoid_rewrite bind_ret_l. setoid_rewrite bind_trigger. apply eqit_Vis.
      intros [].
    + destruct Ht' as [ [s1 r1] [Hm1s Hm2s ] ]. cbn in Hm2s.
      enough (leq lmax lexn2). eapply leq_sense_trans; eauto. apply leq_sense_join_r.
      apply Hm2. exists s1. exists (Ret tt). split.
      constructor; reflexivity.
      setoid_rewrite Hm2s. setoid_rewrite bind_ret_l. setoid_rewrite bind_trigger.
      apply eqit_Vis. intros [].
  - destruct e.
    + destruct i; contradiction.
    + destruct i. setoid_rewrite H in Ht'. setoid_rewrite bind_vis in Ht'.
      apply eqit_inv_bind_vis in Ht' as Ht''. destruct Ht'' as [Ht'' | Ht''].
      * destruct Ht'' as [kxa [Hkxa _ ] ]. eapply IHHconv with (m1 := fun s => kxa tt); eauto.
        -- intros. apply Hm1. exists s. rewrite Hkxa.
           red. red in H0. destruct H0 as [ _ Hkxa']. red in Hkxa'.
           destruct Hkxa' as [t'' [Hconv' Ht''] ].
           exists (Vis (inr1 (LabelledPrint s0 v)) (fun _ => t'') ). split.
           { eapply conv_vis. reflexivity. eauto. Unshelve. apply tt. }
           setoid_rewrite bind_vis. apply eqit_Vis. intros []. auto.
        -- cbn. cbn in Ht'. rewrite Hkxa in Ht'. rewrite bind_vis in Ht'.  apply eqit_inv_vis in Ht'.
           destruct Ht'. destruct b. apply H1.
      * destruct Ht'' as [ [s1 r1] [Hm1s1 Hm2s2] ]. cbn in Hm2s2.
       enough (leq lmax lexn2). eapply leq_sense_trans; eauto. apply leq_sense_join_r.
       apply Hm2. exists s1. exists (trigger (LabelledPrint s0 v);; k tt ). split.
       { eapply conv_vis. unfold trigger. setoid_rewrite bind_vis. reflexivity. cbn. rewrite bind_ret_l. destruct b; auto. Unshelve. apply tt. }
       setoid_rewrite bind_trigger.
       rewrite Hm2s2. setoid_rewrite bind_vis. apply eqit_Vis. intros [].
       eapply eqit_bind'. reflexivity. intros [] [] _. apply eqit_Vis; intros [].
Qed.

Variant max_exception_label_coind_e l : forall A, (impExcE +' IOE) A -> Prop :=
  | melce_print (e : IOE unit) : max_exception_label_coind_e l unit (inr1 e)
  | melce_exc l' : leq l' l -> max_exception_label_coind_e l void (inl1 (Throw _ l'))
.

Definition max_exception_label_coind {R} l (t : itree _ R ) := itree_forall (max_exception_label_coind_e l) (fun _ => True) t.

Lemma max_exception_label_coind_imp_ind_aux R l (t : itree _ R) : 
  max_exception_label_coind l t -> forall l', raises_exception (Throw _ l') t -> leq l' l.
Proof.
  intros Hcoind l' Hraise. red in Hraise. destruct Hraise as [t' [Hconv Ht'] ].
  generalize dependent t. induction Hconv; intros.
  - rewrite H in Ht'. setoid_rewrite bind_ret_l in Ht'. setoid_rewrite bind_trigger in Ht'.
    rewrite Ht' in Hcoind.  punfold Hcoind. clear Ht' H. red in Hcoind. inv Hcoind.
    ITraceFacts.inj_existT; subst. pclearbot. inv H1; auto.
  - rewrite H in Ht'. setoid_rewrite bind_vis in Ht'. 
    rewrite Ht' in Hcoind.
    pinversion Hcoind; ITraceFacts.inj_existT; subst.
    eapply IHHconv; try apply H4. Unshelve. all: auto. reflexivity.
Qed.

Lemma max_exception_label_coind_imp_ind R lexn (m : stateT map (itree _ ) R)  :
  (forall s, max_exception_label_coind lexn (m s)) -> max_exception_label lexn m. 
Proof.
  intros Hm. red. unfold can_raise_exception.
  intros. destruct H as [s Hs]. revert Hs. apply max_exception_label_coind_imp_ind_aux; auto.
Qed.

Lemma max_exception_label_coind_flip_imp_ind R lexn (m : stateT map (itree _ ) R)  :
   max_exception_label lexn m -> (forall s, max_exception_label_coind lexn (m s)). 
Proof.
  ginit. intros. red in H0. unfold can_raise_exception in H0.
  assert (forall l', raises_exception (Throw _ l') (m s) -> leq l' lexn ).
  { intros. apply H0. exists s. auto. }
  clear H0. remember (m s) as t. clear Heqt. clear s m. generalize dependent t. gcofix CIH. intros.
  destruct (observe t) eqn : Ht; symmetry in Ht; use_simpobs.
  - rewrite Ht. gstep. constructor. auto.
  - rewrite Ht. gstep. constructor. gfinal. left. eapply CIH; eauto.
    assert (t ≈ t0). rewrite Ht. rewrite tau_eutt. reflexivity.
    setoid_rewrite <- H. auto.
  - rewrite Ht. setoid_rewrite Ht in H0.
    destruct e.
    + destruct i. gstep. constructor. 2 : intros []. constructor.
      apply H0. exists (Ret tt). split. constructor; reflexivity.
      setoid_rewrite bind_ret_l. setoid_rewrite bind_trigger.
      apply eqit_Vis. intros [].
    + destruct i. gstep. constructor. constructor.
      intros. gfinal. left. eapply CIH; eauto.
      intros. apply H0. red in H. destruct H as [t' [Hconv Ht'] ].
      exists (Vis (inr1 (LabelledPrint s v) ) (fun _ => t') ). split.
      * eapply conv_vis. reflexivity. auto. Unshelve. apply tt.
      * setoid_rewrite bind_vis. apply eqit_Vis. destruct a. intros [].
        apply Ht'.
Qed.

Lemma max_exception_mon R lexn1 lexn2 (t : itree _ R) :
  leq lexn1 lexn2 -> max_exception_label_coind lexn1 t -> max_exception_label_coind lexn2 t.
Proof.
  intros. eapply itree_forall_mon; try apply H0; auto.
  intros. inv H1.
  - constructor; auto.
  - constructor; auto. eapply leq_sense_trans; eauto.
Qed.

Lemma try_catch_public_exc R RR (t1 t2 catch1 catch2 : itree (impExcE +' IOE) R ) observer :
  max_exception_label_coind Public t1 -> max_exception_label_coind Public t2 -> 
  eqit_secure sense_preorder priv_exc_io RR true true observer t1 t2 -> 
  eqit_secure sense_preorder priv_exc_io RR true true observer catch1 catch2 ->
  eqit_secure sense_preorder priv_exc_io RR true true observer 
              (try_catch t1 (fun _ => catch1)) (try_catch t2 (fun _ => catch2)).
Proof.
  revert t1 t2. pcofix CIH. intros t1 t2 Ht1 Ht2 Hsect Hseccatch.
  punfold Hsect. red in Hsect.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Hsect before r; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite Exception.try_catch_ret.
    pfold. constructor; auto.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite try_catch_tau.
    rewrite Heqot1 in Ht1. rewrite Heqot2 in Ht2. pinversion Ht1; subst.
    pinversion Ht2; subst.
    pfold. constructor. right. eapply CIH; eauto.
  - rewrite Heqot1. rewrite try_catch_tau. pfold. constructor; auto.
    pstep_reverse. eapply IHHsect; eauto.
    rewrite Heqot1 in Ht1. pinversion  Ht1; subst; auto.
  - rewrite Heqot2. rewrite try_catch_tau. pfold. constructor; auto.
    pstep_reverse. eapply IHHsect; eauto.
    rewrite Heqot2 in Ht2. pinversion Ht2; subst; auto.
  - pclearbot. rewrite Heqot1 in Ht1. rewrite Heqot2 in Ht2.
    rewrite Heqot1. rewrite Heqot2.
    pinversion Ht1; ITraceFacts.inj_existT; subst.
    pinversion Ht2; ITraceFacts.inj_existT; subst.
    inv H3; ITraceFacts.inj_existT; subst.
    + repeat rewrite try_catch_ev. pfold.
      constructor; auto. left. pfold. constructor. right. eapply CIH; eauto.
      apply H4. apply H6. apply H.
    + repeat rewrite try_catch_exc. eapply paco2_mon; eauto. intros; contradiction.
  - rewrite Heqot1, Heqot2. rewrite try_catch_tau. pclearbot.
    rewrite Heqot1 in Ht1. rewrite Heqot2 in Ht2.
    pinversion Ht1; ITraceFacts.inj_existT; subst.
    pinversion Ht2; ITraceFacts.inj_existT; subst.
    inv H2; ITraceFacts.inj_existT; subst.
    + rewrite try_catch_ev. setoid_rewrite <- try_catch_tau at 1. pfold. red.  cbn. unpriv_co.
      right. eapply CIH; eauto.
      pfold. constructor. left. auto. pfold. constructor; auto. pstep_reverse.
    + inv SIZECHECK. contradiction.
 - rewrite Heqot1, Heqot2. rewrite try_catch_tau. pclearbot.
    rewrite Heqot1 in Ht1. rewrite Heqot2 in Ht2.
    pinversion Ht1; ITraceFacts.inj_existT; subst.
    pinversion Ht2; ITraceFacts.inj_existT; subst.
    inv H3; ITraceFacts.inj_existT; subst.
    + rewrite try_catch_ev. setoid_rewrite <- try_catch_tau at 2. pfold.
      red. cbn. unpriv_co. right. eapply CIH; eauto. pfold. constructor.
      left. auto. pfold. constructor; auto. pstep_reverse.
    + inv SIZECHECK. contradiction.
 - pclearbot. rewrite Heqot1, Heqot2. rewrite Heqot1 in Ht1. rewrite Heqot2 in Ht2.
   pinversion Ht1; ITraceFacts.inj_existT; subst.
   pinversion Ht2; ITraceFacts.inj_existT; subst.
   inv H2; ITraceFacts.inj_existT; subst; inv SIZECHECK1; try contradiction.
   inv H3; ITraceFacts.inj_existT; subst; inv SIZECHECK2; try contradiction.
   repeat rewrite try_catch_ev. pfold. red. cbn. unpriv_co.
   constructor; auto. constructor; auto. left.
   pfold. constructor. right. eapply CIH; eauto.
   apply H4. apply H6. apply H.
 - rewrite Heqot1. rewrite Heqot1 in Ht1. pinversion Ht1; ITraceFacts.inj_existT; subst.
   inv H3; ITraceFacts.inj_existT; subst; inv SIZECHECK; try contradiction.
   rewrite try_catch_ev. pfold. red. cbn. unpriv_ind. constructor; apply tt.
   constructor; auto. pstep_reverse. eapply H0; eauto. apply H5.
 - rewrite Heqot2. rewrite Heqot2 in Ht2. pinversion Ht2; ITraceFacts.inj_existT; subst.
   inv H3; ITraceFacts.inj_existT; subst; inv SIZECHECK; try contradiction.
   rewrite try_catch_ev. pfold. red. cbn. unpriv_ind. constructor; apply tt.
   constructor; auto. pstep_reverse. eapply H0; eauto. apply H5.
 - exfalso. rewrite Heqot1 in Ht1. pinversion Ht1; ITraceFacts.inj_existT; subst.
   inv H2; ITraceFacts.inj_existT; subst.
   + inv SIZECHECK. apply H0; apply tt.
   + cbn in SECCHECK. destruct l'; contradiction.
 - exfalso. rewrite Heqot2 in Ht2. pinversion Ht2; ITraceFacts.inj_existT; subst.
   inv H2; ITraceFacts.inj_existT; subst.
   + inv SIZECHECK. apply H0; apply tt.
   + cbn in SECCHECK. destruct l'; contradiction.
 - exfalso. rewrite Heqot1 in Ht1. pinversion Ht1; ITraceFacts.inj_existT; subst.
   inv H2; ITraceFacts.inj_existT; subst.
   + inv SIZECHECK. apply H0; apply tt.
   + cbn in SECCHECK1. destruct l'; contradiction.
 - exfalso. rewrite Heqot2 in Ht2. pinversion Ht2; ITraceFacts.inj_existT; subst.
   inv H2; ITraceFacts.inj_existT; subst.
   + inv SIZECHECK. apply H0; apply tt.
   + cbn in SECCHECK2. destruct l'; contradiction.
Qed.
(*throw_prefix would make the final state before throwing an exception explicit,
  and allows try_catch to be expressed as a bind this is probably the best way to hand this
  try_catch_to_throw_prefix is the main lemma, but maybe need a version that 
  deals with strong bisim and has some extra taus somewhere

*)

(*there is some kind of type mismatch
Lemma interp_state_throw_prefix R handler (σ : map) 
      (t : itree (impExcE +' stateE +' IOE ) R) :
  interp_state handle_imp (throw_prefix t) σ ≅ 
               throw_prefix (interp_state handle_imp t σ) .

Definition state_try_catch {E Err S R} (m : stateT S (itree (excE Err +' E) ) R) 
           (catch : Err -> stateT S (itree (excE Err +' E) ) R )  := 
                                   fun σ => try_catch (m σ) .
*)
