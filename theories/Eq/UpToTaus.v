(** * Equivalence up to taus *)

(** Abbreviated as [eutt]. *)

(** We consider [Tau] as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many [Tau]s between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** A rewrite hint database named [itree] is available via the tactic
    [autorewrite with itree] as a custom simplifier of expressions using
    mainly [Ret], [Tau], [Vis], [ITree.bind] and [ITree.Interp.Interp.interp].
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eq.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)

(** Splitting things this way makes the library easier to build in parallel.
 *)

(* begin hide *)
Require Import Paco.paco Program Setoid Morphisms RelationClasses.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Lemma simpobs {E R} {ot} {t: itree E R} (EQ: ot = observe t): t ≅ go ot.
Proof.
  pstep. repeat red. simpobs. simpl. subst. pstep_reverse. apply Reflexive_eqit.
Qed.

Lemma eqit_trans {E R} b (t1 t2 t3: itree E R)
      (REL1: eqit eq b false t1 t2)
      (REL2: eqit eq b false t2 t3):
  eqit eq b false t1 t3.
Proof.
  ginit. guclo eqit_clo_trans; eauto.
  econstructor; eauto with paco. reflexivity.
Qed.

Lemma eutt_trans {E R} (t1 t2 t3: itree E R)
      (REL1: t1 ≈ t2)
      (REL2: t2 ≈ t3):
  t1 ≈ t3.
Proof.
  revert_until R. pcofix CIH; intros.
  punfold REL1. red in REL1. punfold REL2. red in REL2. pstep. red.
  hinduction REL1 before CIH; clear t1 t2; intros; subst.
  - remember (RetF r2) as ot.
    hinduction REL2 before CIH; intros; subst; try inv Heqot; eauto.
  - remember (TauF m2) as ot.
    hinduction REL2 before CIH; intros; subst; try inv Heqot; pclearbot; eauto.
    econstructor; eauto.
    rewrite (itree_eta' ot2) in REL2. punfold_reverse REL2.
    rewrite (itree_eta' ot2). pstep_reverse.
Admitted.
      
Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition transH := @eqit_trans_clo E R1 R2 true true true true.
Definition transL := @eqit_trans_clo E R1 R2 true true false false.

Variant euttG rH rL gL gH t1 t2 : Prop :=
| euttG_intro
    (IN: gpaco2 (@eqit_ E R1 R2 RR true true (transH gH)) (euttC RR true true)
                (transH rH \2/ transL rL)
                (transH rH \2/ transL rL \2/ transL gL) t1 t2)
.
Hint Constructors euttG.
Hint Unfold transH transL.

Lemma euttG_clo_trans gH:
  transL <3= gupaco2 (@eqit_ E R1 R2 RR true true (transH gH)) (euttC RR true true).
Proof.
  intros. eapply eqit_clo_trans in PR; eauto.
  eapply gupaco2_mon_gen; cycle 1; eauto with paco.
  intros. eapply eqitF_mono; eauto. contradiction.
Qed.  

Lemma euttG_clo_bind gH:
  eqit_bind_clo true true <3= gupaco2 (@eqit_ E R1 R2 RR true true (transH gH)) (euttC RR true true).
Proof.
  intros. eapply eqit_clo_bind in PR.
  eapply gupaco2_mon_gen; cycle 1; eauto with paco.
  intros. eapply eqitF_mono; eauto. contradiction.
Qed.

Global Instance eq_euttG rH rL gL gH:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. econstructor. destruct H1.
  guclo euttG_clo_trans. econstructor; cycle -1; eauto using eqit_mon.
Qed.

Lemma rclo_euttC: rclo2 (euttC RR true true) <3= @euttC E R1 R2 RR true true.
Proof.
(*   intros. induction PR. *)
(*   - apply cpn2_base. *)

(*     destruct x1, p; econstructor; try reflexivity; eauto. *)
(*   - destruct x1, p; destruct IN. *)
(*     + apply H in RELATED. destruct RELATED. *)
(*       econstructor; cycle -1; eauto; eapply eutt_trans; eauto. *)
(*     + apply H in RELATED. destruct RELATED. *)
(*       econstructor; cycle -1; eauto; eapply eqit_trans; eauto. *)
(* Qed. *)
Admitted.

(* Lemma euttG_inv t1 t2 rH rL gL gH (P: _ -> _ -> Prop) *)
(*       (INF: forall ot1 ot2 (INF1: inftaus (go ot1)) (INF2: inftaus (go ot2)), P ot1 ot2) *)
(*       (BASE: forall t1 t2 *)
(*                (IN: (transH rH \2/ transL rL) t1 t2 : Prop), *)
(*           P (observe t1) (observe t2)) *)
(*       (RET: forall r1 r2 *)
(*                (IN: RR r1 r2 : Prop), *)
(*           P (RetF r1) (RetF r2)) *)
(*       (VIS: forall u e k1 k2 *)
(*                (IN: forall x : u, euttH (rH \2/ rL \2/ gL \2/ gH) (rH \2/ rL \2/ gL \2/ gH) (rH \2/ rL \2/ gL \2/ gH) (rH \2/ rL \2/ gL \2/ gH) (k1 x) (k2 x)), *)
(*             P (VisF e k1) (VisF e k2)) *)
(*       (TAUL: forall t1 ot2 (IN: P (observe t1) ot2), *)
(*              P (TauF t1) ot2) *)
(*       (TAUR: forall ot1 t2 (IN: P ot1 (observe t2)), *)
(*              P ot1 (TauF t2)): *)
(*   euttG rH rL gL gH t1 t2 -> P (observe t1) (observe t2). *)
(* Proof. *)
(*   revert t1 t2; intros. *)
(*   destruct (inftaus_or_fintaus t1) as [INF1 | FIN1], (inftaus_or_fintaus t2) as [INF2 | FIN2]; intros. *)
(*   { eapply INF. *)
(*     - pstep. punfold INF1. *)
(*     - pstep. punfold INF2. *)
(*   } *)
(*   { destruct FIN2. inv H0. gunfold H. apply rclo_euttC in H. *)
(*     destruct H. destruct RELATED; cycle 1. *)
(*     + eapply BASE. destruct H, H. *)
(*       * left. econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon. *)
(*       * right. econstructor; cycle -1; eauto; eapply eqit_trans; eauto. *)
(*     + repeat red in H. *)

(*       punfold EQVl. red in EQVl. punfold EQVr. red in EQVr.  *)
(*         genobs t1' ot1'. genobs t2' ot2'. *)
(*         hinduction H before TAUR; intros; subst; dependent destruction EQVr; simpobs; try inv H2; try discriminate. *)
(*         * exfalso. punfold INF1; red in INF1. remember (RetF r1) as ot. *)
(*           induction EQVl; intros; subst; try inv INF1; try inv Heqot. *)
(*           eapply IHEQVl; eauto. pclearbot. punfold BASE0. *)
(*         * exfalso. punfold INF1; red in INF1. remember (VisF e k1) as ot. *)
(*           induction EQVl; intros; subst; try inv INF1; try inv Heqot. *)
(*           eapply IHEQVl; eauto. pclearbot. punfold BASE0. *)
(*         * eapply (IHeqitF t0 (Ret r2)); simpl; eauto. *)
(*           pstep_reverse. eapply eqit_inv_tauR. pstep. eauto. *)
(*         * eapply (IHeqitF t0 (Vis e k1)); simpl; eauto. *)
(*           pstep_reverse. eapply eqit_inv_tauR. pstep. eauto. *)

    






(*     destruct FIN2. inv H0. genobs t2 ot2. genobs x ox. *)
(*     hinduction H1 before TAUR; intros; subst. *)
(*     - clear x Heqox. gunfold H. *)
(*       apply rclo_euttC in H. *)
(*       destruct H. destruct RELATED; cycle 1. *)
(*       + eapply BASE. destruct H, H. *)
(*         * left. econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon. *)
(*         * right. econstructor; cycle -1; eauto; eapply eqit_trans; eauto. *)
(*       + punfold EQVl. red in EQVl. punfold EQVr. red in EQVr. repeat red in H. *)
(*         genobs t1' ot1'. genobs t2' ot2'. *)
(*         hinduction H before TAUR; intros; subst; dependent destruction EQVr; simpobs; try inv H2; try discriminate. *)
(*         * exfalso. punfold INF1; red in INF1. remember (RetF r1) as ot. *)
(*           induction EQVl; intros; subst; try inv INF1; try inv Heqot. *)
(*           eapply IHEQVl; eauto. pclearbot. punfold BASE0. *)
(*         * exfalso. punfold INF1; red in INF1. remember (VisF e k1) as ot. *)
(*           induction EQVl; intros; subst; try inv INF1; try inv Heqot. *)
(*           eapply IHEQVl; eauto. pclearbot. punfold BASE0. *)
(*         * eapply (IHeqitF t0 (Ret r2)); simpl; eauto. *)
(*           pstep_reverse. eapply eqit_inv_tauR. pstep. eauto. *)
(*         * eapply (IHeqitF t0 (Vis e k1)); simpl; eauto. *)
(*           pstep_reverse. eapply eqit_inv_tauR. pstep. eauto. *)
(*     - gunfold H. apply rclo_euttC in H. *)
(*       destruct H. punfold EQVr. red in EQVr. simpobs. rewrite (itree_eta' (TauF t')) in EQVr. *)
(*       punfold_reverse EQVr. eapply eqit_inv_tauL in EQVr. *)
      

      
(*   } *)
(*   { admit. } *)
(*   admit. *)
(* Admitted. *)

End EUTTG.

Hint Constructors euttG.
Hint Unfold transH transL.

Section EUTTG_Properties.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).

(* Lose weak hypotheses after general rewriting *)

Lemma euttG_trans_eutt rH rL gL gH t1 t2:
  eqit_trans_clo true true true true (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  econstructor. revert_until gH. gcofix CIH; intros.
  destruct H0. destruct RELATED. gunfold IN.
  
  
  
  

  
  
  intros.
  
  revert t1 t2. gcofix CIH; intros.
  destruct H0. punfold EQVl; red in EQVl. punfold EQVr; red in EQVr.
  revert t1 t2 EQVl EQVr.
  eapply (euttG_inv RR t1' t2'), RELATED; intros.
  - admit.
  - gbase. left. destruct IN, H.
    + econstructor; cycle -1; eauto; eapply eutt_trans; eauto.
    + econstructor; cycle -1; eauto; eapply eutt_trans; eauto using eqit_mon.
  - admit.
  - 


  red in RELATED. rewrite (itree_eta t1') in RELATED.
  change (gpaco1 (euttG_ RR) euttC (rpair gH gL) r (inr (t1, t2)))
         with (rsnd (gpaco1 (euttG_ RR) euttC (rpair gH gL) r ) t1 t2).
  rewrite (itree_eta t1).
  revert t2 t2' EQVr RELATED. eapply (eutt_inv t1 t1'), EQVl; intros.
  - 
  


  gclo. econstructor.
  { rewrite itree_eta. reflexivity. }
  { rewrite itree_eta. reflexivity. }
  revert t2 t2' EQVr RELATED.

Qed.


(* Lemma euttG_trans_euttL rH rL gL gH *)
(*       (GOOD: eqit_trans_clo true true true true rH <2= rH) *)
(*       (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH): *)
(*   forall t1 t0 t2 *)
(*       (EQVl: eqit eq true true bot2 t1 t0) *)
(*       (REL: euttG rH rH rH gH t0 t2), *)
(*   euttG rH rL gL gH t1 t2. *)
(* Proof. *)
(*   gcofix CIH. intros. *)
(*   punfold EQVl. red in EQVl. genobs t1 ot1. genobs t0 ot0. *)
(*   hinduction EQVl before CIH; intros; subst. *)
(*   - gunfold REL0. remember (inl (t0, t2)) as x. *)
(*     hinduction REL0 before CIH; intros; subst. *)
(*     + destruct IN. *)
(*       * gstep.  repeat red in H. repeat red. *)
(*         hinduction H before CIH; intros; inv Heqot0; simpobs; eauto. *)
(*         econstructor; eauto. eapply (IHeqitF r2 (Ret r2)); eauto. *)
(*       * gbase. apply INV. simpl in H. *)
(*         eapply GOOD. econstructor; eauto; try reflexivity. *)
(*         rewrite (itree_eta t1), (itree_eta t0). simpobs. reflexivity. *)
(*     + destruct IN. *)
(*       * destruct H0. gclo. left. econstructor; cycle -1. *)
(*         -- eapply H; [eauto|..|eauto]. *)
(*         -- *)
(*          punfold EQVl. red in EQVl. simpobs. *)
(*         -- punfold EQVl. *)
(*         (* eapply H; [eauto|..]. *) admit. *)
(*       * admit. *)
(*   - *)
(* Qed. *)

(* Lemma foo rL rH: *)
(*   @eqit_trans_clo E R1 R2 true true true true (rsnd (rclo1 euttC (rpair rH rL))) *)
(*   <2= rsnd (rclo1 euttC (rpair rH (eqit_trans_clo true true true true rL))). *)
(* Proof. *)
(*   intros. destruct PR. repeat red in RELATED. remember (inr (t1', t2')) as x. *)
(*   hinduction RELATED before rH; intros; subst. *)
(*   - apply rclo1_base. eauto. *)
(*   - destruct IN. apply rclo1_clo. *)
(*     econstructor; [| |eapply H; [eauto|..|eauto]]. *)
(*     + reflexivity. *)
(*     + reflexivity. *)
(*     + eapply eutt_trans; eauto. *)
(*       eapply eqit_mon, EQVl0; eauto. *)
(*     + eapply eutt_trans; eauto. *)
(*       eapply eqit_mon, EQVr0; eauto. *)
(* Qed. *)



Lemma euttG_trans_eutt rH rL gL gH
      (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH)
      (GOOD: eqit_trans_clo true true true true rH <2= rH) t1 t2:
  eqit_trans_clo true true true true (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.
Proof.
  intros. destruct H. gunfold RELATED.
  hexploit foo; [econstructor; [apply EQVl|apply EQVr|..]|].
  { eapply rclo1_mon; [apply RELATED|]. intros. apply rpair_union, PR. }
  intros IN.
  econstructor. red in IN.
  cut (eqit_trans_clo true true true true (eqit_ RR true true
         (rsnd (gupaco1 (euttG_ RR) euttC (rpair rH gH \1/ rpair rH rH)))
         (rfst (gupaco1 (euttG_ RR) euttC (rpair rH gH \1/ rpair rH rH))) \2/ rH)
       <2= rfst (paco1 (euttG_ RR ∘ rclo1 euttC) (rpair gL gH \1/ rpair rL rH) \1/ rpair rL rH)).
  { admit. }

  intros. red. destruct PR. destruct RELATED0; cycle 1.
  { right. eapply INV. eauto. }
  left. red in H.
  
  

  eapply rclo1_mon. apply IN.
  intros. destruct x0, p; simpl in *.
  - 

  

  
Qed.

  


(* Make new hypotheses *)

Lemma euttG_coind: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) x,
    (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).

(* Process itrees *)

Lemma euttG_ret: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) v1 v2,
  RR v1 v2 -> euttG rH rL gL gH (Ret v1) (Ret v2).

Lemma euttG_bind: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  eqit_bind_clo true true (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.

Lemma euttG_trans_eq: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  eqit_trans_clo true true false false (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.


(* Make available weak hypotheses *)

Lemma euttG_tau: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  euttG rH gL gL gH t1 t2 -> euttG rH rL gL gH (Tau t1) (Tau t2).

(* Make available strong hypotheses *)

Lemma euttG_vis: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) u (e: E u) k1 k2,
  (forall v, euttG gH gH gH gH (k1 v) (k2 v)) -> euttG rH rL gL gH (Vis e k1) (Vis e k2).

(* Use available hypotheses *)

Lemma euttG_base: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  rL t1 t2 -> euttG rH rL gL gH t1 t2.














Lemma rclo1_euttC_mon_fst r r'
      (LE: rfst r <2= rsnd r'):
  rfst (rclo1 (@euttC E R1 R2) r) <2= rsnd (rclo1 euttC r').
Proof.
  intros. red in PR |- *. remember (inl (x0, x1)) as p.
  hinduction PR before LE; intros; subst.
  - apply rclo1_base. apply LE, IN.
  - destruct IN.
    + apply rclo1_clo. left. destruct H0. econstructor; eauto using eqit_mon.
    + apply rclo1_clo. right. destruct H0. unfold rfst, rsnd in *. econstructor; eauto.
Qed.

Lemma rclo1_euttC_mon_snd r r'
      (LE: rsnd r <2= rsnd r'):
  rsnd (rclo1 (@euttC E R1 R2) r) <2= rsnd (rclo1 euttC r').
Proof.
  intros. red in PR |- *. remember (inr (x0, x1)) as p.
  hinduction PR before LE; intros; subst.
  - apply rclo1_base. apply LE, IN.
  - destruct IN.
    + apply rclo1_clo. left. destruct H0. econstructor; eauto.
    + apply rclo1_clo. right. destruct H0. unfold rsnd in *. econstructor; eauto.
Qed.

(* Lemma foo rh: *)
(*    euttG (rpair rh rh) (rpair rh rh) <1= *)
(*    euttG (rpair (rsnd (euttG (rpair bot2 rh) (rpair bot2 rh))) rh) *)
(*          (rpair (rsnd (euttG (rpair bot2 rh) (rpair bot2 rh))) rh). *)
(* Proof. *)
(*   gcofix CIH. intros. *)
(*   destruct x1, p. *)
(*   - gunfold PR. gupaco. econstructor. *)
(*     eapply rclo1_euttC_mon_snd, IN. clear t1 t2 IN. *)
(*   intros. destruct PR; right; cycle 1. *)
(*   { gbase. apply H. } *)
(*   gclo. left. destruct H. econstructor; eauto. clear t1 t2 EQVl EQVr. *)
(*   red in RELATED. red.  *)
(* Qed. *)




Lemma foo rh t1 t2
      (IN: euttH rh rh t1 t2) :
  rsnd (euttG (rpair bot2 rh) (rpair bot2 rh)) t1 t2.
Proof.
  revert t1 t2 IN. gcofix CIH. intros.
  gunfold IN. gupaco. econstructor.
  eapply rclo1_euttC_mon_snd, IN. clear t1 t2 IN.
  intros. destruct PR; right; cycle 1.
  { gbase. apply H. }
  gclo. left. destruct H. econstructor; eauto. clear t1 t2 EQVl EQVr.
  red in RELATED. red. 
  

  


  
  revert t1' t2' RELATED. gcofix CIH.



  
  gunfold RELATED. gupaco. econstructor.
  eapply rclo1_euttC_mon_fst, RELATED. clear t1' t2' RELATED.
  intros. destruct PR; right; cycle 1.
  { gbase. destruct H; apply H. }
  simpl in H.
  
  

  




  remember (inr (t1, t2)) as p.
  
  
  induction IN; subst.
  { destruct IN; cycle 1.
    - gbase. apply H.
    - simpl in *. gclo. left. simpl.
      destruct H. econstructor; eauto.
      gunfold RELATED.

      

      

      
      


      gstep. simpl in *. unfold gupaco1 in *.


      eapply euttG__mon. apply H.
      intros. eapply gupaco1_mon. apply PR.
      intros. apply CIH.
      
      
  
Qed.













Section Test.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Variable euttG: forall (rH rL gL gH : itree E R1 -> itree E R2 -> Prop), itree E R1 -> itree E R2 -> Prop.

(**
   Correctness
 **)

Axiom eutt_le_euttG:
  eutt RR <2= euttG bot2 bot2 bot2 bot2.

Axiom euttG_le_eutt:
  euttG bot2 bot2 bot2 bot2 <2= eutt RR.

(**
   Reasoning Principles
 **)

(* Make new hypotheses *)

Axiom euttG_coind: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) x,
  (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).

(* Process itrees *)

Axiom euttG_ret: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) v1 v2,
  RR v1 v2 -> euttG rH rL gL gH (Ret v1) (Ret v2).

Axiom euttG_bind: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  eqit_bind_clo true true (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.

Axiom euttG_trans_eq: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  eqit_trans_clo true true false false (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.

(* Lose weak hypotheses after general rewriting *)

Axiom euttG_trans_eutt: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  eqit_trans_clo true true true true (euttG rH rH rH gH) t1 t2 -> euttG rH rL gL gH t1 t2.

(* Make available weak hypotheses *)

Axiom euttG_tau: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  euttG rH gL gL gH t1 t2 -> euttG rH rL gL gH (Tau t1) (Tau t2).

(* Make available strong hypotheses *)

Axiom euttG_vis: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) u (e: E u) k1 k2,
  (forall v, euttG gH gH gH gH (k1 v) (k2 v)) -> euttG rH rL gL gH (Vis e k1) (Vis e k2).

(* Use available hypotheses *)

Axiom euttG_base: forall rH rL gL gH (INV: rH <2= rL /\ rL <2= gL /\ gL <2= gH) t1 t2,
  rL t1 t2 -> euttG rH rL gL gH t1 t2.

End Test.






(**
   Correctness
 **)

Axiom eutt_le_euttL:
  eutt RR <2= euttL bot2 bot2 bot2.

Axiom euttL_le_euttH:
  euttL bot2 bot2 bot2 <2= euttH bot2 bot2.

Axiom euttH_le_eutt:
  euttH bot2 bot2 <2= eutt RR.

(**
   euttH
 **)

(* Make strong hypotheses *)

Axiom euttH_coind: forall r rh (INV: r <2= rh) x,
  (x <2= euttH r (rh \2/ x)) -> (x <2= euttH r rh).

(* Process itrees *)

Axiom euttH_ret: forall r rh (INV: r <2= rh) v1 v2,
  RR v1 v2 -> euttH r rh (Ret v1) (Ret v2).

Axiom euttH_bind: forall r rh (INV: r <2= rh) t1 t2,
  eutt_bind_clo (euttH r rh) t1 t2 -> euttH r rh t1 t2.

Axiom euttH_trans: forall r rh (INV: r <2= rh) t1 t2,
  eutt_trans_clo (euttH r rh) t1 t2 -> euttH r rh t1 t2.

(* Make hypotheses available *)

Axiom euttH_vis: forall r rh (INV: r <2= rh) u (e: E u) k1 k2,
  (forall v, euttH rh rh (k1 v) (k2 v)) -> euttH r rh (Vis e k1) (Vis e k2).

(* Use available hypotheses *)

Axiom euttH_base: forall r rh (INV: r <2= rh) t1 t2,
  r t1 t2 -> euttH r rh t1 t2.

(* Transition to lower-level *)

Axiom euttH_lower: forall r rh (INV: r <2= rh) t1 t2,
  euttL r r rh t1 t2 -> euttH r rh t1 t2.

(**
   euttL
 **)

(* Make weak hypothesis *)

Axiom euttL_coind: forall r rl rh (INV: r <2= rl /\ rl <2= rh) x,
  (x <2= euttL r (rl \2/ x) (rh \2/ x)) -> (x <2= euttL r rl rh).

(* Process itrees *)

Axiom euttL_ret: forall r rl rh (INV: r <2= rl /\ rl <2= rh) v1 v2,
  RR v1 v2 -> euttL r rl rh (Ret v1) (Ret v2).

Axiom euttL_bind: forall r rl rh (INV: r <2= rl /\ rl <2= rh) t1 t2,
  eutt_bind_clo (euttL r rl rh) t1 t2 -> euttL r rl rh t1 t2.

Axiom euttL_trans: forall r rl rh (INV: r <2= rl /\ rl <2= rh) t1 t2,
  eq_trans_clo (euttL r rl rh) t1 t2 -> euttL r rl rh t1 t2.

(* Make hypotheses available *)

Axiom euttL_tau: forall r rl rh (INV: r <2= rl /\ rl <2= rh) t1 t2,
  euttL rl rl rh t1 t2 -> euttL r rl rh (Tau t1) (Tau t2).

(* Use available hypotheses *)

Axiom euttL_base: forall r rl rh (INV: r <2= rl /\ rl <2= rh) t1 t2,
  r t1 t2 -> euttL r rl rh t1 t2.

(* Transition to higher-level *)

Axiom euttL_higher: forall r rl rh (INV: r <2= rl /\ rl <2= rh) u (e: E u) k1 k2,
  (forall v, euttH rh rh (k1 v) (k2 v)) -> euttL r rl rh (Vis e k1) (Vis e k2).




End EUTTG_Properties.





