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
Require Import Paco.paco.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT_REL.

Context {T1 T2 : Type}.

Definition eutt_rel := (T1 * T2) + (T1 * T2) -> Prop.

Definition rpair (r1 r2: T1 -> T2 -> Prop) : eutt_rel := fun x =>
  match x with
  | inl (t1,t2) => r1 t1 t2
  | inr (t1,t2) => r2 t1 t2
  end.

Definition rfst (r: eutt_rel) t1 t2 := r (inl (t1,t2)).

Definition rsnd (r: eutt_rel) t1 t2 := r (inr (t1,t2)).

Lemma rpair_mon r s r' s' p
      (IN: rpair r s p)
      (LEr: r <2= r')
      (LEs: s <2= s'):
  rpair r' s' p.
Proof.
  destruct p, p; simpl in *; eauto.
Qed.

Lemma rfst_mon r r' t1 t2
      (IN: rfst r t1 t2)
      (LE: r <1= r'):
  rfst r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rsnd_mon r r' t1 t2
      (IN: rsnd r t1 t2)
      (LE: r <1= r'):
  rsnd r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rpair_bot: rpair bot2 bot2 <1= bot1.
Proof.
  intros. destruct x0, p; contradiction.
Qed.

End EUTT_REL.

Hint Unfold rpair rfst rsnd.
Hint Resolve rpair_mon rfst_mon rsnd_mon : paco.
     
Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition euttG_ (rp: eutt_rel) : eutt_rel :=
  rpair (@eqit_ E _ _ RR true true (rsnd rp) (rfst rp))
        (eqit_trans_clo true true true true (rfst rp)).

Definition euttC_trans rp :=
  rpair (@eqit_trans_clo E R1 R2 true true false false (rfst rp))
        (eqit_trans_clo true true true true (rsnd rp)).

Definition euttC_bind rp :=
  rpair (@eqit_bind_clo E R1 R2 true true (rfst rp))
        (eqit_bind_clo true true (rsnd rp)).
  
Definition euttC := euttC_trans \2/ euttC_bind.

Definition euttG lp hp := gpaco1 euttG_ euttC lp hp.

Definition euttL r rl rh := rfst (euttG (rpair r r) (rpair rl rh)).

Definition euttH r rh := rsnd (euttG (rpair r r) (rpair r rh)).

Lemma euttG__mon: monotone1 euttG_.
Proof.
  red; intros. destruct x0, p; simpl in *.
  - eapply eqitF_mono; eauto.
  - destruct IN; eauto.
Qed.

Hint Resolve euttG__mon : paco.

Lemma euttC_trans_wcompat: wcompatible1 euttG_ euttC_trans.
Proof.
  econstructor.
  { red; intros. destruct x0, p; simpl in *; destruct IN; eauto. }
  intros.
  admit.
Admitted.

Lemma euttC_bind_wcompat: wcompatible1 euttG_ euttC_bind.
Proof.
  econstructor.
  { red; intros. destruct x0, p; simpl in *; destruct IN; eauto with paco. }
  intros.
  admit.
Admitted.

Lemma euttC_wcompat: wcompatible1 euttG_ euttC.
Proof.
  apply wcompat1_union; eauto with paco.
  - apply euttC_trans_wcompat.
  - apply euttC_bind_wcompat.
Qed.

End EUTTG.

Hint Resolve euttG__mon : paco.
Hint Resolve euttC_wcompat : paco.

Section EUTTG_Properties.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Local Notation euttG := (@euttG E R1 R2 RR).
Local Notation euttH := (@euttH E R1 R2 RR).
Local Notation euttL := (@euttH E R1 R2 RR).

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

Lemma foo rh t1 t2
      (IN: euttH rh rh t1 t2) :
  rsnd (euttG (rpair (@bot2 _ (fun _ => _)) rh) (rpair (@bot2 _ (fun _ => _)) rh)) t1 t2.
Proof.
  revert t1 t2 IN. gcofix CIH. intros.
  gunfold IN. gupaco. econstructor.
  eapply rclo1_euttC_mon_snd, IN. clear t1 t2 IN.
  intros. destruct PR; right; cycle 1.
  { gbase. apply H. }
  gclo. left. destruct H. econstructor; eauto. clear t1 t2 EQVl EQVr.

  red in RELATED.


  
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



