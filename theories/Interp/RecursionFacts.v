(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)

(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)

From Stdlib Require Import
     Program.Tactics
     Setoid
     Morphisms.

From Coinduction Require Import all. 

From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

Import ITreeNotations.

Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mrec]. *)

Definition _interp_mrec {R : Type} (ot : itreeF (D +' E) R _) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec ctx t)
  | VisF e k =>
    match e with
    | inl1 d => Tau (interp_mrec ctx (ctx _ d >>= k))
    | inr1 e => Vis e (fun x => Tau (interp_mrec ctx (k x)))
    end
  end.

(* Implementation note: in [_interp_mrec], the [Tau] in the [inr1] branch
   might look superfluous. It gets inserted by [iter] (which behaves uniformly
   in both the [inl1] and [inr1] branches). This [Tau] could be avoided, but
   it makes the implementation and proofs more complicated for too little gain.
*)

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  interp_mrec ctx t ≅ _interp_mrec (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l; reflexivity.
  - destruct e; cbn.
    + rewrite bind_ret_l; reflexivity.
    + rewrite bind_vis.
      step; constructor. intros.
      rewrite bind_ret_l.
      apply reflexivity.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E := fun _ m =>
  match m with
  | inl1 m => mrec f m
  | inr1 m => ITree.trigger m
  end.

Global Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_mrec _ _ ctx R).
Proof.
  repeat red. 
  coinduction. intros.
  rewrite !unfold_interp_mrec.
  step in H. inv H; eauto with itree. 
  - taus. now apply CIH. 
  - cbn. destruct e.
    + taus. apply CIH.
      ebind. intros; subst.  
    do 2 step. apply REL. 
    + constructor. intro. step. taus. apply CIH.
    apply REL.   
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k; coinduction; intros.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e]; cbn. 
  - apply reflexivity.
  - taus. fold_subst. apply CIH. 
  - to_mon. taus. fold_subst. 
    rewrite <- bind_bind.
    apply CIH.  
  - constructor. intro. fold_subst. 
    rewrite bind_ret_l, bind_tau. 
    step. taus. apply CIH.   
Qed.

Theorem interp_mrec_trigger {U} (a : (D +' E) U) :
    interp_mrec ctx (ITree.trigger a)
  ≳ mrecursive ctx _ a.
Proof.
  rewrite unfold_interp_mrec; unfold mrecursive.
  destruct a; cbn.
  rewrite tau_euttge, bind_ret_r.
  reflexivity.
  step; constructor. intros. rewrite tau_euttge, unfold_interp_mrec; cbn.
  apply reflexivity.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx c ≈ interp (mrecursive ctx) c.
Proof.
  rewrite <- (tau_eutt (interp _ _)).
  revert_until T. coinduction. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c0); [| |destruct e]; simpl; eauto.
  - now taur. 
  - taus. apply CIH. 
  - taus. rewrite interp_mrec_bind. unfold mrec.
  ebind. intros; subst. apply CIH. 
  - to_mon. rewrite tau_euttge. 
    unfold ITree.trigger.  rewrite bind_vis.
    constructor. intro. 
    rewrite bind_ret_l. rewrite tau_euttge. apply CIH. 
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx d ≈ interp (mrecursive ctx) (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

Lemma interp_mrecursive {T} (d : D T) :
  interp (mrecursive ctx) (trigger_inl1 d) ≈ mrec ctx d.
Proof.
  unfold mrecursive. unfold trigger_inl1.
  rewrite interp_trigger. cbn. reflexivity.
Qed.

Theorem unfold_interp_mrec_h {T} (t : itree _ T)
  : interp_mrec ctx (interp (case_ (C := Handler) ctx inr_) t)
  ≈ interp_mrec ctx t.
Proof.
  rewrite <- tau_eutt.
  revert t. coinduction. intros.
  rewrite (itree_eta t); destruct (observe t).
  - rewrite 2 unfold_interp_mrec; now taul. 
  - rewrite unfold_interp, 2 unfold_interp_mrec. 
    taus. apply CIH. 
  - rewrite interp_vis.
    rewrite (unfold_interp_mrec _ (Vis _ _)).
    destruct e; cbn; to_mon. 
    + rewrite 2 interp_mrec_bind.
      taus. 
      ebind; intros; subst. 
      rewrite unfold_interp_mrec; cbn; apply CIH. 
    + unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
      rewrite bind_trigger, unfold_interp_mrec; cbn; to_mon.
      rewrite tau_euttge.
      constructor.
      intros. step. taus. 
      rewrite unfold_interp_mrec; cbn.
      apply CIH. 
Qed.

End Facts.

Local Opaque interp_mrec.

Global Instance Proper_interp_mrec {D E} :
  @Proper ((D ~> itree (D +' E)) -> (itree (D +' E) ~> itree E))
          (Relation.i_pointwise (fun _ => eutt eq) ==>
           Relation.i_respectful (fun _ => eutt eq) (fun _ => eutt eq))
          interp_mrec.
Proof.
  intros f g Hfg R.
  coinduction; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  step in Ht; induction Ht; cbn. 
  3: { destruct e; constructor. 
    + apply CIH. ebind. apply Hfg.  
      intros ? _ []. apply REL. 
    + intros; step; taus. eauto with itree.
  }
  1,2: constructor; auto with itree.
  all: to_mon; rewrite unfold_interp_mrec, tau_euttge; auto.
Qed.

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (rec f)) ITree.trigger.

Lemma rec_as_interp {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≈ interp (recursive f) (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  apply eq_sub_eutt.
  eapply eq_itree_interp.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_recursive_call {E A B} (f : A -> itree (callE A B +' E) B) (x:A) :
   interp (recursive f) (call x) ≈ rec f x.
Proof.
  unfold recursive. unfold call.
  rewrite interp_trigger. cbn.
  reflexivity.
Qed.

#[global]
Instance euttge_interp_mrec {D E} :
  @Proper ((D ~> itree (D +' E)) -> (itree (D +' E) ~> itree E))
          (Relation.i_pointwise (fun _ => euttge eq) ==>
           Relation.i_respectful (fun _ => euttge eq) (fun _ => euttge eq))
          interp_mrec.
Proof.
  intros f g Hfg R.
  coinduction; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  step in Ht; induction Ht; try easy; cbn. 
  3: { destruct e; constructor. 
    + apply CIH. ebind. apply Hfg.  
      intros ? _ []. apply REL. 
    + intros; step; taus. eauto with itree.
  }
  1,2: constructor; auto with itree.
  all: to_mon; rewrite unfold_interp_mrec, tau_euttge; auto.
Qed.

#[global]
Instance euttge_interp_mrec' {E D R} (ctx : D ~> itree (D +' E)) :
  Proper (euttge eq ==> euttge eq) (@interp_mrec _ _ ctx R).
Proof.
  do 4 red. eapply euttge_interp_mrec. reflexivity.
Qed.
