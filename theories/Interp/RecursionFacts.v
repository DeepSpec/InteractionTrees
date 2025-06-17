(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)

(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)

Require Import Paco.paco.

From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
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
      pstep; constructor. intros. left.
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
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. auto with paco itree.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k; ginit. pcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree.
  1: apply reflexivity.
  all: rewrite unfold_interp_mrec; ITree.fold_subst.
  all: try (gstep; econstructor; eauto with paco).
  - rewrite <- bind_bind; eauto with paco.
  - intros. red. rewrite bind_tau. gstep; constructor; auto with paco.
Qed.

Theorem interp_mrec_trigger {U} (a : (D +' E) U) :
    interp_mrec ctx (ITree.trigger a)
  ≳ mrecursive ctx _ a.
Proof.
  rewrite unfold_interp_mrec; unfold mrecursive.
  destruct a; cbn.
  rewrite tau_euttge, bind_ret_r.
  reflexivity.
  pstep; constructor. intros; left. rewrite tau_euttge, unfold_interp_mrec; cbn.
  apply reflexivity.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx c ≈ interp (mrecursive ctx) c.
Proof.
  rewrite <- (tau_eutt (interp _ _)).
  revert_until T. ginit. pcofix CIH. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - gstep; repeat econstructor; eauto.
  - gstep; constructor; eauto with paco.
  - rewrite interp_mrec_bind. unfold mrec.
    gstep; constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto with paco.
  - rewrite tau_euttge. unfold ITree.trigger, case_; simpl. rewrite bind_vis.
    gstep. constructor.
    intros; red.
    rewrite bind_ret_l. rewrite tau_euttge. auto with paco.
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
  revert t. ginit; pcofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t).
  - rewrite 2 unfold_interp_mrec; cbn; gstep; repeat constructor; auto with paco.
  - rewrite unfold_interp, 2 unfold_interp_mrec; cbn. gstep.
    constructor; auto with paco.
  - rewrite interp_vis.
    rewrite (unfold_interp_mrec _ (Vis _ _)).
    destruct e; cbn.
    + rewrite 2 interp_mrec_bind.
      gstep; constructor.
      guclo eqit_clo_bind; econstructor; [reflexivity|].
      intros ? _ []; rewrite unfold_interp_mrec; cbn; auto with paco.
    + unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
      rewrite bind_trigger, unfold_interp_mrec; cbn.
      rewrite tau_euttge.
      gstep; constructor.
      intros; red. gstep; constructor.
      rewrite unfold_interp_mrec; cbn.
      auto with paco.
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
  ginit; pcofix CIH; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  punfold Ht; induction Ht; cbn; pclearbot.
  3: { destruct e; gstep; constructor.
    + gfinal; left. apply CIH.
      eapply eutt_clo_bind; eauto.
      intros ? _ []. auto with itree.
    + gstep; constructor. auto with paco itree.
  }
  1,2: gstep; constructor; auto with paco itree.
  1,2: rewrite unfold_interp_mrec, tau_euttge; auto.
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
  ginit; pcofix CIH; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  punfold Ht; induction Ht; cbn; pclearbot.
  3: { destruct e; gstep; constructor.
    + gfinal; left. apply CIH.
      eapply eqit_bind; auto. apply Hfg.
    + gstep; constructor. auto with paco itree.
  }
  1,2: gstep; constructor; auto with paco.
  1: rewrite unfold_interp_mrec, tau_euttge; auto.
  discriminate.
Qed.

#[global]
Instance euttge_interp_mrec' {E D R} (ctx : D ~> itree (D +' E)) :
  Proper (euttge eq ==> euttge eq) (@interp_mrec _ _ ctx R).
Proof.
  do 4 red. eapply euttge_interp_mrec. reflexivity.
Qed.

Module Interp_mrec_loop2.

Inductive invariant {D E} (ctx : D ~> itree (D +' E)) {R}
  : itree (D +' E) R -> itree (D +' E) R -> Prop :=
| Equal {t} : invariant ctx t t
| Interp {A} {t : itree (D +' E) A} {k k' : A -> _} : (forall a, invariant ctx (k a) (k' a)) -> invariant ctx (t >>= k) (interp (Handler.case_ ctx Handler.inr_) t >>= k')
| Bind {A} {t : itree (D +' E) A} {k k' : A -> _}
  : (forall (a : A), invariant ctx (k a) (k' a)) ->
    invariant ctx (t >>= k) (t >>= fun x => k' x)
.
Hint Constructors invariant : core.

Inductive itree_case {E R} (t : itree E R) : Prop :=
| CaseRet r : Ret r ≅ t -> itree_case t
| CaseTau u : Tau u ≅ t -> itree_case t
| CaseVis A (e : E A) k : Vis e k ≅ t -> itree_case t.

Lemma case_itree {E R} (t : itree E R) : itree_case t.
Proof.
  destruct (observe t) eqn:Eq.
  - econstructor 1. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 2. rewrite <- Eq, <- itree_eta; reflexivity.
  - econstructor 3. rewrite <- Eq, <- itree_eta; reflexivity.
Qed.

Lemma interp_mrec_loop2_ {D E} (ctx : D ~> itree (D +' E)) {R}
  : forall {t : itree (D +' E) R} {u : itree (D +' E) R},
    invariant ctx t u -> interp_mrec ctx t ≈ interp_mrec (Handler.cat ctx (Handler.case_ ctx Handler.inr_)) u.
Proof with auto.
  einit.
  ecofix SELF. induction 1 as [t | A t k | A t k k'].
  - destruct (case_itree t) as [ ? H | u H | A [d|e] k H ]; rewrite <- H; rewrite 2 unfold_interp_mrec; simpl.
    + eret.
    + etau.
    + etau.
    + evis.
  - destruct (case_itree t) as [ ? W | u W | ? [d|e] h W ]; rewrite <- W.
    + rewrite interp_ret. rewrite 2 bind_ret_l.
      apply H0.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec. simpl.
      etau.
    + rewrite interp_vis. simpl. rewrite bind_bind.
      rewrite unfold_interp_mrec; simpl.
      destruct (case_itree (ctx _ d)) as [ ? H1 | ? H1 | ? [d'|e] ? H1 ]; rewrite <- H1.
      * rewrite 2 bind_ret_l.
        rewrite bind_tau.
        rewrite unfold_interp_mrec with (t := Tau _); simpl.
        etau.
      * rewrite 2 bind_tau.
        rewrite 2 unfold_interp_mrec; simpl.
        rewrite tau_euttge.
        setoid_rewrite tau_euttge at 3.
        etau. ebase.
      * rewrite 2 bind_vis, 2 unfold_interp_mrec. simpl.
        rewrite tau_euttge.
        unfold Handler.cat at 2.
        setoid_rewrite tau_euttge at 3.
        etau. ebase. right. apply SELFL. eauto.
      * rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl.
        rewrite tau_euttge.
        setoid_rewrite tau_euttge at 3.
        evis. etau. ebase.
    + rewrite interp_vis; simpl. unfold Handler.inr_ at 2, Handler.htrigger.
      rewrite bind_trigger. rewrite 2 bind_vis.
      rewrite 2 unfold_interp_mrec; simpl.
      setoid_rewrite unfold_interp_mrec at 2; simpl.
      setoid_rewrite tau_euttge at 3.
      evis. etau.
  - destruct (case_itree t) as [ ? W | ? W | ? [d|e] h W]; rewrite <- W.
    + rewrite 2 bind_ret_l. apply H0.
    + rewrite 2 bind_tau, 2 unfold_interp_mrec; simpl. etau.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl.
      unfold Handler.cat at 2. etau. ebase.
    + rewrite 2 bind_vis, 2 unfold_interp_mrec; simpl. evis. etau.
Qed.

End Interp_mrec_loop2.

Lemma interp_mrec_loop2 {D E} (ctx : D ~> itree (D +' E)) {R} {t : itree (D +' E) R}
  : interp_mrec ctx t ≈ interp_mrec (Handler.cat ctx (Handler.case_ ctx inr_)) t.
Proof.
  apply Interp_mrec_loop2.interp_mrec_loop2_.
  constructor.
Qed.

Theorem mrec_loop2 {D E} (ctx : D ~> itree (D +' E)) {R} {d : D R}
  : mrec ctx d ≈ mrec (Handler.cat ctx (Handler.case_ ctx inr_)) d.
Proof.
  unfold mrec.
  unfold Handler.cat at 2.
  rewrite <- unfold_interp_mrec_h.
  apply interp_mrec_loop2.
Qed.
