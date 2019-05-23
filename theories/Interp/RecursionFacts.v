(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)

(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)

Require Import Paco.paco.

From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
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
  | VisF e k => Tau
    match e with
    | inl1 d => interp_mrec ctx (ctx _ d >>= k)
    | inr1 e => Vis e (fun x => interp_mrec ctx (k x))
    end
  end.

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  interp_mrec ctx t ≅ _interp_mrec (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_aloop.
  destruct observe; cbn.
  - reflexivity.
  - rewrite bind_ret; reflexivity. (* TODO: bind_ret, bind_vis are sloooow *)
  - destruct e; cbn.
    + rewrite bind_ret; reflexivity.
    + rewrite bind_vis. pstep; constructor. left.
      pstep; constructor. intros. left.
      rewrite bind_ret.
      apply reflexivity.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.trigger.

Global Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_mrec _ _ ctx R).
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. red. auto with paco.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k; ginit. gcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t). (* TODO: should be [unfold_bind] but it is much slower *)
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree.
  1: apply reflexivity.
  all: rewrite unfold_interp_mrec.
  all: try (gstep; econstructor; eauto with paco).
  - rewrite <- bind_bind; eauto with paco.
  - gstep; constructor; auto with paco.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx c ≅ interp (mrecursive ctx) c.
Proof.
  revert_until T. ginit. gcofix CIH. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - gstep. econstructor. eauto.
  - gstep. econstructor. eauto with paco.
  - rewrite interp_mrec_bind.
    gstep. constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto with paco.
  - unfold ITree.trigger, case_; simpl. rewrite bind_vis.
    gstep. constructor.
    gstep; econstructor. intros. red.
    rewrite bind_ret. auto with paco.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx d ≅ interp (mrecursive ctx) (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

Lemma interp_mrecursive {T} (d : D T) :
  interp (mrecursive ctx) (trigger_inl1 d) ≅ Tau (mrec ctx d).
Proof.
  unfold mrecursive. unfold trigger_inl1.
  rewrite interp_trigger. cbn. reflexivity.
Qed.

Theorem unfold_interp_mrec_h {T} (t : itree _ T)
  : interp_mrec ctx (interp (case_ ctx inr_) t)
  ≳ interp_mrec ctx t.
Proof.
  revert t. ginit; gcofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t);
    rewrite 2 unfold_interp_mrec; cbn; gstep; constructor.
  - auto.
  - rewrite bind_ret; auto with paco.
  - rewrite bind_map.
    destruct e.
    + rewrite 2 interp_mrec_bind.
      guclo eqit_clo_bind; econstructor; [reflexivity|].
      intros ? _ []; auto with paco.
    + cbn. unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
      rewrite bind_trigger, unfold_interp_mrec; cbn.
      rewrite tau_eutt.
      gstep; constructor. auto with paco.
Qed.

End Facts.

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (rec f)) ITree.trigger.

Lemma rec_as_interp {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≅ interp (recursive f) (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  eapply eq_itree_interp.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_recursive_call {E A B} (f : A -> itree (callE A B +' E) B) (x:A) :
   interp (recursive f) (call x) ≅ Tau (rec f x).
Proof.
  unfold recursive. unfold call.
  rewrite interp_trigger. cbn. reflexivity.
Qed.
