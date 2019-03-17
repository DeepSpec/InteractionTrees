(** Properties of [Fix.mrec] and [Fix.rec]. *)

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
     Core.ITree
     Core.KTree
     Core.KTreeFacts
     Eq.Eq
     Eq.UpToTaus
     Eq.SimUpToTaus
     Indexed.Sum
     Indexed.Function
     Indexed.OpenSum
     Interp.Interp
     Interp.MorphismsFacts
     Interp.Recursion.

Import ITreeNotations.

Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mrec]. *)

Definition _interp_mrec R (ot : itreeF (D +' E) R _) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec ctx _ t)
  | VisF e k => Tau
    match e with
    | inl1 d => interp_mrec ctx _ (ctx _ d >>= k)
    | inr1 e => Vis e (fun x => interp_mrec ctx _ (k x))
    end
  end.

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  interp_mrec ctx _ t ≅ _interp_mrec _ (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite bind_ret_; reflexivity. (* TODO: bind_ret, bind_vis are sloooow *)
  - destruct e; cbn.
    + rewrite bind_ret_; reflexivity.
    + rewrite bind_vis_. ustep; constructor.
      ustep; constructor. intros.
      rewrite bind_ret.
      apply reflexivity.
Qed.

Lemma ret_mrec {T} (x: T) :
  interp_mrec ctx _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

Lemma tau_mrec {T} (t: itree _ T) :
  interp_mrec ctx _ (Tau t) ≅ Tau (interp_mrec ctx _ t).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_right {T U} (e : E U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inr1 e) k) ≅
  Tau (Vis e (fun x => interp_mrec ctx _ (k x))).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_left {T U} (d : D U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx _ (Vis (inl1 d) k) ≅
  Tau (interp_mrec ctx _ (ITree.bind (ctx _ d) k)).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Hint Rewrite @ret_mrec : itree.
Hint Rewrite @vis_mrec_left : itree.
Hint Rewrite @vis_mrec_right : itree.
Hint Rewrite @tau_mrec : itree.

Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (interp_mrec ctx R).
Proof.
  ucofix CIH. intros.
  rewrite !unfold_interp_mrec.
  uunfold H0. inv H0; simpobs; [| |destruct e].
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. apply pointwise_relation_fold in REL.
    ubase. eapply CIH. rewrite REL. reflexivity.
  - econstructor. ustep; constructor. auto with paco.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx _ (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx _ t) (fun x => interp_mrec ctx _ (k x)).
Proof.
  revert t k; ucofix CIH; intros.
  rewrite (unfold_interp_mrec _ t), (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind.
  1: { apply reflexivity. }
  all: try (econstructor; eauto with paco).
  intros.
  ustep; constructor. auto with paco.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.lift.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx _ c ≅ interp (mrecursive ctx) _ c.
Proof.
  revert_until T. ucofix CIH. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - econstructor. eauto.
  - econstructor. eauto with paco.
  - rewrite interp_mrec_bind.
    constructor.
    uclo eq_itree_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto with paco.

  - unfold ITree.lift, case_; simpl. rewrite bind_vis_.
    constructor.
    ustep; econstructor. intros.
    rewrite bind_ret_. auto with paco.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx _ d ≅ interp (mrecursive ctx) _ (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

Lemma interp_mrecursive {T} (d : D T) :
  interp (mrecursive ctx) _ (lift_inl1 _ d) ≅ Tau (mrec ctx _ d).
Proof.
  unfold mrecursive. unfold lift_inl1.
  rewrite interp_lift. cbn. reflexivity.
Qed.

End Facts.

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (rec f)) ITree.lift.

Lemma rec_as_interp {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≅ interp (recursive f) _ (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  eapply eq_itree_interp.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_recursive_call {E A B} (f : A -> itree (callE A B +' E) B) (x:A) :
   interp (recursive f) _ (call x) ≅ Tau (rec f x).
Proof.
  unfold recursive. unfold call.
  rewrite interp_lift. cbn. reflexivity.
Qed.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) ca :
  interp f _ (loop_ t ca) ≅ loop_ (fun ca => interp f _ (t ca)) ca.
Proof.
  revert ca. ucofix CIH. intros.
  unfold loop. rewrite !unfold_loop'. unfold loop_once.
  rewrite interp_bind.
  uclo eq_itree_clo_bind. econstructor; [reflexivity|].
  intros. subst. rewrite unfold_interp.
  destruct u2; econstructor; eauto with paco.
Qed.
