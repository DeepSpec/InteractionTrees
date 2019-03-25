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
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
     Indexed.OpenSum
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
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite bind_ret_; reflexivity. (* TODO: bind_ret, bind_vis are sloooow *)
  - destruct e; cbn.
    + rewrite bind_ret_; reflexivity.
    + rewrite bind_vis_. wstep; constructor.
      wstep; constructor. intros.
      rewrite bind_ret.
      apply reflexivity.
Qed.

Lemma ret_mrec {T} (x: T) :
  interp_mrec ctx (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

Lemma tau_mrec {T} (t: itree _ T) :
  interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_right {T U} (e : E U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx (Vis (inr1 e) k) ≅
  Tau (Vis e (fun x => interp_mrec ctx (k x))).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Lemma vis_mrec_left {T U} (d : D U) (k : U -> itree (D +' E) T) :
  interp_mrec ctx (Vis (inl1 d) k) ≅
  Tau (interp_mrec ctx (ITree.bind (ctx _ d) k)).
Proof. rewrite unfold_interp_mrec. reflexivity. Qed.

Hint Rewrite @ret_mrec : itree.
Hint Rewrite @vis_mrec_left : itree.
Hint Rewrite @vis_mrec_right : itree.
Hint Rewrite @tau_mrec : itree.

Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_mrec _ _ ctx R).
Proof.
  wcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  wunfold H0. inv H0; simpobs; [| |destruct e].
  - apply reflexivity.
  - wstep. econstructor. eauto with paco.
  - wstep. econstructor. apply pointwise_relation_fold in REL.
    wbase. eapply CIH. rewrite REL. reflexivity.
  - wstep. econstructor. wstep; constructor. auto with paco.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k; wcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t). (* TODO: slow *)
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind.
  1: { apply reflexivity. }
  all: try (wstep; econstructor; eauto with paco).
  intros.
  wstep; constructor. auto with paco.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.send.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx c ≅ interp (mrecursive ctx) c.
Proof.
  revert_until T. wcofix CIH. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - wstep. econstructor. eauto.
  - wstep. econstructor. eauto with paco.
  - rewrite interp_mrec_bind.
    wstep. constructor.
    wclo eq_itree_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto with paco.
  - unfold ITree.send, case_; simpl. rewrite bind_vis_.
    wstep. constructor.
    wstep; econstructor. intros.
    rewrite bind_ret_. auto with paco.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx d ≅ interp (mrecursive ctx) (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

Lemma interp_mrecursive {T} (d : D T) :
  interp (mrecursive ctx) (send_inl1 d) ≅ Tau (mrec ctx d).
Proof.
  unfold mrecursive. unfold send_inl1.
  rewrite interp_send. cbn. reflexivity.
Qed.

End Facts.

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (rec f)) ITree.send.

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
  rewrite interp_send. cbn. reflexivity.
Qed.

Lemma unfold_forever {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ (t >>= fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (_ >>= _)).
  reflexivity.
Qed.

Lemma interp_forever {E F} (f : E ~> itree F) {R S}
      (t : itree E R)
  : interp f (ITree.forever t)
  ≅ @ITree.forever F R S (interp f t).
Proof.
  wcofix CIH.
  rewrite unfold_forever.
  rewrite (unfold_forever (interp _ _)).
  rewrite interp_bind.
  wclo eq_itree_clo_bind. econstructor; [reflexivity |].
  intros ? _ []. rewrite interp_tau.
  wstep. constructor; auto with paco.
Qed.
