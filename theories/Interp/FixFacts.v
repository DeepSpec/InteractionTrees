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
     Interp.MorphismsFacts.

Import ITreeNotations.

Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

(** Unfolding of [interp_mrec]. *)

Definition interp_mrecF R (ot : itreeF (D +' E) R _) : itree E R :=
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
  interp_mrec ctx _ t ≅ interp_mrecF _ (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite ret_bind_; reflexivity. (* TODO: ret_bind, vis_bind are sloooow *)
  - destruct e; cbn.
    + rewrite ret_bind_; reflexivity.
    + rewrite vis_bind_. pfold; constructor. left.
      pfold; constructor.
      left. rewrite ret_bind.
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
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  pupto2_final.
  punfold H0. inv H0; simpobs; pclearbot; [| |destruct e].
  - apply reflexivity.
  - pfold. econstructor. eauto.
  - pfold. econstructor. apply pointwise_relation_fold in REL.
    right. eapply CIH. rewrite REL. reflexivity.
  - pfold. econstructor. left; pfold; constructor. auto.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx _ (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx _ t) (fun x => interp_mrec ctx _ (k x)).
Proof.
  intros. pupto2_init; revert t k; pcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t), (unfold_bind t).
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree;
    try rewrite <- bind_bind.
  1: { pupto2_final; apply reflexivity. }
  all: try (pfold; econstructor; eauto).
  intros.
  pupto2_final. left; pfold; constructor. auto.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx _ c ≈ interp (case_ (mrec ctx) ITree.liftE) _ c.
Proof.
  repeat intro. pupto2_init. revert_until T. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto 8.
  - rewrite interp_mrec_bind.
    pfold; constructor.
    pupto2 eutt_nested_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto.

  - unfold ITree.liftE, case_; simpl. rewrite vis_bind_.
    pfold; constructor.
    pupto2_final.
    left; pfold; econstructor.
    left.
    rewrite ret_bind_. auto.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx _ d ≈ interp (case_ (mrec ctx) ITree.liftE) _ (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

End Facts.

Lemma rec_unfold {E A B} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≈ interp (case_ (calling' (rec f)) ITree.liftE) _ (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  eapply eutt_interp_gen.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) ca :
  interp f _ (loop_ t ca) ≅ loop_ (fun ca => interp f _ (t ca)) ca.
Proof.
  pupto2_init. revert ca. pcofix CIH. intros.
  unfold loop. rewrite !unfold_loop'. unfold loop_once.
  rewrite interp_bind.
  pupto2 eq_itree_clo_bind. econstructor; [reflexivity|].
  intros. subst. rewrite unfold_interp. pupto2_final. pfold. red.
  destruct u2; simpl; eauto.
Qed.
