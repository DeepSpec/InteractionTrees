
(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts
     Interp.MorphismsFacts.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

Set Universe Polymorphism.
(* end hide *)

(* Morphism Category -------------------------------------------------------- *)



Lemma eh_cmp_id_left_strong :
  forall A R (t : itree A R), interp eh_id R t ≈ t.
Proof.
  intros A R.
  intros t.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold; pupto2_init; revert t; pcofix CIH'; intros.
  rewrite unfold_interp. unfold interp_u.
  destruct (observe t); cbn; eauto.
  - pfold. econstructor. auto.
  - unfold eh_id, ITree.liftE. rewrite vis_bind.
    pfold; do 2 constructor.
    left; rewrite ret_bind; auto.
Qed.


Lemma eh_cmp_id_left :
  forall A B (f : A ~> itree B), eh_cmp eh_id f ≡ f.
Proof.
  intros A B f X e.
  unfold eh_cmp. apply eh_cmp_id_left_strong.
Qed.


Lemma eh_cmp_id_right :
  forall A B (f : A ~> itree B), eh_cmp f eh_id ≡ f.
Proof.
  intros B A f X e.
  unfold eh_cmp.
  unfold eh_id. unfold ITree.liftE.
  rewrite unfold_interp. unfold interp_u.
  cbn. setoid_rewrite tau_eutt. setoid_rewrite interp_ret. rewrite bind_ret.
  reflexivity.
Qed.

Lemma eh_both_left_right_id : forall A B X e,  eh_both eh_inl eh_inr X e = (@eh_id (A +' B)) X e.
Proof.
  intros A B X e.
  unfold eh_both.
  unfold eh_id. unfold ITree.liftE.
  destruct e.
  - unfold eh_inl. reflexivity.
  - unfold eh_inr. reflexivity.
Qed.

Lemma eh_cmp_assoc : forall A B C D (h : C ~> itree D) (g : B ~> itree C) (f : A ~> itree B),
    eh_cmp h (eh_cmp g f) ≡ (eh_cmp (eh_cmp h g) f).
Proof.
  intros A B C D h g f X e.
  unfold eh_cmp. rewrite interp_interp. reflexivity.
Qed.

Lemma eh_par_id : forall A B, eh_par eh_id eh_id ≡ (@eh_id (A +' B)).
Proof.
  intros A B X e.
  unfold eh_par.
  unfold eh_id.
  destruct e.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inl1 (E2:=B)) (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
  - unfold ITree.liftE.
    rewrite translate_vis.
    assert (pointwise_relation X (@eq_itree (A +' B) _ _ eq) (fun x : X => translate (inr1 (E2:=B)) (Ret x)) (fun x : X => Ret x)).
    { intros x. rewrite translate_ret. reflexivity. }
    rewrite H. reflexivity.
Qed.

Lemma eh_swap_swap_id : forall A B, eh_cmp eh_swap eh_swap ≡ (eh_id : (A +' B) ~> itree (A +' B)).
Proof.
  intros A B X e.
  unfold eh_cmp. unfold eh_swap. unfold eh_lift.
  (* TODO: Why does [rewrite interp_liftE.] not work? *)
  match goal with
  | [ |- _ (interp ?f ?X (ITree.liftE ?e)) _ ] =>
    rewrite (interp_liftE f e)
  end.
  rewrite tau_eutt.
  destruct e; simpl; reflexivity.
Qed.

Lemma eh_empty_unit_l : forall (A : Type -> Type), eh_cmp eh_empty_right eh_inl ≡ (eh_id : A ~> itree A).
Proof.
  intros A X e.
  unfold eh_cmp.
  unfold eh_empty_right.
  unfold eh_inl.
  unfold eh_lift.
  rewrite interp_liftE.
  setoid_rewrite tau_eutt. rewrite bind_ret.
  reflexivity.
Qed.

Lemma eh_empty_unit_r : forall A, eh_cmp eh_empty_left eh_inr ≡ (eh_id : A ~> itree A).
Proof.
  intros A X e.
  unfold eh_cmp.
  unfold eh_empty_left.
  unfold eh_inr.
  unfold eh_lift.
  rewrite interp_liftE.
  setoid_rewrite tau_eutt. rewrite bind_ret.
  reflexivity.
Qed.
