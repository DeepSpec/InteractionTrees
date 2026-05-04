(* begin hide *)
From Stdlib Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From Coinduction Require Import all.

From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception.
(* end hide *)

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Lemma try_catch_ret : forall E Err R r (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Ret r) kcatch ≅ Ret r.
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Lemma try_catch_tau : forall E Err R t (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Tau t) kcatch ≅ Tau (try_catch t kcatch).
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Lemma try_catch_exc : forall E Err R exc (k :void -> itree (exceptE Err +' E) R)
                               (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Vis (inl1 (Throw exc)) k ) kcatch ≅ kcatch exc.
Proof.
   intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
   rewrite unfold_iter. cbn. unfold ITree.map.
   rewrite bind_bind. setoid_rewrite bind_ret_l. rewrite bind_ret_r.
   reflexivity.
Qed.

Lemma try_catch_ev : forall E A Err R (ev: E A) k (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch (Vis (inr1 ev) k ) kcatch ≅ Vis (inr1 ev) (fun x => Tau (try_catch (k x) kcatch) ).
Proof.
  intros. unfold try_catch. unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter. cbn. unfold ITree.map at 3.
  setoid_rewrite bind_bind. rewrite bind_trigger. cbn.
  setoid_rewrite bind_ret_l. reflexivity.
Qed.

Global Instance proper_eqitree_try_catch {E Err R} : Proper (eq_itree eq ==> pointwise_relation Err (eq_itree eq) ==> eq_itree eq) (@try_catch Err R E).
Proof.
  intros t1 t2 Ht k1 k2 Hk. red in Hk. generalize dependent t2. revert t1.
  coinduction. intros. unfold try_catch.  setoid_rewrite unfold_iter_ktree.
  sinv Ht. 
  - repeat rewrite bind_ret_l. eret. 
  - repeat rewrite bind_ret_l. etau.  
  - destruct e.
    + destruct e. bcbn. 
     rewrite 2 bind_map. rewrite 2 bind_ret_r. 
      step. apply Hk. 
    + cbn. evis. do 2 setoid_rewrite bind_ret_l.  
      step. etau.
Qed.

Global Instance proper_eutt_try_catch {E Err R} : Proper (eutt eq ==> pointwise_relation Err (eutt eq) ==> eutt eq) (@try_catch Err R E).
Proof.
  intros t1 t2 Ht k1 k2 Hk. red in Hk. generalize dependent t2. revert t1.
  coinduction. intros. unfold try_catch. setoid_rewrite unfold_iter_ktree.
  step in Ht. 
  hinduction Ht before c; intros; subst; eauto.
  - repeat rewrite bind_ret_l. eret. 
  - repeat rewrite bind_ret_l. etau.  
  - destruct e.
  (* RTODO: make cbn work here *)
    + destruct e. bcbn. rewrite 2 bind_map. rewrite 2 bind_ret_r. 
      step. apply Hk. 
    + bcbn. evis. do 2 setoid_rewrite bind_ret_l.  
      step. etau. 
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
Qed.


Global Instance proper_eqitree_throw_prefix_false {E Err R} : Proper (eqit false false eq ==> eqit false false eq) (@throw_prefix Err R E).
Proof.
  intros t1 t2 Ht. generalize dependent t2. revert t1.
  coinduction. intros. unfold throw_prefix. setoid_rewrite unfold_iter_ktree.
  step in Ht. inv Ht.
  - repeat rewrite bind_ret_l. bcbn. eret.
  - destruct e.
    + destruct e. bcbn. eret.
    + setoid_rewrite bind_map. rewrite 2 bind_trigger.
      evis. step. bcbn. etau. 
Qed.

Global Instance proper_eutt_throw_prefix {E Err R} : Proper (eutt eq ==> eutt eq) (@throw_prefix Err R E).
Proof.
  intros t1 t2 Ht. generalize dependent t2. revert t1.
  coinduction. intros. unfold throw_prefix. setoid_rewrite unfold_iter_ktree.
  step in Ht. hinduction Ht before c; intros; subst; eauto.
  - repeat rewrite bind_ret_l. bcbn. eret.
  - destruct e.
    + destruct e. bcbn. eret.
    + setoid_rewrite bind_map. rewrite 2 bind_trigger.
      evis. step. bcbn. etau. 
  - bcbn. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
  - bcbn. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
Qed.

Global Instance proper_eqitree_throw_prefix {E Err R b} : Proper (eqit b b eq ==> eqit b b eq) (@throw_prefix Err R E).
Proof.
  destruct b; [apply proper_eutt_throw_prefix | apply proper_eqitree_throw_prefix_false].
Qed.

Definition throw_prefix_ret : forall E Err R (r : R),
    @throw_prefix Err R E (Ret r) ≅ Ret (inl r).
Proof.
  intros. setoid_rewrite unfold_iter_ktree. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Definition throw_prefix_tau : forall E Err R (t : itree (exceptE Err +' E) R),
    throw_prefix (Tau t) ≅ Tau (throw_prefix t) .
Proof.
  intros. setoid_rewrite unfold_iter_ktree at 1. cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Definition throw_prefix_exc : forall E Err R k (e : Err), 
    @throw_prefix Err R E (Vis (inl1 (Throw e) ) k) ≅ Ret (inr e).
Proof.
  intros. setoid_rewrite unfold_iter_ktree. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Definition throw_prefix_ev : forall X E Err R k  (e : E X) , 
    throw_prefix ((Vis (inr1 e) k : itree (exceptE Err +' E) R )) ≅ Vis (inr1 e) (fun x => Tau (throw_prefix (k x)) ).
Proof.
  intros. setoid_rewrite unfold_iter_ktree at 1. cbn. rewrite bind_map.
  rewrite bind_trigger. apply eqit_Vis. intros. reflexivity.
Qed.

Lemma try_catch_throw_prefix_nop : forall E Err R  kcatch (ttry : itree (exceptE Err +' E) R),
    try_catch (throw_prefix ttry) kcatch ≈ throw_prefix ttry.
Proof. 
  intros E Err R kcatch. coinduction. intros.
  destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. rewrite try_catch_ret. reflexivity.
  - rewrite Heq. rewrite throw_prefix_tau. rewrite try_catch_tau. etau.
  - destruct e.
   + destruct e. rewrite Heq. rewrite throw_prefix_exc. rewrite try_catch_ret. reflexivity.
   + rewrite Heq. rewrite throw_prefix_ev. rewrite try_catch_ev. evis.
     rewrite try_catch_tau. repeat rewrite tau_euttge. apply CIH.
Qed.

Lemma throw_prefix_bind_decomp : forall E Err R (t : itree (exceptE Err +' E) R ),
    t ≈ ITree.bind (throw_prefix t) (fun r => 
                                    match r with 
                                    | inr e => v <- trigger (inl1 (Throw e));; match v : void with end
                                    | inl a => Ret a
                                    end).
Proof.
  intros E Err R. coinduction. intros.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. rewrite bind_ret_l. eret. 
  - rewrite Heq. rewrite throw_prefix_tau. rewrite bind_tau. etau.
  - destruct e.
    + rewrite Heq. destruct e. rewrite throw_prefix_exc. rewrite bind_ret_l. bcbn. evis. 
      easy. 
    + rewrite Heq. rewrite throw_prefix_ev. rewrite bind_vis. evis. 
      intros. rewrite tau_euttge. apply CIH. 
Qed.

Lemma try_catch_to_throw_prefix : forall E Err R (ttry : itree (exceptE Err +' E) R  ) (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch ttry kcatch ≈ ITree.bind (throw_prefix ttry) (fun r =>
                                                            match r with
                                                            | inr e => kcatch e
                                                            | inl a => Ret a
                                                            end).
Proof.
  intros. revert ttry. coinduction. 
  intros. destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite try_catch_ret. rewrite throw_prefix_ret. rewrite bind_ret_l. 
    eret. 
  - rewrite Heq. rewrite try_catch_tau. rewrite throw_prefix_tau. rewrite bind_tau.
    etau. 
  - destruct e.
    + destruct e. rewrite Heq. rewrite try_catch_exc. rewrite throw_prefix_exc. rewrite bind_ret_l.
      reflexivity. 
    + rewrite Heq. rewrite try_catch_ev. rewrite throw_prefix_ev. rewrite bind_vis. setoid_rewrite tau_euttge.
      evis. 
Qed.

Lemma throw_prefix_of_try_catch :  forall E Err R (ttry : itree (exceptE Err +' E) R  ) (kcatch : Err -> itree (exceptE Err +' E) R),
    throw_prefix (try_catch ttry kcatch) ≈ try_catch (ITree.bind ttry (fun r => Ret (inl r)) ) (fun e => throw_prefix (kcatch e) ).
Proof.
  intros. revert ttry. coinduction. 
  intros. destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite bind_ret_l. repeat rewrite try_catch_ret. rewrite throw_prefix_ret.
    eret. 
  - rewrite Heq. rewrite bind_tau. repeat rewrite try_catch_tau. rewrite throw_prefix_tau.
    etau. 
  - destruct e.
    + destruct e. rewrite Heq. rewrite bind_vis. repeat rewrite try_catch_exc.
      reflexivity. 
    + rewrite Heq. rewrite bind_vis. repeat rewrite try_catch_ev. rewrite throw_prefix_ev.
      setoid_rewrite throw_prefix_tau.
      repeat setoid_rewrite tau_euttge.
      evis. 
Qed.

Lemma throw_prefix_bind : forall E Err R S (t : itree (exceptE Err +' E) R ) (k : R -> itree (exceptE Err +' E) S),
    throw_prefix (ITree.bind t k) ≅ ITree.bind (throw_prefix t) 
                 (fun r : R + Err => match r with 
                                  | inl r' => throw_prefix (k r') 
                                  | inr e => Ret (inr e) end ).
Proof.
  intros. revert t. coinduction. 
  intros. destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. repeat rewrite bind_ret_l.
    reflexivity. 
  - rewrite Heq. rewrite throw_prefix_tau. repeat rewrite bind_tau. rewrite throw_prefix_tau.
    etau. 
  - destruct e.
    + destruct e. rewrite Heq. rewrite throw_prefix_exc. rewrite bind_vis. rewrite throw_prefix_exc.
      rewrite bind_ret_l. eret. 
    + rewrite Heq. rewrite throw_prefix_ev. repeat rewrite bind_vis. rewrite throw_prefix_ev.
      evis. rewrite bind_tau. step. taus. apply CIH.  
Qed.

Lemma throw_prefix_iter : forall E Err A B (body : A -> itree (exceptE Err +' E) (A + B)  ) (init : A),
    throw_prefix (ITree.iter body init) ≅ ITree.iter (R := B + Err)  (fun a : A => r <- throw_prefix (body a);; 
                                                             match (r : (A + B) + Err) with
                                                             | inl (inl a) => Ret (inl a)
                                                             | inl (inr b) => Ret (inr (inl b))
                                                             | inr e => Ret (inr (inr e)) end)  init.
Proof.
  intros E Err A B. coinduction. intros.
  setoid_rewrite unfold_iter_ktree at 2 3.
  destruct (observe (body init) ) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq at 1. rewrite bind_ret_l. setoid_rewrite bind_bind. 
    rewrite Heq at 1. rewrite throw_prefix_ret. rewrite bind_ret_l.
    destruct r; rewrite bind_ret_l.
    + rewrite throw_prefix_tau. etau. 
    + rewrite throw_prefix_ret. eret. 
  - rewrite Heq at 1. setoid_rewrite bind_bind. rewrite Heq at 1.
    rewrite throw_prefix_tau. repeat rewrite bind_tau. rewrite throw_prefix_tau.
    etau. setoid_rewrite throw_prefix_bind at 1. ebind; intros; subst. 
    destruct u2 as [ [ a | b] | e ].
    + rewrite bind_ret_l. rewrite throw_prefix_tau. step; etau. 
    + rewrite bind_ret_l. rewrite throw_prefix_ret. step; eret. 
    + rewrite bind_ret_l. step; eret. 
  - rewrite Heq at 1. setoid_rewrite bind_bind. rewrite Heq at 1.
    destruct e.
    + destruct e. rewrite bind_vis. rewrite throw_prefix_exc.
      setoid_rewrite throw_prefix_exc. repeat rewrite bind_ret_l.
      eret. 
    + rewrite bind_vis. rewrite throw_prefix_ev. setoid_rewrite throw_prefix_ev.
      rewrite bind_vis. setoid_rewrite bind_tau. evis. step; etau. 
      rewrite throw_prefix_bind. ebind; intros; subst. 
      destruct u2 as [ [ a | b] | e' ].
      * rewrite bind_ret_l. rewrite throw_prefix_tau. step; etau. 
      * rewrite bind_ret_l. rewrite throw_prefix_ret.
        step; eret. 
      * rewrite bind_ret_l. step; eret. 
Qed.
