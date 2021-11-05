From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Events.Exception
.

(* end hide *)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
From Paco Require Import paco.

Global Instance proper_eqitree_try_catch {E Err R} : Proper (eq_itree eq ==> pointwise_relation Err (eq_itree eq) ==> eq_itree eq) (@try_catch Err R E).
Proof.
  intros t1 t2 Ht k1 k2 Hk. red in Hk. generalize dependent t2. revert t1.
  ginit. gcofix CIH. intros. unfold try_catch.  setoid_rewrite unfold_iter_ktree.
  pinversion Ht; try inv CHECK.
  - repeat rewrite bind_ret_l. gfinal; right. pfold; constructor; auto.
  - repeat rewrite bind_ret_l. gstep; constructor. gfinal. left. eauto.
  - destruct e.
    + destruct e. cbn. repeat rewrite bind_map. repeat rewrite bind_ret_r.  gfinal.
      right. eapply paco2_mon; try apply Hk. intros; contradiction.
    + cbn. repeat rewrite bind_map. repeat rewrite bind_trigger. gstep. constructor. intros.
      gstep. constructor. gfinal. left. eauto.
Qed.

Global Instance proper_eutt_try_catch {E Err R} : Proper (eutt eq ==> pointwise_relation Err (eutt eq) ==> eutt eq) (@try_catch Err R E).
Proof.
  intros t1 t2 Ht k1 k2 Hk. red in Hk. generalize dependent t2. revert t1.
  ginit. gcofix CIH. intros. unfold try_catch. setoid_rewrite unfold_iter_ktree.
  punfold Ht. red in Ht.
  hinduction Ht before r; intros; subst; eauto; try inv CHECK; pclearbot.
  - repeat rewrite bind_ret_l. gfinal; right. pfold; constructor; auto.
  - repeat rewrite bind_ret_l. gstep; constructor. gfinal. left. eauto.
  - destruct e.
    + destruct e. cbn. repeat rewrite bind_map. repeat rewrite bind_ret_r.  gfinal.
      right. eapply paco2_mon; try apply Hk. intros; contradiction.
    + cbn. repeat rewrite bind_map. repeat rewrite bind_trigger. gstep. constructor. intros.
      gstep. constructor. gfinal. left. eauto.
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
Qed.


Global Instance proper_eqitree_throw_prefix {E Err R b} : Proper (eqit eq b b ==> eqit eq b b) (@throw_prefix Err R E).
Proof.
  intros t1 t2 Ht. generalize dependent t2. revert t1.
  ginit. gcofix CIH. intros. unfold throw_prefix. setoid_rewrite unfold_iter_ktree.
  punfold Ht. red in Ht. hinduction Ht before r; intros; subst; eauto; try inv CHECK.
  - repeat rewrite bind_ret_l. gfinal; right. subst. pfold; constructor; auto.
  - repeat rewrite bind_ret_l. gstep; constructor. gfinal. left. pclearbot.
    eapply CIH. auto.
  - destruct e.
    + destruct e. cbn. repeat rewrite bind_map. repeat rewrite bind_ret_r. repeat rewrite bind_ret_l.  gfinal.
      right. pfold; constructor; auto.
    + cbn. repeat rewrite bind_map. repeat rewrite bind_trigger. gstep. constructor. intros.
      gstep. constructor. gfinal. left. pclearbot. eapply CIH; eauto.
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
  - rewrite bind_ret_l. rewrite tau_euttge. rewrite unfold_iter_ktree. eapply IHHt; eauto.
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
    @throw_prefix Err R E (Vis (inl1 (Throw _ e) ) k) ≅ Ret (inr e).
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
  intros E Err R kcatch. ginit. gcofix CIH. intros.
  destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. rewrite try_catch_ret. gfinal. right.
    pfold; constructor; auto.
  - rewrite Heq. rewrite throw_prefix_tau. rewrite try_catch_tau. gstep. constructor.
    gfinal; left; auto.
  - destruct e.
   + destruct e. rewrite Heq. rewrite throw_prefix_exc. rewrite try_catch_ret. gfinal.
     right. pfold; constructor; auto.
   + rewrite Heq. rewrite throw_prefix_ev. rewrite try_catch_ev. gstep.
     constructor. intros. red. rewrite try_catch_tau. repeat rewrite tau_euttge.
     gfinal. left. auto.
Qed.

Lemma throw_prefix_bind_decomp : forall E Err R (t : itree (exceptE Err +' E) R ),
    t ≈ ITree.bind (throw_prefix t) (fun r => 
                                    match r with 
                                    | inr e => v <- trigger (inl1 (Throw _ e));; match v : void with end
                                    | inl a => Ret a
                                    end).
Proof.
  intros E Err R. ginit. gcofix CIH. intros.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. rewrite bind_ret_l. gfinal. right. pfold; constructor; auto.
  - rewrite Heq. rewrite throw_prefix_tau. rewrite bind_tau. gstep. constructor.
    gfinal; left. auto.
  - destruct e.
    + rewrite Heq. destruct e. rewrite throw_prefix_exc. rewrite bind_ret_l. cbn. rewrite bind_trigger.
      gstep. constructor. intros [].
    + rewrite Heq. rewrite throw_prefix_ev. rewrite bind_vis. gstep. constructor.
      intros. red. rewrite tau_euttge. gfinal; left; auto.
Qed.

Lemma try_catch_to_throw_prefix : forall E Err R (ttry : itree (exceptE Err +' E) R  ) (kcatch : Err -> itree (exceptE Err +' E) R),
    try_catch ttry kcatch ≈ ITree.bind (throw_prefix ttry) (fun r =>
                                                            match r with
                                                            | inr e => kcatch e
                                                            | inl a => Ret a
                                                            end).
Proof.
  intros. revert ttry. ginit. gcofix CIH.
  intros. destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite try_catch_ret. rewrite throw_prefix_ret. rewrite bind_ret_l. gfinal.
    right. pfold; constructor; auto.
  - rewrite Heq. rewrite try_catch_tau. rewrite throw_prefix_tau. rewrite bind_tau.
    gstep. constructor. gfinal; left; auto.
  - destruct e.
    + destruct e. rewrite Heq. rewrite try_catch_exc. rewrite throw_prefix_exc. rewrite bind_ret_l.
      gfinal; right. apply paco2_mon with (r := bot2); intros; try contradiction.
      enough (kcatch e ≈ kcatch e); auto. reflexivity.
    + rewrite Heq. rewrite try_catch_ev. rewrite throw_prefix_ev. rewrite bind_vis. setoid_rewrite tau_euttge.
      gstep. constructor. intros. gfinal. left. auto.
Qed.

Lemma throw_prefix_of_try_catch :  forall E Err R (ttry : itree (exceptE Err +' E) R  ) (kcatch : Err -> itree (exceptE Err +' E) R),
    throw_prefix (try_catch ttry kcatch) ≈ try_catch (ITree.bind ttry (fun r => Ret (inl r)) ) (fun e => throw_prefix (kcatch e) ).
Proof.
  intros. revert ttry. ginit. gcofix CIH.
  intros. destruct (observe ttry) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite bind_ret_l. repeat rewrite try_catch_ret. rewrite throw_prefix_ret.
    gfinal; right; pfold; constructor; auto.
  - rewrite Heq. rewrite bind_tau. repeat rewrite try_catch_tau. rewrite throw_prefix_tau.
    gstep. constructor. gfinal. left. auto.
  - destruct e.
    + destruct e. rewrite Heq. rewrite bind_vis. repeat rewrite try_catch_exc.
      gfinal; right. apply paco2_mon with (r := bot2); intros; try contradiction.
      enough (throw_prefix (kcatch e) ≈ throw_prefix (kcatch e)); auto; try reflexivity.
    + rewrite Heq. rewrite bind_vis. repeat rewrite try_catch_ev. rewrite throw_prefix_ev.
      setoid_rewrite throw_prefix_tau.
      repeat setoid_rewrite tau_euttge.
      gstep. constructor. intros. gfinal. left. auto.
Qed.

Lemma throw_prefix_bind : forall E Err R S (t : itree (exceptE Err +' E) R ) (k : R -> itree (exceptE Err +' E) S),
    throw_prefix (ITree.bind t k) ≅ ITree.bind (throw_prefix t) 
                 (fun r : R + Err => match r with 
                                  | inl r' => throw_prefix (k r') 
                                  | inr e => Ret (inr e) end ).
Proof.
  intros. revert t. ginit. gcofix CIH.
  intros. destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite throw_prefix_ret. repeat rewrite bind_ret_l.
    gfinal; right. apply paco2_mon with (r := bot2); intros; try contradiction.
    enough (throw_prefix (k r0) ≅ throw_prefix (k r0)); auto; try reflexivity.
  - rewrite Heq. rewrite throw_prefix_tau. repeat rewrite bind_tau. rewrite throw_prefix_tau.
    gstep. constructor. gfinal; eauto.
  - destruct e.
    + destruct e. rewrite Heq. rewrite throw_prefix_exc. rewrite bind_vis. rewrite throw_prefix_exc.
      rewrite bind_ret_l. gstep; constructor; auto.
    + rewrite Heq. rewrite throw_prefix_ev. repeat rewrite bind_vis. rewrite throw_prefix_ev.
      gstep. constructor. intros. red. rewrite bind_tau. gstep. constructor.
      gfinal. eauto.
Qed.

Lemma throw_prefix_iter : forall E Err A B (body : A -> itree (exceptE Err +' E) (A + B)  ) (init : A),
    throw_prefix (ITree.iter body init) ≅ ITree.iter (R := B + Err)  (fun a : A => r <- throw_prefix (body a);; 
                                                             match (r : (A + B) + Err) with
                                                             | inl (inl a) => Ret (inl a)
                                                             | inl (inr b) => Ret (inr (inl b))
                                                             | inr e => Ret (inr (inr e)) end)  init.
Proof.
  intros E Err A B. ginit. gcofix CIH. intros.
  setoid_rewrite unfold_iter_ktree at 2 3.
  destruct (observe (body init) ) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq at 1. rewrite bind_ret_l. setoid_rewrite bind_bind. 
    rewrite Heq at 1. rewrite throw_prefix_ret. rewrite bind_ret_l.
    destruct r0; rewrite bind_ret_l.
    + rewrite throw_prefix_tau. gstep. constructor. gfinal. eauto.
    + rewrite throw_prefix_ret. gfinal. right. pfold; constructor; auto.
  - rewrite Heq at 1. setoid_rewrite bind_bind. rewrite Heq at 1.
    rewrite throw_prefix_tau. repeat rewrite bind_tau. rewrite throw_prefix_tau.
    gstep. constructor. setoid_rewrite throw_prefix_bind at 1. guclo eqit_clo_bind.
    econstructor; try reflexivity. intros; subst. destruct u2 as [ [ a | b] | e ].
    + rewrite bind_ret_l. rewrite throw_prefix_tau. gstep. constructor. gfinal. eauto.
    + rewrite bind_ret_l. rewrite throw_prefix_ret. gstep; constructor; auto.
    + rewrite bind_ret_l. gstep; constructor; auto.
  - rewrite Heq at 1. setoid_rewrite bind_bind. rewrite Heq at 1.
    destruct e.
    + destruct e. rewrite bind_vis. rewrite throw_prefix_exc.
      setoid_rewrite throw_prefix_exc. repeat rewrite bind_ret_l.
      gstep; constructor; auto.
    + rewrite bind_vis. rewrite throw_prefix_ev. setoid_rewrite throw_prefix_ev.
      rewrite bind_vis. setoid_rewrite bind_tau. gstep; constructor. intros. red.
      gstep; constructor. rewrite throw_prefix_bind.
      guclo eqit_clo_bind. econstructor; try reflexivity. intros; subst.
      destruct u2 as [ [ a | b] | e' ].
      * rewrite bind_ret_l. rewrite throw_prefix_tau. gstep; constructor.
        gfinal. eauto.
      * rewrite bind_ret_l. rewrite throw_prefix_ret.
        gstep; constructor; auto.
      * rewrite bind_ret_l. gstep; constructor; auto.
Qed.
