(** * Theorems for [ITree.Interp.Handler] *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts
     Interp.InterpFacts
     Interp.RecursionFacts.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

Section HandlerCategory.

Local Opaque eutt ITree.bind' interp ITree.trigger.

Instance Proper_Cat_Handler {A B C}
  : @Proper (Handler A B -> Handler B C -> Handler A C)
            (eq2 ==> eq2 ==> eq2)
            cat.
Proof.
  cbv; intros.
  apply eutt_interp; auto.
Qed.

Instance CatIdR_Handler : CatIdR Handler.
Proof.
  cbv; intros.
  rewrite interp_trigger_h. reflexivity.
Qed.

Instance CatIdL_Handler : CatIdL Handler.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CatAssoc_Handler : CatAssoc Handler.
Proof.
  cbv; intros.
  rewrite interp_interp.
  reflexivity.
Qed.

Global Instance Category_Handler : Category Handler.
Proof.
  split; typeclasses eauto.
Qed.

Global Instance InitialObject_Handler : InitialObject Handler void1.
Proof.
  cbv; contradiction.
Qed.

Instance Proper_Case_Handler {A B C}
  : @Proper (Handler A C -> Handler B C -> Handler (A +' B) C)
            (eq2 ==> eq2 ==> eq2)
            case_.
Proof.
  cbv; intros.
  destruct (_ : sum1 _ _ _); auto.
Qed.

Instance CaseInl_Handler : CaseInl Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CaseInr_Handler : CaseInr Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CaseUniversal_Handler : CaseUniversal Handler sum1.
Proof.
  cbv; intros.
  destruct (_ : sum1 _ _ _).
  - rewrite <- H, interp_trigger, tau_eutt. reflexivity.
  - rewrite <- H0, interp_trigger, tau_eutt. reflexivity.
Qed.

Global Instance Coproduct_Handler : Coproduct Handler sum1.
Proof.
  split; typeclasses eauto.
Qed.

Local Opaque Recursion.interp_mrec.

Instance Proper_Iter_Handler {A B}
  : @Proper (Handler A (A +' B) -> Handler A B)
            (eq2 ==> eq2)
            iter.
Proof.
  repeat intro.
  apply Proper_interp_mrec; auto.
Qed.

Instance IterUnfold_Handler : IterUnfold Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_mrec_as_interp.
  reflexivity.
Qed.

Instance IterNatural_Handler : IterNatural Handler sum1.
Proof.
  cbv; intros.
  match goal with
  | [ |- _ _ (_ _ _ (_ ?h0 _ _)) ] =>
    remember h0 as h eqn:EQh
    (* h is pretty big and duplicating it slows down the display of the goal,
       so we try to rewrite with EQh only when necessary. *)
  end.
  remember (f T a0) as t eqn:tmp_t. clear tmp_t.
  revert t; einit; ecofix CIH; intros t.
  rewrite (itree_eta t).
  destruct (observe t).
  - rewrite unfold_interp_mrec; cbn.
    rewrite 2 interp_ret.
    rewrite unfold_interp_mrec.
    reflexivity.
  - rewrite unfold_interp_mrec; cbn.
    rewrite 2 interp_tau.
    rewrite (unfold_interp_mrec _ _ (Tau _)); cbn.
    estep.
  - rewrite unfold_interp_mrec; cbn.
    rewrite interp_tau.
    rewrite interp_vis.
    rewrite unfold_interp_mrec; cbn.
    destruct e.
    + estep. subst h. rewrite interp_trigger, bind_tau.
      rewrite (unfold_interp_mrec _ _ (Tau _)); cbn.
      rewrite tau_eutt.
      rewrite (interp_mrec_bind _ (ITree.trigger _)).
      rewrite (interp_mrec_as_interp _ (ITree.trigger _)).
      rewrite interp_trigger; cbn.
      rewrite tau_eutt.
      unfold Recursion.mrec.
      rewrite <- interp_mrec_bind.
      rewrite <- interp_bind.
      eauto with paco.
    + estep. rewrite interp_vis, tau_eutt.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_as_interp.
      remember (h _ (inr1 b0)) as W eqn:EW; rewrite EQh in EW; subst W.
      rewrite interp_interp.

      match goal with
      | [ |- _ _ (_ _ (_ ?f _ _)) ] =>
        remember f as hdl eqn:Ehdl
      end.
      assert (E0 : (Relation.i_pointwise (fun _ => euttge eq)) hdl (Handler.id_ _)); [ | clear Ehdl ].
      { subst hdl; rewrite EQh; clear. intros T0 a0.
        rewrite interp_trigger; cbn.
        rewrite tau_eutt.
        reflexivity.
      }
      apply euttge_interp in E0. hnf in E0.
      rewrite (E0 _ (g _ b0) (g _ b0)) by reflexivity. clear E0.
      rewrite interp_id_h.
      ebind; econstructor; try reflexivity.
      intros ? _ [].
      eauto with paco.
Qed.

Section DinatSimulation.

Context {A B C : Type -> Type}.
Context (f : A ~> itree (B +' C)) (g : B ~> itree (A +' C)).
Context {R : Type}.

Local Inductive interleaved
  : itree (A +' C) R -> itree (B +' C) R -> Prop :=
| interleaved_Ret r : interleaved (Ret r) (Ret r)
| interleaved_Left {U} (t : itree _ U) k1 k2 :
    (forall (x : U), interleaved (k1 x) (k2 x)) ->
    interleaved (interp (case_ g inr_) t >>= k1) (t >>= k2)
| interleaved_Right {U} (t : itree _ U) k1 k2 :
    (forall (x : U), interleaved (k1 x) (k2 x)) ->
    interleaved (t >>= k1) (interp (case_ f inr_) t >>= k2)
.

Hint Constructors interleaved.

Let hg := case_ g inr_.
Let hf := case_ f inr_.

Theorem interleaved_mrec : forall t1 t2,
    interleaved t1 t2 ->
    Recursion.interp_mrec (cat f (case_ g inr_)) t1
  ≈ Recursion.interp_mrec (cat g (case_ f inr_)) t2.
Proof.
  einit; ecofix CIH; intros.
  induction H0.
  - rewrite 2 unfold_interp_mrec; cbn. estep.
  - rewrite (itree_eta t); destruct (observe t).
    + rewrite interp_ret, 2 bind_ret. auto.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec; cbn.
      estep.
    + rewrite interp_vis, bind_tau, bind_vis, 2 unfold_interp_mrec; cbn.
      estep.
      rewrite bind_bind.
      destruct e; cbn.
      * cbv; eauto 6 with paco.
      * unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
        rewrite bind_trigger, unfold_interp_mrec; cbn.
        rewrite tau_eutt.
        estep.
    (* TODO: deduplicate *)
  - rewrite (itree_eta t); destruct (observe t).
    + rewrite interp_ret, 2 bind_ret. auto.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec; cbn.
      estep.
    + rewrite interp_vis, bind_tau, bind_vis, 2 unfold_interp_mrec; cbn.
      estep.
      rewrite bind_bind.
      destruct e; cbn.
      * cbv; eauto 6 with paco.
      * unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
        rewrite bind_trigger, unfold_interp_mrec; cbn.
        rewrite tau_eutt.
        estep.
Qed.

End DinatSimulation.

Local Transparent ITree.trigger.

Instance IterDinatural_Handler : IterDinatural Handler sum1.
Proof.
  cbv; intros.
  change (
      Recursion.interp_mrec (cat f (case_ g inr_))
                            (interp (case_ g inr_) (f _ a0))
    ≈ interp (mrecursive (cat g (case_ f inr_))) (f _ a0)).
  rewrite <- interp_mrec_as_interp.

  rewrite <- (bind_ret2 (interp _ _)).
  rewrite <- (bind_ret2 (f _ a0)) at 2.

  apply interleaved_mrec.
  do 2 constructor.
Qed.

Local Opaque ITree.trigger.

Instance IterCodiagonal_Handler : IterCodiagonal Handler sum1.
Proof.
  cbv; intros.
  remember (f T a0) as t eqn:EQt; clear EQt.
  revert t. einit; ecofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t);
    rewrite unfold_interp, (unfold_interp_mrec f), 2 unfold_interp_mrec; cbn.
  - reflexivity.
  - estep.
  - estep.
    rewrite interp_mrec_bind.
    rewrite (@interp_mrec_as_interp _ _ _ X).
    destruct e; rewrite interp_trigger, tau_eutt; cbn.
    + unfold Recursion.mrec.
      rewrite <- interp_mrec_bind, <- interp_bind.
      auto with paco.
    + rewrite unfold_interp_mrec; cbn.
      rewrite tau_eutt.
      destruct s; cbn.
      * unfold Recursion.mrec.
        rewrite <- 2 interp_mrec_bind.
        rewrite <- interp_bind.
        auto with paco.
      * rewrite bind_trigger.
        auto with paco.
Qed.

Global Instance Conway_Handler : Conway Handler sum1.
Proof.
  split; typeclasses eauto.
Qed.

End HandlerCategory.
