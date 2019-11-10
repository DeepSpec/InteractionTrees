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
  rewrite interp_trigger.
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
  rewrite interp_trigger.
  reflexivity.
Qed.

Instance CaseInr_Handler : CaseInr Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_trigger.
  reflexivity.
Qed.

Instance CaseUniversal_Handler : CaseUniversal Handler sum1.
Proof.
  cbv; intros.
  destruct (_ : sum1 _ _ _).
  - rewrite <- H, interp_trigger. reflexivity.
  - rewrite <- H0, interp_trigger. reflexivity.
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
  pattern f.
  match goal with
  | [ |- ?G ?f ] =>
    enough (HHH : G (fun T e => Tau (f T e))); cbn in *
  end.
  { etransitivity; [etransitivity; [|eapply HHH] |]; clear.
    - symmetry. apply euttge_sub_eutt, euttge_interp.
      + reflexivity.
      + apply euttge_interp_mrec; repeat intro; apply tau_eutt.
    - apply euttge_sub_eutt, euttge_interp_mrec.
      + intros ? ?. apply euttge_interp.
        * reflexivity.
        * apply tau_eutt.
      + rewrite tau_eutt. reflexivity.
  }
  match goal with
  | [ |- _ _ (_ _ _ (_ ?h0 _ _)) ] =>
    remember h0 as h eqn:EQh
    (* h is pretty big and duplicating it slows down the display of the goal,
       so we try to rewrite with EQh only when necessary. *)
  end.
  remember (Tau (f T a0)) as t eqn:tmp_t. clear tmp_t.
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
    rewrite interp_vis.
    destruct e; cbn.
    + rewrite interp_tau.
      rewrite 2 interp_mrec_bind, interp_bind.
      subst h; cbn.
      rewrite interp_trigger.
      rewrite unfold_interp_mrec; cbn.
      rewrite interp_mrec_trigger; cbn.
      unfold Recursion.mrec.
      rewrite !interp_tau.
      rewrite (unfold_interp_mrec _ _ (Tau _)); cbn.
      rewrite !bind_tau.
      etau. rewrite tau_eutt, <- interp_bind, <- 2 interp_mrec_bind.
      setoid_rewrite (tau_eutt (interp _ _)).
      rewrite <- interp_bind.
      auto with paco.
    + rewrite interp_vis.
      rewrite interp_mrec_bind.
      subst h; cbn.
      Local Transparent eutt.
      ebind. apply (pbc_intro_h _ _ _ _ _ eq).
      { rewrite interp_mrec_as_interp, interp_interp.
        rewrite <- interp_id_h at 1.
        eapply eutt_interp; try reflexivity.
        intros ? ?.
        rewrite interp_trigger; cbn.
        reflexivity. }
      intros ? _ [].
      rewrite (unfold_interp_mrec _ _ (Tau _)); cbn.
      etau.
      rewrite tau_eutt.
      auto with paco.
Qed.

Section DinatSimulation.

Context {A B C : Type -> Type}.
Context (f0 : A ~> itree (B +' C)) (g0 : B ~> itree (A +' C)).
Context {R : Type}.

Context (f := fun T e => Tau (f0 T e)) (g := fun T e => Tau (g0 T e)).

Inductive interleaved
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

Let hg := @case_ _ Handler _ _ _ _ _ g inr_.
Let hf := @case_ _ Handler _ _ _ _ _ f inr_.

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
    + rewrite interp_vis, bind_vis.
      rewrite bind_bind.
      rewrite (unfold_interp_mrec _ _ (Vis _ _)); cbn.
      destruct e; cbn. setoid_rewrite (tau_eutt (interp _ _)).
      * unfold cat at 3, Cat_Handler at 3, Handler.cat.
        change (g X b) with (Tau (g0 X b)).
        rewrite bind_tau, unfold_interp_mrec; cbn.
        etau. rewrite tau_eutt. ebase.
      * unfold inr_ at 3, Inr_sum1_Handler at 3, Handler.inr_, Handler.htrigger.
        rewrite bind_trigger.
        rewrite unfold_interp_mrec; cbn.
        evis; intros; etau. rewrite tau_eutt. ebase.
  - rewrite (itree_eta t); destruct (observe t).
    + rewrite interp_ret, 2 bind_ret. auto.
    + rewrite interp_tau, 2 bind_tau, 2 unfold_interp_mrec; cbn.
      estep.
    + rewrite interp_vis, bind_vis.
      rewrite bind_bind.
      rewrite (unfold_interp_mrec _ _ (Vis _ _)); cbn.
      destruct e; cbn. setoid_rewrite (tau_eutt (interp _ _)).
      * unfold cat at 2, Cat_Handler at 2, Handler.cat.
        change (f X a) with (Tau (f0 X a)).
        rewrite !bind_tau, (unfold_interp_mrec _ _ (Tau _)); cbn.
        etau. rewrite tau_eutt. ebase.
      * unfold inr_ at 4, Inr_sum1_Handler at 4, Handler.inr_, Handler.htrigger.
        rewrite bind_trigger.
        rewrite unfold_interp_mrec; cbn.
        evis; intros; etau. rewrite tau_eutt. ebase.
Qed.

End DinatSimulation.

Local Opaque eutt.
Local Transparent ITree.trigger.

Instance IterDinatural_Handler : IterDinatural Handler sum1.
Proof.
  cbv; intros a b c f0 g0 T a0.
  pose (f := fun T e => Tau (f0 T e)). pose (g := fun T e => Tau (g0 T e)).
  enough (
      Recursion.interp_mrec (cat f (case_ g inr_))
                            (interp (case_ g inr_) (f _ a0))
    ≈ interp (mrecursive (cat g (case_ f inr_))) (f _ a0)).
  { cbv in H. etransitivity; [etransitivity; [|apply H]|]; clear H.
    - symmetry. apply euttge_sub_eutt, euttge_interp_mrec.
      1: intros ? ?.
      1,2: rewrite tau_eutt; apply euttge_interp; try reflexivity.
      1,2: intros ? []; [apply tau_eutt| reflexivity].
    - apply euttge_sub_eutt, euttge_interp; [ | apply tau_eutt].
      intros ? []; try reflexivity.
      rewrite tau_eutt. apply euttge_interp_mrec.
      intros ? ?.
      rewrite tau_eutt.
      all: apply euttge_interp; try reflexivity.
      all: intros ? []; [apply tau_eutt | reflexivity].
  }
  rewrite <- interp_mrec_as_interp.

  rewrite <- (bind_ret2 (interp _ _)).
  rewrite <- (bind_ret2 (f _ a0)) at 2.

  apply interleaved_mrec.
  do 2 constructor.
Qed.

Local Opaque ITree.trigger.

Import Recursion.

Instance IterCodiagonal_Handler : IterCodiagonal Handler sum1.
Proof.
  cbv; intros a b f0 T x.
  remember (f0 T x) as t eqn:EQt; clear.
  pose (f := fun T e => Tau (f0 T e)).
  enough (interp_mrec (fun _ d => interp_mrec f (f _ d))
                      (interp_mrec f t)
          ≈ interp_mrec (fun _ e => interp (fun _ ab =>
                                              match ab with
                                              | inl1 x => ITree.trigger (inl1 x)
                                              | inr1 y => ITree.trigger y
                                              end) (f _ e))
                        (interp (fun _ ab =>
                                   match ab with
                                   | inl1 x => ITree.trigger (inl1 x)
                                   | inr1 y => ITree.trigger y
                                   end) t)).
  { subst f. etransitivity; [etransitivity; [| apply H] |]; clear H.
    - symmetry. apply euttge_sub_eutt, euttge_interp_mrec.
      + intros ? ?. apply euttge_interp_mrec; try apply tau_eutt.
        intros ? ?. apply tau_eutt.
      + apply euttge_interp_mrec; repeat intro; reflexivity + rewrite tau_eutt.
        reflexivity.
    - apply euttge_sub_eutt, euttge_interp_mrec; repeat intro;
        apply euttge_interp; try reflexivity.
      apply tau_eutt.
  }
  revert t. einit; ecofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t); cbn.
  all: rewrite (unfold_interp_mrec _ _ (go _)), unfold_interp; cbn.
  1,2: rewrite unfold_interp_mrec; cbn.
  1,2: rewrite (unfold_interp_mrec _ _ (go _)); estep.
  destruct e.
  - rewrite (interp_mrec_bind _ (ITree.trigger _)).
    rewrite interp_mrec_trigger; cbn.
    unfold Recursion.mrec.
    remember (f X a0) as fxa eqn:Hfxa; unfold f in Hfxa; subst fxa.
    rewrite interp_tau, unfold_interp_mrec; cbn.
    rewrite (unfold_interp_mrec _ _ (Tau _)); cbn.
    rewrite !bind_tau.
    etau.
    rewrite tau_eutt. setoid_rewrite tau_eutt.
    rewrite <- interp_mrec_bind, <- interp_bind.
    auto with paco.
  - rewrite bind_trigger.
    setoid_rewrite tau_eutt.
    rewrite 2 unfold_interp_mrec; cbn.
    destruct s; estep.
    rewrite <- interp_mrec_bind, <- interp_bind.
    auto with paco.
Qed.

Global Instance Iterative_Handler : Iterative Handler sum1.
Proof.
  split; typeclasses eauto.
Qed.

End HandlerCategory.
