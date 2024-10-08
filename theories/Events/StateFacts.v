(** * Theorems about State effects *)

(* begin hide *)
From Coq Require Import Program.Tactics Morphisms.

From Paco Require Import paco.

From ExtLib Require Import Data.Monads.StateMonad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.HeterogeneousRelations
     Basics.Monad
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Interp.Interp
     Interp.InterpFacts
     Interp.RecursionFacts
     Events.State.

Import ITreeNotations.

Local Open Scope itree_scope.

(* end hide *)

Definition _interp_state {E F S R}
           (f : E ~> stateT S (itree F)) (ot : itreeF E R _)
  : stateT S (itree F) R := mkStateT (fun s =>
  match ot with
  | RetF r => Ret (r, s)
  | TauF t => Tau (runStateT (interp_state f t) s)
  | VisF e k => runStateT (f _ e) s >>= (fun xs => Tau (runStateT (interp_state f (k (fst xs))) (snd xs)))
  end).

Lemma unfold_interp_state {E F S R} (h : E ~> stateT S (itree F))
      (t : itree E R) s :
    eq_itree eq
      (runStateT (interp_state h t) s)
      (runStateT (_interp_state h (observe t)) s).
Proof.
  unfold interp_state, interp, Basics.iter, MonadIter_stateT, Basics.iter, MonadIter_itree; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite 2 bind_ret_l.
    reflexivity.
  - rewrite 2 bind_bind; cbn.
    apply eqit_bind; [reflexivity|].
    intros [].
    rewrite 2 bind_ret_l.
    reflexivity.
Qed.

(*
Definition stateT_rel {S1 S2 M1 M2 R1 R2}
    (RS : S1 -> S2 -> Prop)
    (RM : M1 (R1 * S1)%type -> M2 (R2 * S2)%type -> Prop)
  : (stateT S1 M1 R1) -> (stateT S2 M2 R2) -> Prop :=
  fun t1 t2 => forall s1 s2, RS s1 s2 -> RM (runStateT t1 s1) (runStateT t2 s2).
*)
Definition eq_stateT {S M R}
    (RM : M (R * S)%type -> M (R * S)%type -> Prop)
  : stateT S M R -> stateT S M R -> Prop :=
  fun t1 t2 => forall s, RM (runStateT t1 s) (runStateT t2 s).

#[global]
Instance eq_stateT_runStateT {S M R} 
    (RM : M (R * S)%type -> M (R * S)%type -> Prop) :
  Proper (eq_stateT RM ==> eq ==> RM) (@runStateT S _ R).
Proof.
  unfold Proper, respectful.
  intros x y Heq_stateT sx sy Heq.
  rewrite Heq.
  apply Heq_stateT.
Qed.

#[global]
Instance eq_itree_interp_state {E F S R} (h : E ~> stateT S (itree F)) :
  Proper (eq_itree eq ==> (eq_stateT (eq_itree eq)))
         (@interp_state _ _ _ _ _ _ h R).
Proof.
  revert_until R.
  ginit. pcofix CIH. intros h x y H0 s.
  rewrite !unfold_interp_state.
  punfold H0; repeat red in H0.
  destruct H0; subst; pclearbot; try discriminate; cbn.
  - gstep; constructor; auto.
  - gstep; constructor; auto with paco.
  - guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros [] _ []. gstep; constructor; auto with paco itree.
Qed.

Lemma interp_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> stateT S (itree F) T)
      (s : S) (r : R) :
  (runStateT (interp_state f (Ret r)) s) ≅ (Ret (r, s)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp_state_vis {E F : Type -> Type} {S T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> stateT S (itree F)) (s : S)
  : runStateT (interp_state h (Vis e k)) s
  ≅ runStateT (h T e) s >>= fun xs => Tau (runStateT (interp_state h (k (fst xs))) (snd xs)).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_tau {E F : Type -> Type} S {T : Type}
      (t : itree E T) (h : E ~> stateT S (itree F)) (s : S)
  : runStateT (interp_state h (Tau t)) s ≅ Tau (runStateT (interp_state h t) s).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_trigger_eqit {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> stateT S (itree F)) (s : S)
  : (runStateT (interp_state f (ITree.trigger e)) s) ≅ (runStateT (f _ e) s >>= fun x => Tau (Ret x)).
Proof.
  unfold ITree.trigger. rewrite interp_state_vis.
  eapply eqit_bind; try reflexivity.
  intros []. rewrite interp_state_ret. reflexivity.
Qed.

Lemma interp_state_trigger {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> stateT S (itree F)) (s : S)
  : runStateT (interp_state f (ITree.trigger e)) s ≈ runStateT (f _ e) s.
Proof.
  unfold ITree.trigger. rewrite interp_state_vis.
  match goal with
    |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
  end.
  eapply eqit_bind; try reflexivity.
  intros []; rewrite interp_state_ret,tau_eutt.
  reflexivity.
Qed.

Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> stateT S (itree F) T)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (runStateT (interp_state f (t >>= k)) s)
    ≅
  (runStateT (interp_state f t) s >>= fun ts => runStateT (interp_state f (k (fst ts))) (snd ts)).
Proof.
  revert t k s.
  ginit. pcofix CIH.
  intros t k s.
  rewrite unfold_bind.
  rewrite (unfold_interp_state f t).
  destruct (observe t).
  - cbn. rewrite bind_ret_l. cbn.
    apply reflexivity.
  - rewrite interp_state_tau. cbn. rewrite bind_tau.
    gstep. econstructor. gbase. apply CIH.
  - rewrite interp_state_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? [].
      rewrite bind_tau.
      gstep; constructor.
      ITree.fold_subst.
      auto with paco.
Qed.

#[global]
Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> stateT S (itree F)) R RR :
  Proper (eutt RR ==> eq_stateT (eutt (prod_rel RR eq))) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until RR.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; pclearbot; cbn.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.

#[global]
Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type}
         (h : E ~> stateT S (itree F)) R :
  Proper (eutt eq ==> eq_stateT (eutt eq)) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; cbn; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.


Lemma eutt_interp_state_aloop {E F S I I' A A'}
      (RA : A -> A' -> Prop) (RI : I -> I' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> stateT S (itree F))
      (t1 : I -> itree E (I + A))
      (t2 : I' -> itree E (I' + A')):
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (prod_rel (sum_rel RI RA) RS)
          (runStateT (interp_state h (t1 i)) s1)
          (runStateT (interp_state h (t2 i')) s2)) ->
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (fun a b => RA (fst a) (fst b) /\ RS (snd a) (snd b))
          (runStateT (interp_state h (ITree.iter t1 i)) s1)
          (runStateT (interp_state h (ITree.iter t2 i')) s2)).
Proof.
  intro Ht.
  einit. ecofix CIH. intros.
  rewrite 2 unfold_iter.
  rewrite 2 interp_state_bind.
  ebind; econstructor.
  - eapply Ht; auto.
  - intros [i1' s1'] [i2' s2'] [[] ?].
    + rewrite 2 interp_state_tau. cbn. auto with paco.
    + rewrite 2 interp_state_ret. cbn. auto with paco.
Qed.

Lemma eutt_interp_state_iter {E F S A A' B B'}
      (RA : A -> A' -> Prop) (RB : B -> B' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> stateT S (itree F))
      (t1 : A -> itree E (A + B))
      (t2 : A' -> itree E (A' + B')) :
  (forall ca ca' s1 s2, RS s1 s2 ->
                        RA ca ca' ->
     eutt (prod_rel (sum_rel RA RB) RS)
          (runStateT (interp_state h (t1 ca)) s1)
          (runStateT (interp_state h (t2 ca')) s2)) ->
  (forall a a' s1 s2, RS s1 s2 -> RA a a' ->
     eutt (fun a b => RB (fst a) (fst b) /\ RS (snd a) (snd b))
          (runStateT (interp_state h (iter (C := ktree _) t1 a)) s1)
          (runStateT (interp_state h (iter (C := ktree _) t2 a')) s2)).
Proof.
  apply eutt_interp_state_aloop.
Qed.

Lemma eutt_eq_interp_state_iter {E F S} (f: E ~> stateT S (itree F)) {I A}
    (t : I -> itree E (I + A)):
  forall i s, runStateT (interp_state f (ITree.iter t i)) s ≈
    runStateT (Basics.iter (fun i => interp_state f (t i)) i) s.
Proof.
  unfold Basics.iter, MonadIter_stateT, Basics.iter, MonadIter_itree in *. cbn.
  ginit. gcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto. reflexivity.
  intros [[] s'] _ []; cbn.
  - rewrite interp_state_tau.
    gstep; constructor.
    auto with paco.
  - rewrite interp_state_ret; apply reflexivity.
Qed.

Lemma eutt_interp_state_loop {E F S A B C} (RS : S -> S -> Prop)
      (h : E ~> stateT S (itree F))
      (t1 t2 : C + A -> itree E (C + B)) :
  (forall ca s1 s2, RS s1 s2 ->
     eutt (fun a b => fst a = fst b /\ RS (snd a) (snd b))
          (runStateT (interp_state h (t1 ca)) s1)
          (runStateT (interp_state h (t2 ca)) s2)) ->
  (forall a s1 s2, RS s1 s2 ->
     eutt (fun a b => fst a = fst b /\ RS (snd a) (snd b))
          (runStateT (interp_state h (loop (C := ktree E) t1 a)) s1)
          (runStateT (interp_state h (loop (C := ktree E) t2 a)) s2)).
Proof.
  intros.
  unfold loop, bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum, id_, Id_Kleisli, cat, Cat_Kleisli, inr_, Inr_Kleisli, inl_, Inl_Kleisli, lift_ktree_; cbn.
  rewrite 2 bind_ret_l.
  eapply (eutt_interp_state_iter eq eq); auto; intros.
  rewrite 2 interp_state_bind.
  subst.
  eapply eutt_clo_bind; eauto.
  intros.
  cbn in H2; destruct (fst u1); rewrite <- (proj1 H2).
  - rewrite bind_ret_l, 2 interp_state_ret.
    pstep.
    constructor.
    split; cbn; auto using (proj2 H2).
  - rewrite bind_ret_l, 2 interp_state_ret. pstep. constructor.
    split; cbn; auto using (proj2 H2).
Qed.

Lemma interp_state_iter {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
      (t' : I -> stateT S (itree F) (I + A))
      (EQ_t : forall i, eq_stateT (eq_itree eq) (State.interp_state f (t i)) (t' i))
  : forall i, eq_stateT (eq_itree eq) (State.interp_state f (ITree.iter t i))
                        (Basics.iter t' i).
Proof.
  unfold Basics.iter, MonadIter_stateT, Basics.iter, MonadIter_itree in *.
  ginit. pcofix CIH; intros i s. cbn.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  - apply EQ_t.
  - intros [[] s'] _ []; cbn.
    + rewrite interp_state_tau.
      gstep; constructor.
      auto with paco.
    + rewrite interp_state_ret; apply reflexivity.
Qed.

Lemma interp_state_iter' {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
  : forall i, eq_stateT (eq_itree eq) (State.interp_state f (ITree.iter t i))
                        (Basics.iter (fun i => State.interp_state f (t i)) i).
Proof.
  eapply interp_state_iter.
  intros i s.
  reflexivity.
Qed.

Lemma interp_state_iter'_eutt {E F S} (f: E ~> stateT S (itree F)) {I A}
    (t : I -> itree E (I + A))
    (t': I -> stateT S (itree F) (I + A))
    (Heq: forall i s, runStateT (interp_state f (t i)) s ≈ runStateT (t' i) s):
  forall i s, runStateT (interp_state f (ITree.iter t i)) s ≈ runStateT (Basics.iter t' i) s.
Proof.
  unfold Basics.iter, MonadIter_stateT, Basics.iter, MonadIter_itree in *; cbn.
  ginit. gcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  - apply Heq.
  - intros [[] s'] _ []; cbn.
    + rewrite interp_state_tau.
      gstep; constructor.
      auto with paco.
    + rewrite interp_state_ret; apply reflexivity.
Qed.
