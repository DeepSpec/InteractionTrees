(** * Theorems about State effects *)

(* begin hide *)
From Coq Require Import Program.Tactics Morphisms.

From Paco Require Import paco.

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

Import Monads.
(* end hide *)

Definition _interp_state {E F S R}
           (f : E ~> stateT S (itree F)) (ot : itreeF E R _)
  : stateT S (itree F) R := fun s =>
  match ot with
  | RetF r => Ret (s, r)
  | TauF t => Tau (interp_state f t s)
  | VisF e k => f _ e s >>= (fun sx => Tau (interp_state f (k (snd sx)) (fst sx)))
  end.

Lemma unfold_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F))
      (t : itree E R) s :
    eq_itree eq
      (interp_state h t s)
      (_interp_state h (observe t) s).
Proof.
  unfold interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite 2 bind_ret_l.
    reflexivity.
  - rewrite bind_map, bind_bind; cbn. setoid_rewrite bind_ret_l.
    apply eqit_bind; reflexivity.
Qed.

#[global]
Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
         (@interp_state _ _ _ _ _ _ h R).
Proof.
  revert_until R.
  ginit. pcofix CIH. intros h x y H0 x2 _ [].
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
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp_state f (Ret r) s) ≅ (Ret (s, r)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp_state_vis {E F : Type -> Type} {S T U : Type}
      (e : E T) (k : T -> itree E U) (h : E ~> Monads.stateT S (itree F)) (s : S)
  : interp_state h (Vis e k) s
  ≅ h T e s >>= fun sx => Tau (interp_state h (k (snd sx)) (fst sx)).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_tau {E F : Type -> Type} S {T : Type}
      (t : itree E T) (h : E ~> Monads.stateT S (itree F)) (s : S)
  : interp_state h (Tau t) s ≅ Tau (interp_state h t s).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_trigger_eqit {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> Monads.stateT S (itree F)) (s : S)
  : (interp_state f (ITree.trigger e) s) ≅ (f _ e s >>= fun x => Tau (Ret x)).
Proof.
  unfold ITree.trigger. rewrite interp_state_vis.
  eapply eqit_bind; try reflexivity.
  intros []. rewrite interp_state_ret. reflexivity.
Qed.

Lemma interp_state_trigger {E F : Type -> Type} {R S : Type}
      (e : E R) (f : E ~> Monads.stateT S (itree F)) (s : S)
  : interp_state f (ITree.trigger e) s ≈ f _ e s.
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
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_state f (t >>= k) s)
    ≅
  (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
Proof.
  revert t k s.
  ginit. pcofix CIH.
  intros t k s.
  rewrite unfold_bind.
  rewrite (unfold_interp_state f t).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn.
    apply reflexivity.
  - cbn. rewrite !bind_tau, interp_state_tau.
    gstep. econstructor. gbase. apply CIH.
  - cbn. rewrite interp_state_vis, bind_bind.
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
         (h : E ~> Monads.stateT S (itree F)) R RR :
  Proper (eutt RR ==> eq ==> eutt (prod_rel eq RR)) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until RR.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
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
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
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
      (h : E ~> Monads.stateT S (itree F))
      (t1 : I -> itree E (I + A))
      (t2 : I' -> itree E (I' + A')):
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (prod_rel RS (sum_rel RI RA))
                     (interp_state h (t1 i) s1)
                     (interp_state h (t2 i') s2)) ->
  (forall i i' s1 s2, RS s1 s2 -> RI i i' ->
     eutt (fun a b => RS (fst a) (fst b) /\ RA (snd a) (snd b))
          (interp_state h (ITree.iter t1 i) s1)
          (interp_state h (ITree.iter t2 i') s2)).
Proof.
  intro Ht.
  einit. ecofix CIH. intros.
  rewrite 2 unfold_iter.
  rewrite 2 interp_state_bind.
  ebind; econstructor.
  - eapply Ht; auto.
  - intros [s1' i1'] [s2' i2'] [? []]; cbn.
    + rewrite 2 interp_state_tau. auto with paco.
    + rewrite 2 interp_state_ret. auto with paco.
Qed.

Lemma eutt_interp_state_iter {E F S A A' B B'}
      (RA : A -> A' -> Prop) (RB : B -> B' -> Prop)
      (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 : A -> itree E (A + B))
      (t2 : A' -> itree E (A' + B')) :
  (forall ca ca' s1 s2, RS s1 s2 ->
                        RA ca ca' ->
     eutt (prod_rel RS (sum_rel RA RB))
          (interp_state h (t1 ca) s1)
          (interp_state h (t2 ca') s2)) ->
  (forall a a' s1 s2, RS s1 s2 -> RA a a' ->
     eutt (fun a b => RS (fst a) (fst b) /\ RB (snd a) (snd b))
          (interp_state h (iter (C := ktree _) t1 a) s1)
          (interp_state h (iter (C := ktree _) t2 a') s2)).
Proof.
  apply eutt_interp_state_aloop.
Qed.

Lemma eutt_eq_interp_state_iter {E F S} (f: E ~> stateT S (itree F)) {I A}
    (t : I -> itree E (I + A)):
  forall i s, interp_state f (ITree.iter t i) s ≈
    Basics.iter (fun i => interp_state f (t i)) i s.
Proof.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
  ginit. gcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto. reflexivity.
  intros [s' []] _ []; cbn.
  - rewrite interp_state_tau.
    gstep; constructor.
    auto with paco.
  - rewrite interp_state_ret; apply reflexivity.
Qed.

Lemma eutt_interp_state_loop {E F S A B C} (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 t2 : C + A -> itree E (C + B)) :
  (forall ca s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h (t1 ca) s1)
          (interp_state h (t2 ca) s2)) ->
  (forall a s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h (loop (C := ktree E) t1 a) s1)
          (interp_state h (loop (C := ktree E) t2 a) s2)).
Proof.
  intros.
  unfold loop, bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum, id_, Id_Kleisli, cat, Cat_Kleisli, inr_, Inr_Kleisli, inl_, Inl_Kleisli, lift_ktree_; cbn.
  rewrite 2 bind_ret_l.
  eapply (eutt_interp_state_iter eq eq); auto; intros.
  rewrite 2 interp_state_bind.
  subst.
  eapply eutt_clo_bind; eauto.
  intros.
  cbn in H2; destruct H2 as [H21 H22].
  destruct (snd u1); rewrite <- H22.
  - rewrite bind_ret_l, 2 interp_state_ret.
    pstep.
    constructor.
    split; cbn; auto using H21.
  - rewrite bind_ret_l, 2 interp_state_ret. pstep. constructor.
    split; cbn; auto using H21.
Qed.

(* SAZ: These are probably too specialized. *)
Definition state_eq {E S X}
  : (stateT S (itree E) X) -> (stateT S (itree E) X) -> Prop :=
  fun t1 t2 => forall s, eq_itree eq (t1 s) (t2 s).

Lemma interp_state_iter {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
      (t' : I -> stateT S (itree F) (I + A))
      (EQ_t : forall i, state_eq (State.interp_state f (t i)) (t' i))
  : forall i, state_eq (State.interp_state f (ITree.iter t i))
                  (Basics.iter t' i).
Proof.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
  ginit. pcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  - apply EQ_t.
  - intros [s' []] _ []; cbn.
    + rewrite interp_state_tau.
      gstep; constructor.
      auto with paco.
    + rewrite interp_state_ret; apply reflexivity.
Qed.

Lemma interp_state_iter' {E F } S (f : E ~> stateT S (itree F)) {I A}
      (t  : I -> itree E (I + A))
  : forall i, state_eq (State.interp_state f (ITree.iter t i))
                       (Basics.iter (fun i => State.interp_state f (t i)) i).
Proof.
  eapply interp_state_iter.
  intros i.
  red. reflexivity.
Qed.

Lemma interp_state_iter'_eutt {E F S} (f: E ~> stateT S (itree F)) {I A}
    (t : I -> itree E (I + A))
    (t': I -> stateT S (itree F) (I + A))
    (Heq: forall i s, interp_state f (t i) s ≈ (t' i) s):
  forall i s, interp_state f (ITree.iter t i) s ≈ Basics.iter t' i s.
Proof.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
  ginit. gcofix CIH; intros i s.
  rewrite 2 unfold_iter; cbn.
  rewrite !bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite interp_state_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  - apply Heq.
  - intros [s' []] _ []; cbn.
    + rewrite interp_state_tau.
      gstep; constructor.
      auto with paco.
    + rewrite interp_state_ret; apply reflexivity.
Qed.
