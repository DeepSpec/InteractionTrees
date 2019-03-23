(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ExtLib Require Import
     Structures.Monoid.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Core.KTree
     Core.KTreeFacts
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.MorphismsFacts
     Interp.RecursionFacts
     Effects.State.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.
(* end hide *)

(** * [interp_state] *)

Import Monads.

Definition _interp_state {E F S}
           (f : E ~> stateT S (itree F)) R (ot : itreeF E R _)
  : stateT S (itree F) R := fun s =>
  match ot with
  | RetF r => Ret (s, r)
  | TauF t => Tau (interp_state f _ t s)
  | VisF e k => Tau (f _ e s >>= (fun sx => interp_state f _ (k (snd sx)) (fst sx)))
  end.

Lemma unfold_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) t s :
    eq_itree eq
      (interp_state h _ t s)
      (_interp_state h R (observe t) s).
Proof.
  unfold interp_state, interp, aloop, ALoop_stateT0, aloop, ALoop_itree.
  rewrite unfold_aloop'.
  destruct observe; cbn.
  - reflexivity.
  - rewrite bind_ret_.
    reflexivity.
  - rewrite map_bind. eapply eq_itree_Tau.
    eapply eq_itree_bind.
    + reflexivity.
    + intros [] _ []; reflexivity.
Qed.

Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq)
         (interp_state h R).
Proof.
  revert_until R.
  wcofix CIH. intros h x y H0 x2 y0 H1.
  rewrite !unfold_interp_state.
  unfold _interp_state.
  wunfold H0; repeat red in H0.
  genobs x ox; destruct ox; simpobs; dependent destruction H0; simpobs; subst.
  - wstep. constructor. eauto.
  - wstep. constructor. eauto with paco.
  - wstep. constructor. wclo eq_itree_clo_bind. econstructor.
    + reflexivity.
    + intros [] _ []. auto with paco.
Qed.

Lemma interp_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp_state f _ (Ret r) s) ≅ (Ret (s, r)).
Proof.
  rewrite itree_eta. reflexivity.
Qed.

Lemma interp_state_vis {E F:Type -> Type} {S T U : Type} (s:S) e k
      (h : E ~> Monads.stateT S (itree F)) :
    interp_state h U (Vis e k) s
  ≅ Tau (h T e s >>= fun sx => interp_state h _ (k (snd sx)) (fst sx)).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_tau {E F:Type -> Type} S {T : Type} (t:itree E T) (s:S)
      (h : E ~> Monads.stateT S (itree F)) :
    interp_state h _ (Tau t) s ≅ Tau (interp_state h _ t s).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_lift {E F : Type -> Type} {R S : Type}
      (f : E ~> Monads.stateT S (itree F))
      (s : S) (e : E R) :
  (interp_state f _ (ITree.lift e) s) ≅ Tau (f _ e s >>= fun i => Ret i).
Proof.
  unfold ITree.lift. rewrite interp_state_vis.
  apply eq_itree_Tau.
  eapply eq_itree_bind.
  - reflexivity.
  - intros [] _ []; rewrite interp_state_ret. reflexivity.
Qed.

Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_state f _ (t >>= k) s)
    ≅
  (interp_state f _ t s >>= fun st => interp_state f _ (k (snd st)) (fst st)).
Proof.
  revert A t k s.
  wcofix CIH.
  intros A t k s.
  rewrite unfold_bind, (unfold_interp_state f t).
  destruct (observe t).
  (* TODO: performance issues with [ret|tau|vis_bind] here too. *)
  - cbn. rewrite !bind_ret. simpl.
    apply reflexivity.
  - cbn. rewrite !bind_tau, interp_state_tau.
    wstep. econstructor. wbase. apply CIH.
  - cbn. rewrite interp_state_vis, bind_tau, bind_bind.
    wstep. constructor.
    wclo eq_itree_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. specialize (CIH _ (k0 (snd u2)) k (fst u2)).
      auto with paco.
Qed.

Instance eutt_interp_state {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  wcofix CIH. wstep. wcofix CIH'. intros.

  rewrite !unfold_interp_state. do 2 wunfold H0.
  induction H0; intros; subst; simpl.
  - wstep. constructor. eauto.
  - wstep. constructor.
    wclo eutt0_clo_bind; econstructor; [reflexivity|].
    intros; subst.
    wbase. eapply CIH'. edestruct EUTTK; eauto with paco.
  - wstep. econstructor. eauto 9 with paco.
  - apply eutt0_tau_left.
    rewrite unfold_interp_state; auto.
  - apply eutt0_tau_right.
    rewrite unfold_interp_state; auto.
Qed.

Lemma interp_state_loop {E F S A B C} (RS : S -> S -> Prop)
      (h : E ~> Monads.stateT S (itree F))
      (t1 t2 : C + A -> itree E (C + B)) :
  (forall ca s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h (C+B) (t1 ca) s1)
          (interp_state h (C+B) (t2 ca) s2)) ->
  (forall ca s1 s2, RS s1 s2 ->
     eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b)
          (interp_state h B (loop_ t1 ca) s1)
          (interp_state h B (loop_ t2 ca) s2)).
Proof.
  wcofix CIH. wstep. wcofix CIH'. intros.

  rewrite (itree_eta (loop_ t1 ca)), (itree_eta (loop_ t2 ca)), !unfold_loop''.
  unfold loop_once. rewrite <- !itree_eta, !interp_state_bind.
  wclo eutt0_clo_bind. econstructor; eauto.
  intros. destruct RELv. rewrite H2. destruct (snd v2).
  - rewrite !interp_state_tau.
    wstep. econstructor. eauto with paco.
  - rewrite !interp_state_ret. wstep. econstructor. eauto.
Qed.
