Set Universe Polymorphism.

From Coq Require Import Setoid Morphisms.

From ExtLib Require Import Structures.Monad.

(* From ITree Require Import Eq. *)

Variant Cont (R A : Type) : Type :=
| MkCont (runCont : (A -> R) -> R)
.

Arguments MkCont {R A}.

Definition runCont {R A} (f : Cont R A) : (A -> R) -> R :=
  match f with
  | MkCont f' => f'
  end.

Definition retCont {R A} (a : A) : Cont R A :=
  MkCont (fun k => k a).

Definition bindCont {R A B} (u : Cont R A) (h : A -> Cont R B) :=
  MkCont (fun k =>
    runCont u (fun a =>
    runCont (h a) k)).

Instance Monad_Cont {R} : Monad (Cont R) :=
  {| ret := @retCont R
  ; bind := @bindCont R
  |}.

Class RelMonad (M : Type -> Type) : Type :=
  { rret : forall A, A -> M A -> Prop
  ; rsubst : forall A B, (A -> M B -> Prop) -> M A -> M B -> Prop
  ; rfmap : forall A B, (A -> B -> Prop) -> M A -> M B -> Prop
  }.

Arguments rret {M _ _}.
Arguments rfmap {M _ _ _}.
Arguments rsubst {M _ _ _}.

Definition eq_rel {A B} (RL RR : A -> B -> Prop) : Prop :=
  forall a b, RL a b <-> RR a b.

Infix "⩯" := eq_rel (at level 40).

Definition catrel {A B C} (RL : A -> B -> Prop) (RR : B -> C -> Prop)
  : A -> C -> Prop :=
  fun a c => exists b, RL a b /\ RR b c.

Class RelMonadLaws (M : Type -> Type) {RM : RelMonad M} : Prop :=
  { Proper_rsubst : forall A B, Proper (eq_rel ==> eq_rel) (rsubst (A := A) (B := B))
  ; rsubst_rret : forall A,
      rsubst rret ⩯ @eq (M A)
  ; cat_rsubst_rret : forall A B (f : A -> M B -> Prop),
      catrel rret (rsubst f) ⩯ f
  ; rsubst_rsubst : forall A B C (f : A -> M B -> Prop) (g : B -> M C -> Prop),
      catrel (rsubst f) (rsubst g) ⩯ rsubst (catrel f (rsubst g))
  }.

Definition funrel {A B} (f : A -> B) (a : A) : B -> Prop :=
  eq (f a).

Notation subst k := (fun u => bind u k).

(* [funrel] is a monad morphism between [M] as a monad on functions
   and [M] as a monad on relations. *)
Class RelMonadMorphism (M : Type -> Type) {MM : Monad M} {RM : RelMonad M} : Prop :=
  { rret_ret : forall A, rret (A := A) ⩯ funrel ret
  ; rsubst_subst : forall A B (k : A -> M B),
      rsubst (funrel k) ⩯ funrel (subst k)
  }.

Section RMM.

Context
  {M : Type -> Type}
  {MM : Monad M}
  {RM : RelMonad M}
  {RMM : RelMonadMorphism M}.

Lemma rret_ret_rel {A} (a : A) : rret a (ret a).
Proof.
  apply rret_ret; reflexivity.
Qed.

Lemma rsubst_subst_rel {A B} (u : M A) (k : A -> M B)
  : rsubst (funrel k) u (bind u k).
Proof.
  apply rsubst_subst; reflexivity.
Qed.

End RMM.

Section Pred.

Definition lift_Pred {M} `{RelMonad M} {A}
           (u : M A) : M A -> Prop :=
  fun v => u = v.

Definition bind_Pred {M} `{RelMonad M} {A B}
           (pu : M A -> Prop) (pk : A -> M B -> Prop) : M B -> Prop :=
  fun v =>
    exists (u: M A),
      pu u /\
      rsubst pk u v.

Definition ret_Pred {M} `{RelMonad M} {A} (a : A) : M A -> Prop :=
  rret a.

Section PredProof.

Notation lift := lift_Pred.

Context
  (M : Type -> Type)
  {MM : Monad M}
  {RM : RelMonad M}
  {RML : RelMonadLaws M}
  {RMM : RelMonadMorphism M}.

Definition eq_pred {A} (p q : A -> Prop) : Prop :=
  forall a, p a <-> q a.

Theorem ret_bind_l {A B} (a : A) (pk : A -> M B -> Prop)
  : eq_pred (bind_Pred (ret_Pred a) pk)
            (pk a).
Proof.
  unfold bind_Pred, ret_Pred.
  red; intros.
  split.
  - intros [? []].
    eapply cat_rsubst_rret.
    red; eauto.
  - intros.
    eapply cat_rsubst_rret in H. (* This repetition could be avoided... *)
    eauto.
Qed.

Theorem ret_bind_r {A} (pu : M A -> Prop)
  : eq_pred (bind_Pred pu ret_Pred)
            pu.
Proof.
  unfold bind_Pred, ret_Pred.
  red; intros.
  split.
  - intros [? []].
    apply rsubst_rret in H0.
    subst; auto.
  - intros.
    eexists; split; eauto.
    apply rsubst_rret.
    reflexivity.
Qed.

Theorem bind_bind {A B C} (pu : M A -> Prop) (pk : A -> M B -> Prop)
        (ph : B -> M C -> Prop)
  : eq_pred (bind_Pred (bind_Pred pu pk) ph)
            (bind_Pred pu (fun a => bind_Pred (pk a) ph)).
Proof.
  unfold bind_Pred, ret_Pred.
  split.
  - intros [? [ [? []] ]].
    eexists; split; eauto.
    apply rsubst_rsubst.
    red; eauto.
  - intros [? []].
    apply rsubst_rsubst in H0.
    destruct H0 as [? []].
    eauto.
Qed.

Theorem lift_bind {A B} (u : M A) (k : A -> M B)
  : eq_pred (lift (bind u k))
            (bind_Pred (lift u) (fun a => lift (k a))).
Proof.
  unfold bind_Pred, lift.
  split.
  - intros []. eexists; split; eauto.
    apply rsubst_subst. red; auto.
  - intros [? []]. apply rsubst_subst. subst; auto.
Qed.

End PredProof.

End Pred.

Section ITrees.

  (* Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop := *)
  (* | ReturnsRet: forall t, t ≈ Ret a -> Returns a t *)
  (* | ReturnsTau: forall t, Returns a t -> Returns a (Tau t) *)
  (* | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t *)
  (* . *)
  (* Hint Constructors Returns. *)
  
  (* Inductive F (rel: forall A B, (A -> itree E B -> Prop) -> itree E A -> itree E B -> Prop): *)

  (* Instance ITreeRelMonad {E: Type -> Type}: RelMonad (itree E). *)
  (* refine *)
  (*   {| *)
  (*     rret := fun _ a t => t ≈ Ret a; *)
  (*     rsubst := fun _ _ kab ta tb => *)
  (*                 exists a k, Returns a ta /\ kab a k /\ tb ≈ bind ta k *)

  (*   |}. *)

End ITrees.
