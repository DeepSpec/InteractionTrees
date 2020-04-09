From ExtLib Require Import
     Structures.Monad.
From ITree Require Import
     ITree
     Eq.Eq
     ITreeMonad
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Monad.

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program.Equality
     Classes.RelationClasses
.

Require Import Classical_Prop.
(* See [PropT.v] in the Vellvm repo for the exact framework to follow with respect to typeclasses, as well as a proof of most monad laws for [PropTM (itree E)] *)

  (* To move to Eq/Eq.v eventually *)
Section Transformer.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMR_OK m EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Definition closed_eqmR {A B} (PA : m A -> Prop) (PB : m B -> Prop) (REL : A -> B -> Prop) :=
    forall a b, eqmR REL a b -> (PA a <-> PB b).

  (* Design choice: under generalized eqm, PropTM is not closed by construction.*)
  Definition PropTM : Type -> Type :=
    fun A => m A -> Prop.

  Definition eqm' : forall (A B : Type) (R : A -> B -> Prop), PropTM A -> PropTM B -> Prop :=
    fun _ _ REL PA PB =>
      (forall x y r, eqmR r x y -> (PA x <-> PB y)) /\
      closed_eqmR PA PB REL.

  Global Instance EqMR_PropTM : EqMR PropTM := eqm'.

  Definition ret_f := (fun A (a : A) (ma : m A) => eqm ma (ret a)).

  Definition agrees {A : Type} : A -> (A -> Prop) -> Prop :=
    fun (x : A) (P : A -> Prop) => P x.

  Infix "∈" := agrees (at level 70).

  Definition bind_f :=
  fun A B (PA : PropTM A) (K : A -> PropTM B) (mb : m B) =>
    exists (ma : m A) (kb : A -> m B),
      PA ma /\ eqmR agrees (Functor.fmap kb ma) (Functor.fmap K ma) /\
      Monad.eqm mb (bind ma kb).

  Global Instance Monad_PropTM : Monad (PropTM) :=
    {|
      ret:= fun A (a: A) => (ret_f A a)
      ; bind := fun A B (PA : PropTM A) (K : A -> PropTM B) =>
                  (bind_f A B PA K)
    |}.

  (* TODO: How do we want to state the closure properties? *)

  Import CatNotations.
  Local Open Scope cat_scope.
End Transformer.

Section Laws.

  Variable (m: Type -> Type).
  Context `{Monad m}.
  Context {EQM : EqMR m}.
  Context {ITERM : MonadIter m}.
  Context {HEQP: @EqMR_OK m EQM}.
  Context {HMLAWS: @MonadLaws m EQM _}.

  Instance eqm_MonadProp_Proper {A} (P: PropTM m A) : Proper (@eqm _ _ A ==> iff) P.
  Proof.
    cbv. intros x y Heq.
  Admitted.

  Lemma ret_bind_l:
    forall A B (f : A -> PropTM m B) (a : A),
      eqm (bind (ret a) f) (f a).
  Proof.
  Admitted.

  Lemma ret_bind_r:
    forall A (ma : PropTM m A),
      eqm (bind ma (fun x => ret x)) ma.
  Proof.
    intros A PTmA.
    cbn in *. unfold bind_f in *. unfold ret_f in *. cbn in *. unfold liftM in *.
    split.
    + intros mA1 mA2 R. intros Heqmr.
      split.
    - intros comp.
      destruct comp as (mA & kamA & Hpta & Heqmrbind & Heqbind).
      try rewrite <- Heqmr. (* rewrite <- Heqmr *)
      (* Setoid rewrite failure *)
      Abort.

  Lemma bind_bind:
    forall A B C (ma : PropTM m A) (mab : A -> PropTM m B)
           (mbc : B -> PropTM m C),
      eqm (bind (bind ma mab) mbc) (bind ma (fun x => bind (mab x) mbc)).
  Proof.
  Admitted.

  Lemma respect_bind :
  forall a b : Type, Proper (eqm ==> pointwise_relation a eqm ==> @eqm (PropTM m) _ b) bind.
  Proof.
  Admitted.

  Global Instance PropTM_Laws : @MonadLaws (PropTM m) _ _.
  split. apply ret_bind_l.
  apply ret_bind_r. apply bind_bind.
  apply respect_bind.
  Qed.

End Laws.
