(** * General-purpose definitions *)

(** Not specific to itrees. *)

(* begin hide *)
From Coq Require
     Ensembles.

From Coq Require Import
     RelationClasses.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Data.Monads.StateMonad
     Data.Monads.ReaderMonad
     Data.Monads.OptionMonad
     Data.Monads.EitherMonad.

Import MonadNotation.
Local Open Scope monad.
(* end hide *)

(** ** Parametric functions *)

(** A notation for a certain class of parametric functions.
    Some common names of things that can be represented by such a type:

    - Natural transformations (functor morphisms)
    - Monad morphisms
    - Event morphisms (if [E] and [F] are simply
      indexed types with no particular structure)
    - Event handlers (if [F] is a monad)
 *)
Notation "E ~> F" := (forall T, E T -> F T)
  (at level 99, right associativity, only parsing) : type_scope.
(* The same level as [->]. *)
(* This might actually not be such a good idea. *)

(** Identity morphism. *)
Definition idM {E : Type -> Type} : E ~> E := fun _ e => e.

(** [void] is a shorthand for [Empty_set]. *)
Notation void := Empty_set.

(** ** Common monads and transformers. *)

Module Monads.

Definition identity (a : Type) : Type := a.

Definition stateT (s : Type) (m : Type -> Type) (a : Type) : Type :=
  s -> m (prod s a).
Definition state (s a : Type) := s -> prod s a.

Definition readerT (r : Type) (m : Type -> Type) (a : Type) : Type :=
  r -> m a.
Definition reader (r a : Type) := r -> a.

Definition writerT (w : Type) (m : Type -> Type) (a : Type) : Type :=
  m (prod w a).
Definition writer := prod.

Instance Functor_stateT {m s} {Fm : Functor m} : Functor (stateT s m)
  := {|
    fmap _ _ f := fun run s => fmap (fun sa => (fst sa, f (snd sa))) (run s)
    |}.

Instance Monad_stateT {m s} {Fm : Monad m} : Monad (stateT s m)
  := {|
    ret _ a := fun s => ret (s, a)
  ; bind _ _ t k := fun s =>
      sa <- t s ;;
      k (snd sa) (fst sa)
    |}.

End Monads.

(** ** Loop operator *)

(** [iter]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R].
 *)
Polymorphic Class MonadIter (M : Type -> Type) : Type :=
  iter : forall {R I: Type}, (I -> M (I + R)%type) -> I -> M R.

(** *** Transformer instances *)

(** And the standard transformers can lift [iter].

    Quite easily in fact, no [Monad] assumption needed.
 *)

Instance MonadIter_stateT {M S} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (stateT S M) :=
  fun _ _ step i => mkStateT (fun s =>
    iter (fun is =>
      let i := fst is in
      let s := snd is in
      is' <- runStateT (step i) s ;;
      ret match fst is' with
          | inl i' => inl (i', snd is')
          | inr r => inr (r, snd is')
          end) (i, s)).

Polymorphic Instance MonadIter_stateT0 {M S} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (Monads.stateT S M) :=
  fun _ _ step i s =>
    iter (fun si =>
      let s := fst si in
      let i := snd si in
      si' <- step i s;;
      ret match snd si' with
          | inl i' => inl (fst si', i')
          | inr r => inr (fst si', r)
          end) (s, i).

Instance MonadIter_readerT {M S} {AM : MonadIter M} : MonadIter (readerT S M) :=
  fun _ _ step i => mkReaderT (fun s =>
    iter (fun i => runReaderT (step i) s) i).

Instance MonadIter_optionT {M} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (optionT M) :=
  fun _ _ step i => mkOptionT (
    iter (fun i =>
      oi <- unOptionT (step i) ;;
      ret match oi with
          | None => inr None
          | Some (inl i) => inl i
          | Some (inr r) => inr (Some r)
          end) i).

Instance MonadIter_eitherT {M E} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (eitherT E M) :=
  fun _ _ step i => mkEitherT (
    iter (fun i =>
      ei <- unEitherT (step i) ;;
      ret match ei with
          | inl e => inr (inl e)
          | inr (inl i) => inl i
          | inr (inr r) => inr (inr r)
          end) i).

(** And the nondeterminism monad [_ -> Prop] also has one. *)

Inductive iter_Prop {R I : Type} (step : I -> I + R -> Prop) (i : I) (r : R)
  : Prop :=
| iter_done
  : step i (inr r) -> iter_Prop step i r
| iter_step i'
  : step i (inl i') ->
    iter_Prop step i' r ->
    iter_Prop step i r
.

Polymorphic Instance MonadIter_Prop : MonadIter Ensembles.Ensemble := @iter_Prop.

(* Elementary constructs for predicates. To be moved in their own file eventually *)
Definition equiv_pred {A : Type} (R S: A -> Prop): Prop :=
  forall a, R a <-> S a.

Definition sum_pred {A B : Type} (PA : A -> Prop) (PB : B -> Prop) : A + B -> Prop :=
  fun x => match x with | inl a => PA a | inr b => PB b end.

Definition prod_pred {A B : Type} (PA : A -> Prop) (PB : B -> Prop) : A * B -> Prop :=
  fun '(a,b) => PA a /\ PB b.

Definition TT {A : Type} : A -> Prop := fun _ => True.
Hint Unfold TT sum_pred prod_pred: core.

Global Instance equiv_pred_refl  {A} : Reflexive (@equiv_pred A).
Proof.
  split; auto.
Qed.
Global Instance equiv_pred_symm  {A} : Symmetric (@equiv_pred A).

Proof.
  red; intros * EQ; split; intros; eapply EQ; auto.
Qed.
Global Instance equiv_pred_trans {A} : Transitive (@equiv_pred A).
Proof.
  red; intros * EQ1 EQ2; split; intros; (apply EQ1,EQ2 || apply EQ2,EQ1); auto.
Qed.
Global Instance equiv_pred_equiv {A} : Equivalence (@equiv_pred A).
Proof.
  split; typeclasses eauto.
Qed.

