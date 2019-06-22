(** * General-purpose definitions *)

(** Not specific to itrees. *)

(* begin hide *)
From Coq Require Ensembles.

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

(** ** Relations for morphisms/parametricity *)

(** Logical relation for the [sum] type. *)
Variant sum_rel {A1 A2 B1 B2 : Type}
        (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  : A1 + B1 -> A2 + B2 -> Prop :=
| inl_morphism a1 a2 : RA a1 a2 -> sum_rel RA RB (inl a1) (inl a2)
| inr_morphism b1 b2 : RB b1 b2 -> sum_rel RA RB (inr b1) (inr b2)
.
Arguments inl_morphism {A1 A2 B1 B2 RA RB}.
Arguments inr_morphism {A1 A2 B1 B2 RA RB}.
Hint Constructors sum_rel.

(** Logical relation for the [prod] type. *)
Variant prod_rel {A1 A2 B1 B2 : Type}
        (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  : (A1 * B1) -> (A2 * B2) -> Prop :=
| prod_morphism a1 a2 b1 b2 : RA a1 a2 -> RB b1 b2 -> prod_rel RA RB (a1, b1) (a2, b2)
.

Arguments prod_morphism {A1 A2 B1 B2 RA RB}.
Hint Constructors prod_rel.


(* SAZ: TODO: Move this elsewhere, it belong with the Basics *)
Section ProdRelInstances.
  Context {R S : Type}.
  Context (RR : R -> R -> Prop).
  Context (SS : S -> S -> Prop).

  Global Instance prod_rel_refl `{Reflexive _ RR} `{Reflexive _ SS} : Reflexive (prod_rel RR SS).
  Proof.
    red. destruct x. constructor; auto.
  Qed.
  
  Global Instance prod_rel_sym `{Symmetric _ RR} `{Symmetric _ SS}  : Symmetric (prod_rel RR SS).
  Proof.
    red. intros. 
    inversion H1. subst.
    constructor; symmetry; auto.
  Qed.

  Global Instance prod_rel_trans `{Transitive _ RR} `{Transitive _ SS}  : Transitive (prod_rel RR SS).
  Proof.
    red.
    intros.
    inversion H1.
    inversion H2.
    subst.
    inversion H9; subst.
    constructor; etransitivity; eauto.
  Qed.

  Global Instance prod_rel_eqv `{Equivalence _ RR} `{Equivalence _ SS} : Equivalence (prod_rel RR SS).
  Proof.
    constructor; typeclasses eauto.
  Qed.

End ProdRelInstances.


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

(** [aloop]: A primitive for general recursion.
    Iterate a function updating an accumulator [I], until it produces
    an output [R]. It's an Asymmetric variant of [loop], and it looks
    similar to an Anamorphism, hence the name [aloop].
 *)
Polymorphic Class ALoop (M : Type -> Type) : Type :=
  aloop : forall {R I: Type}, (I -> M I + R) -> I -> M R.

(* TODO: try this one.
Class ALoop (M : Type -> Type) : Type :=
  aloop : forall I R, (I -> itreeF M R I) -> I -> M R.

It allows us to drop the [Monad] and [Functor] constraints
in [Interp.Interp.interp].
 *)

(** *** Transformer instances *)

(** And the standard transformers can lift [aloop].

    Quite easily in fact, no [Monad] assumption needed.
 *)

(* TODO: some of these mk functions have too many explicit arguments *)
Instance ALoop_stateT {M S} {AM : ALoop M} : ALoop (stateT S M) :=
  fun _ _ step i => mkStateT _ _ (fun s =>
    aloop (fun is =>
      let i := fst is in
      let s := snd is in
      match step i with
      | inl run => inl (runStateT run s)
      | inr r => inr (r, s)
      end) (i, s)).

Polymorphic Instance ALoop_stateT0 {M S} {AM : ALoop M} : ALoop (Monads.stateT S M) :=
  fun _ _ step i s =>
    aloop (fun si =>
      let s := fst si in
      let i := snd si in
      match step i with
      | inl run => inl (run s)
      | inr r => inr (s, r)
      end) (s, i).

Instance ALoop_readerT {M S} {AM : ALoop M} : ALoop (readerT S M) :=
  fun _ _ step i => mkReaderT (fun s =>
    aloop (fun i =>
      match step i with
      | inl run => inl (runReaderT run s)
      | inr r => inr r
      end) i).

Instance ALoop_optionT {M} {AM : ALoop M} : ALoop (optionT M) :=
  fun _ _ step i => mkOptionT _ _ (
    aloop (fun oi =>
      match oi with
      | Some i =>
        match step i with
        | inl run => inl (unOptionT run)
        | inr r => inr (Some r)
        end
      | None => inr None
      end) (Some i)).

Instance ALoop_eitherT {M E} {AM : ALoop M} : ALoop (eitherT E M) :=
  fun _ _ step i => mkEitherT _ _ _ (
    aloop (fun ei =>
      match ei with
      | inl e => inr (inl e)
      | inr i =>
        match step i with
        | inl run => inl (unEitherT run)
        | inr r => inr (inr r)
        end
      end) (inr i)).

(** And the nondeterminism monad [_ -> Prop] also has one. *)

Inductive aloop_Prop {R I : Type} (step : I -> (I -> Prop) + R) (i : I) (r : R)
  : Prop :=
| aloop_done
  : step i = inr r -> aloop_Prop step i r
| aloop_step p i'
  : step i = inl p ->
    p i' ->
    aloop_Prop step i' r ->
    aloop_Prop step i r
.

Polymorphic Instance ALoop_Prop : ALoop Ensembles.Ensemble := @aloop_Prop.
