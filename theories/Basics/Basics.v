(** * General-purpose definitions *)

(** Not specific to itrees. *)

(* begin hide *)
From Coq Require
     Ensembles.

From Coq Require Import
     Morphisms
     Setoid
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


(* SAZ: There is probably a nice way to typeclassify the eq_rel proofs *)
(* Heterogeneous relation equivalence *)
Definition eq_rel {A B} (R : A -> B -> Prop) (S : A -> B -> Prop) :=
  forall (a:A) (b:B), (R a b) <-> (S a b).
(* subrelation R S /\ subrelation S R *)

Lemma eq_rel_prod_eq : forall A B, eq_rel (prod_rel eq eq) (eq : A * B -> A * B -> Prop).
Proof.
  intros.
  unfold eq_rel; split; intros.
  - inversion H. subst. reflexivity.
  - destruct a; destruct b; inversion H; subst; constructor; reflexivity.
Qed.           

  
Global Instance eq_rel_Reflexive {A B} : Reflexive (@eq_rel A B).
Proof.
  red. unfold eq_rel. tauto.
Qed.

Global Instance eq_rel_Symmetric {A B} : Reflexive (@eq_rel A B).
Proof.
  red. unfold eq_rel. tauto.
Qed.

Global Instance eq_rel_Transitive {A B} : Transitive (@eq_rel A B).
Proof.
  red. unfold eq_rel. intros. eapply transitivity; eauto.
Qed.


Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
Proof.
  repeat red; unfold eq_rel; split; intros.
  - rewrite <- H. rewrite H1. rewrite H0. reflexivity.
  - rewrite H. rewrite H1. rewrite H0. reflexivity.
Qed.

Global Instance prod_rel_Proper {A1 A2 B1 B2} : Proper (eq_rel ==> eq_rel ==> eq_rel) (@prod_rel A1 A2 B1 B2).
Proof.
  repeat red; unfold eq_rel; split; intros.
  - inversion H1; subst. constructor. apply H. assumption. apply H0. assumption.
  - inversion H1; subst. constructor. apply H. assumption. apply H0. assumption.
Qed.



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
