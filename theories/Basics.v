(** General-purpose definitions, not specific to itrees *)

(* begin hide *)
Set Universe Polymorphism.
(* end hide *)

(** A notation for a certain class of parametric functions.
    Some common names for things that can be represented
    by such a type:

    - Effect morphisms (if [E] and [F] are simply
      indexed types with no particular structure)
    - Natural transformations (functors morphisms)
    - Monad morphisms
 *)
Notation "E ~> F" := (forall T, E T -> F T)
  (at level 99, right associativity) : type_scope.

(** Identity morphism. *)
Definition idM {E : Type -> Type} : E ~> E := fun _ e => e.

(** A universe polymorphic empty type.
    Similar to [Empty_set : Set] and [False : Prop].
    Defined as an [Inductive] to get the usual eliminators. *)
(* TODO: Is this any better than [Definition void = Empty_set.]? *)
Inductive void : Type := .

(** Common monads and transformers. *)

Module Monads.

Set Universe Polymorphism.

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

End Monads.
