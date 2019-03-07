(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by mapping the event morphism across each visible event.  We call this
    process _event translation_.


    Translate is defined separately from the itree Morphisms because it is
    conceptually at a different level: translation always yields strong
    bisimulations.  We can relate translation and interpretation via the law:

    translate h t ≈ interp (liftE ∘ h) t
*)

(** The semantics of an interaction tree [itree E ~> M] can be
    derived from semantics given for every individual effect
    [E ~> M].

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] means [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following.

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "Itree interpreters" (or "itree morphisms") are monad morphisms
      [itree E ~> itree F]. Most interpreters in this library are
      actually itree interpreters.

    This module provides various ways of defining interpreters
    from effect handlers and other similar structures.

    - "Effect handlers" are functions [E ~> M] where [M] is a monad.

    - "Itree effect handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough).
 *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Core.ITree
     Indexed.Sum.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.
(* end hide *)

(** A plain effect morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {E F R} (h : E ~> F) (rec: itree E R -> itree F R) (t : itreeF E R _) : itree F R  :=
  match t with
  | RetF x => Ret x
  | TauF t => Tau (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

CoFixpoint translate {E F R} (h : E ~> F) (t : itree E R) : itree F R
  := translateF h (translate h) (observe t).

(** An itree effect handler [E ~> itree F] defines an
    itree morphism [itree E ~> itree F]. *)
Definition interp {E F : Type -> Type} (h : E ~> itree F) :
  itree E ~> itree F := fun R =>
  ITree.aloop (fun t =>
    match observe t with
    | RetF r => inr r
    | TauF t => inl (Ret t)
    | VisF e k => inl (ITree.map k (h _ e))
    end).
(* TODO: this does a map, and aloop does a bind. We could fuse those
   by giving aloop a continuation to compose its bind with.
   (coyoneda...) *)
(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

(* The indexed type [D : Type -> Type] gives the signature of
   a set of functions. For example, a pair of mutually recursive
   [even : nat -> bool] and [odd : nat -> bool] can be declared
   as follows:

[[
   Inductive D : Type -> Type :=
   | Even : nat -> D bool
   | Odd  : nat -> D bool.
]]

   Their mutually recursive definition can then be written finitely
   (without [Fixpoint]):

[[
   Definition def : D ~> itree (D +' emptyE) := fun _ d =>
     match d with
     | Even n => match n with
                 | O => ret true
                 | S m => liftE (Odd m)
                 end
     | Odd n => match n with
                | O => ret false
                | S m => liftE (Even m)
                end
     end.
]]

   The function [interp_mrec] below then ties the knot.

[[
   Definition f : D ~> itree emptyE :=
     interp_mrec def.

   Definition even (n : nat) : itree emptyE bool := f _ (Even n).
   Definition odd  (n : nat) : itree emptyE bool := f _ (Odd n).
]]

   The result is still in the [itree] monad of possibly divergent
   computations, because [mutfix_itree] doesn't care whether
   the mutually recursive definition is well-founded.

 *)

(** Interpret an itree in the context of a mutually recursive
    definition ([ctx]). *)
Definition interp_mrec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
  fun R =>
    ITree.aloop (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => inr r
      | TauF t => inl (Ret t)
      | VisF (inl1 d) k => inl (Ret (ctx _ d >>= k))
      | VisF (inr1 e) k => inl (Vis e (fun x => Ret (k x)))
      end).

(** Unfold a mutually recursive definition into separate trees,
    resolving the mutual references. *)
Definition mrec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : D ~> itree E :=
  fun R d => interp_mrec ctx _ (ctx _ d).

Inductive callE (A B : Type) : Type -> Type :=
| Call : A -> callE A B B.

Arguments Call {A B}.

(** Get the [A] contained in a [callE A B]. *)
Definition unCall {A B T} (e : callE A B T) : A :=
  match e with
  | Call a => a
  end.

(** Lift a function on [A] to a morphism on [callE]. *)
Definition calling {A B} {F : Type -> Type}
           (f : A -> F B) : callE A B ~> F :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* This is identical to [callWith] but [rec] finds a universe
   inconsistency with [callWith], and not with [callWith']. *)
Definition calling' {A B} {F : Type -> Type}
           (f : A -> itree F B) : callE A B ~> itree F :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* Interpret a single recursive definition. *)
Definition rec {E : Type -> Type} {A B : Type}
           (body : A -> itree (callE A B +' E) B) :
  A -> itree E B :=
  fun a => mrec (calling' body) _ (Call a).

Definition loop_once {E : Type -> Type} {A B C : Type}
           (body : C + A -> itree E (C + B))
           (loop_ : C + A -> itree E B) : C + A -> itree E B :=
  fun ca =>
    cb <- body ca ;;
    match cb with
    | inl c => loop_ (inl c)
    | inr b => Ret b
    end.

Definition loop_ {E : Type -> Type} {A B C : Type}
           (body : C + A -> itree E (C + B)) :
  C + A -> itree E B :=
  cofix loop__ := loop_once body (fun cb => Tau (loop__ cb)).

(** Iterate a function updating an accumulator [C],
    until it produces an output [B]. An encoding of tail recursive
    functions.

    The Kleisli category for the [itree] monad is a traced
    monoidal category, with [loop] as its trace.
 *)
(* We use explicit recursion instead of relying on [rec] to
   make the definition properly tail recursive. *)
Definition loop {E : Type -> Type} {A B C : Type}
           (body : (C + A) -> itree E (C + B)) :
  A -> itree E B :=
  fun a => loop_ body (inr a).
