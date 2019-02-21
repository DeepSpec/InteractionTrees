(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics
     Core
     Morphisms
     Effect.Sum.

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
    cofix mutfix_ (t : itree (D +' E) R) : itree E R :=
      handleF1 mutfix_
               (fun _ d k => Tau (mutfix_ (ctx _ d >>= k)))
               (observe t).

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

(* Iterate a function updating an accumulator [C],
   until it produces an output [B]. *)
Definition loop {E : Type -> Type} {A B C : Type}
           (body : (C + A) -> itree E (C + B)) :
  A -> itree E B :=
  rec (fun a =>
    bc <- translate (fun _ x => inr1 x) _ (body a) ;;
    match bc with
    | inl c => ITree.liftE (inl1 (Call a))
    | inr b => Ret b
    end) ∘ inr.

(* Iterate a function updating an accumulator [A], until it produces
   an output [B]. It's an Asymmetric variant of [loop], and it looks
   similar to an Anamorphism, hence the name [aloop]. *)
Definition aloop {E : Type -> Type} {A B : Type}
           (body : A -> itree E (A + B)) :
  A -> itree E B :=
  rec (fun a =>
    ac <- translate (fun _ x => inr1 x) _ (body a) ;;
    match ac with
    | inl a => ITree.liftE (inl1 (Call a))
    | inr b => Ret b
    end).
