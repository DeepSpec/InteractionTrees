(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITree
     Indexed.Sum
     Interp.Handler.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)
(** * General recursion *)

(** *** Mutual recursion *)

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
   Definition def : D ~> itree (D +' void1) := fun _ d =>
     match d with
     | Even n => match n with
                 | O => ret true
                 | S m => lift (Odd m)
                 end
     | Odd n => match n with
                | O => ret false
                | S m => lift (Even m)
                end
     end.
]]

   The function [interp_mrec] below then ties the knot.

[[
   Definition f : D ~> itree void1 :=
     interp_mrec def.

   Definition even (n : nat) : itree void1 bool := f _ (Even n).
   Definition odd  (n : nat) : itree void1 bool := f _ (Odd n).
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

(** *** Simple recursion *)

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

(* TODO: This is identical to [callWith] but [rec] finds a universe
   inconsistency with [calling], and not with [calling'].
   The inconsistency now pops up later (currently in [Effects.Env]) *)
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

(** An easy way to construct an event suitable for use with [rec].
    [call] is an event representing the recursive call.  Since in general, the
    function might have other effects of type [E], the resulting itree has
    type [(callE A B +' E)].
*)
Definition call {E A B} (a:A) : itree (callE A B +' E) B := ITree.lift (inl1 (Call a)).

Definition recursive {E A B} (f : A -> itree (callE A B +' E) B) : (callE A B +' E) ~> itree E :=
  case_ (calling' (rec f)) ITree.lift.
