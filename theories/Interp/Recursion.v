(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Indexed.Sum.

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
                 | S m => trigger (Odd m)
                 end
     | Odd n => match n with
                | O => ret false
                | S m => trigger (Even m)
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
    ITree.iter (fun t : itree (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF (inl1 d) k => Ret (inl (ctx _ d >>= k))
      | VisF (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
      end).

Arguments interp_mrec {D E} ctx [T].

(** Unfold a mutually recursive definition into separate trees,
    resolving the mutual references. *)
Definition mrec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : D ~> itree E :=
  fun R d => interp_mrec ctx (ctx _ d).

Arguments mrec {D E} ctx [T].

(** Make a recursive call in the handler argument of [mrec]. *)
Definition trigger_inl1 {D E : Type -> Type} : D ~> itree (D +' E)
  := fun _ d => ITree.trigger (inl1 d).

Arguments trigger_inl1 {D E} [T].

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

(** Short for endofunctions, used in [mrec_fix] and [rec_fix]. *)
Local Notation endo T := (T -> T).

Definition mrec_fix {D E : Type -> Type} {A B : Type}
           (ctx : endo (D ~> itree (D +' E)))
  : D ~> itree E
  := mrec (ctx trigger_inl1).

Notation "'mrec-fix' f d := g" := (mrec_fix (fun f _ d => g))
  (at level 200, f ident, d pattern).
(* No idea what a good level would be. *)

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
   The inconsistency now pops up later (currently in [Events.Env]) *)
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
  fun a => mrec (calling' body) (Call a).

(** An easy way to construct an event suitable for use with [rec].
    [call] is an event representing the recursive call.  Since in general, the
    function might have other events of type [E], the resulting itree has
    type [(callE A B +' E)].
*)
Definition call {E A B} (a:A) : itree (callE A B +' E) B := ITree.trigger (inl1 (Call a)).

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

Definition rec_fix {E : Type -> Type} {A B : Type}
           (body : endo (A -> itree (callE A B +' E) B))
  : A -> itree E B
  := rec (body call).

Notation "'rec-fix' f a := g" := (rec_fix (fun f a => g))
  (at level 200, f ident, a pattern).
(* No idea what a good level would be. *)
