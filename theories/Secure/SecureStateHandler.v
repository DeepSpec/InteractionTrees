From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section SecureStateHandler.
Context (Label : Preorder).
Context (E : Type -> Type).
Context (priv : forall A, E A -> L).
Context (var : Type).
Context (contains_var : forall A, E A -> var -> Prop).

(* this should be what it means for a relation on states and a *)

Definition state value := var -> value.

Definition rel_respects_labels {value} (RS : state value -> state value -> Prop)
           (l : L) :=
  forall (x : var), (forall A (e : E A), contains_var A e x -> leq (priv A e) l ) <-> (forall s1 s2, s1 x <> s2 x -> ~ RS s1 s2 ).

End SecureStateHandler.


(* given a standard state handler, what it means for a label to agree*)
(* priv (Get | Set) x ⊑ l <-> ((forall s1 s2, s1 x <> s2 x) -> ~ RS s1 s2 *)


      



End SecureStateHandler.
