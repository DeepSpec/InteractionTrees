From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive Void : Type -> Type := .

Section PureItree.

  (*how to deal with nonterminsim*)
  (* partial correctness itrees   *)
  (* match t with Ret a => p (inl a)  *)
  
  Definition PureItree A := itree Void A.

  (* can interpretation deal with infinite taus*)

  Definition _PureItreeSpec A := (A + unit -> Prop) -> Prop.

  Definition _PureItreeSpec' A := (itree Void A -> Prop) -> Prop.

  Definition retp A (a : A) := fun (p : A + unit -> Prop) => (p (inl a)).

End PureItree.

Section StateItree.
  Context (S : Type).
  
  Definition StateItree A := itree (stateE S) A.

  Definition _StateItreeSpec A := (itree Void (A * S) -> Prop) -> S -> Prop.
(*
  Definition _retsis A (a: A) : _StateItreeSpec A := fun p s => p (Itree.ret _ (a,s)).

  Definition _stateH A (ev : stateE S) :=
    match ev with
    | Get => fun 


  

  CoInductive t :=.
*)
