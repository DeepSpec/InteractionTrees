(** * Exception event *)

(* begin hide *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
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
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
     Dijkstra.StateSpecT
   (*  Simple *)
.

(* end hide *)

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Throw exceptions of type [Err]. *)
Variant exceptE (Err : Type) : Type -> Type :=
| Throw : Err -> exceptE Err void.

(** Since the output type of [Throw] is [void], we can make it an action
    with any return type. *)
Definition throw {Err : Type} {E : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : itree E X
  := vis (Throw _ e) (fun v : void => match v with end).

(* translate *)

(*
Program Definition try_catch {Err R : Type } {E : Type -> Type} 
           
           (ttry : itree (exceptE Err +' E) R) (kcatch : Err -> itree (exceptE Err +' E) R) : itree (exceptE Err +' E) R :=
  let ttry' : itree (exceptE Err +' (exceptE Err +' E)) R := 
              translate (fun _ e => match e with |  inl1 e' => inl1 e' | inr1 e' => (inr1 (inr1 e') ) end ) ttry in
  mrec (fun _ e => 
          match e with Throw _ err => translate (fun _ e => inr1 e) (kcatch err) end) ttry'.
*)
