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
     Eq.EqAxiom
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

(* Tau t ≈ t*)
(* eqit_secure (Vis e k)  (k a) *)

(* r => fun (f g : A -> B) => f = g*)
Global Instance strong_bisim_proper_paco {E R1 R2 F r} :
       Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> flip impl) (paco2 F r).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.
