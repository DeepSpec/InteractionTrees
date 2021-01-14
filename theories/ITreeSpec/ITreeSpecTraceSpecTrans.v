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
     Dijkstra.DijkstraMonad
     Dijkstra.ITrace
     Dijkstra.ITraceBind
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
     Dijkstra.StateSpecT
     Dijkstra.StateIOTrace
     ITreeSpec.ITreeSpecDefinition
     ITreeSpec.SatisfiesFacts
     ITreeSpec.ITreeSpecObservation
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Notation "↑ log" := (ev_list_to_stream log) (at level 30).

(* unclear if this direction is right, might be other way or both ways*)
Program Definition inj {E R} (phi : itree_spec E R) : TraceSpec E R :=
  fun log p => forall tr, (↑ log ++ tr) ⊧ phi ->  p ( ↑ log ++ tr) .


(* see if this injection function works towards *)
