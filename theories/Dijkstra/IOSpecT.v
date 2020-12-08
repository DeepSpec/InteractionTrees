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
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
   (*  Simple *)
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Definition WHist A :=  (Delay A * stream Ev -> Prop) -> ( stream Ev -> Prop)  
(* a tree can be viewed as a nondeterministic funtion from initial logs to
   Delay value and final log*)

(*ret should just be stateT ret*)

(*depending on the bind, this the total log may either be the concat of these logs
  or just the final log
*)

(*


*)
