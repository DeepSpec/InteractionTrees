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
     Dijkstra.IBranch
     Dijkstra.IBranchBind
     Dijkstra.EuttDiv
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma bind_trigger_refine : forall (E : Type -> Type) (A R : Type) (b : itree (EvAns E) R) 
                              (e : E A) (k : A -> itree E R),
    (exists a : A, True) ->
    b ⊑ ITree.bind (ITree.trigger e) k -> 
    exists a : A, exists (k' : unit -> ibranch E R), b ≈ Vis (evans A e a) k' /\ k' tt ⊑ k a.
Proof.
  intros. rewrite bind_trigger in H0. apply branch_refine_vis in H0 as Hvis.
  destruct Hvis as [X [e' [k' Hbvis] ] ]. setoid_rewrite Hbvis.
  rewrite Hbvis in H0.
  punfold H0. red in H0. cbn in *. inv H0. inj_existT. subst. inv H3; inj_existT; subst.
  - exists a. exists k'. split; try reflexivity. pclearbot.
    assert (RAnsRef E unit A (evans A e a) tt e a ); auto.
    apply H8 in H0. pclearbot. auto.
  - destruct H as [a _]. contradiction.
Qed.
