From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
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
     Dijkstra.PureITreeDijkstra
     Dijkstra.IterRel
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma equiv_resp_eutt : forall A B (a : A), resp_eutt Void _ (fun t : itree Void (A + B) => t ≈ ret (inl a) ).
Proof.
  intros. intros t1 t2 H. split; intros.
  - rewrite <- H. auto.
  - rewrite H. auto.
Qed.

Definition spec_iter_arrow_rel {A B : Type} (f : A -> PureITreeSpec (A + B) ) (a1 a2: A) : Prop :=
  proj1_sig (f a1) (fun t => t ≈ ret (inl a2)) (equiv_resp_eutt A B a2).

Notation "x =[ f ]=> y" := (spec_iter_arrow_rel f x y) (at level 80).

Lemma obs_arrow_rel_det : forall A B (f : A -> itree Void (A + B) ) (a1 a2 a3: A), 
  a1 =[ fun x => obs _ (f x) ]=> a2 -> a1 =[ fun x => obs _ (f x) ]=> a3 -> a2 = a3.
Proof.
  intros. unfold spec_iter_arrow_rel in *.
  cbn in *. red in H. red in H0. rewrite H in H0. apply inv_ret in H0. injection H0. auto.
Qed.
