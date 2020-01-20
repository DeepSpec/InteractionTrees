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
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac clear_ret_eutt_spin :=
  match goal with | H : ret ?a ≈ spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
             | H : Ret ?a ≈ spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
             | H : spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
             | H : divergence (ret _ ) |- _ => pinversion H
  end.
  
Ltac invert_evidence :=
  intros; repeat match goal with 
                 | H : _ /\ _ |- _ => destruct H
                 | H : _ \/ _ |- _ => destruct H 
                 | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                 | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                 | H : upaco1 _ _ _ |- _ => pclearbot
                 end.

Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ => 
                                                 apply inv_ret in H; try discriminate; try (injection H as H);
                                                 subst end.


Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.


Notation "a ∈ b" := (proj1_sig b a) (at level 70). 

Notation "a ∋ b" := (proj1_sig a b) (at level 70).

Section StateSpecT.
  Context (S : Type).
  Context (W : Type -> Type).

  Context {SpecMonadW : SpecMonad W}.

  Definition StateSpecT (A : Type) := S -> Input W (S *A) -> Prop.

End StateSpecT.


