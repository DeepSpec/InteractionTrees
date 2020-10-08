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
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* Contains a specification monad transformer for exceptions*)

Section ExcT.
  Context (E : Type).
  Context (W : Type -> Type).
  Context {EqW : EqM W}.
  Context {MonadW : Monad W}.
  Context {MonadLawsW : MonadLaws W}.
  Context {OrderW : OrderM W}.
  Context {OrderedMonadW : OrderedMonad W}.
  Context {EquivRel : forall A, Equivalence (EqW A) }.

  Definition ExcSpecT (A : Type) := W (E + A).

  Definition ret_exc (A : Type) (a : A) :ExcSpecT A := ret (inr a).

  Definition bind_exc (A B : Type) (m : W (E + A)) (f : A -> ExcSpecT B) : ExcSpecT B :=
    bind m  (fun (x : E + A) => match x with inr a => f a | inl e => ret (inl e) end). 

  Global Instance ExcSpecTMonad : Monad ExcSpecT :=
    {
      ret := ret_exc;
      bind := bind_exc
    }.

  Global Instance ExcSpecTOrder : OrderM ExcSpecT :=
    fun _ w1 w2 => OrderW _ w1 w2.

   Global Instance ExcSpecTOrderedLaws : OrderedMonad ExcSpecT.
   Proof.
     destruct OrderedMonadW. constructor. 
     - intros. repeat red. apply reflex.
     - intros. repeat red. repeat red in H, H0. eapply trans; eauto.
     - intros A B w1 w2 f1 f2 Hlw Hlf.
       apply monot; auto. intros. destruct a as [e |  a]. simpl; try apply reflex.
       apply Hlf.
   Qed.

  Global Instance ExcSpecTEq : EqM ExcSpecT := fun _ w1 w2 => EqW _ w1 w2.



End ExcT.
