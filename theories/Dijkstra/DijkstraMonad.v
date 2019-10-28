From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Data.Monads.StateMonad
     Data.Monads.ReaderMonad
     Data.Monads.OptionMonad
     Data.Monads.EitherMonad
     .
From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Basics.MonadTheory
.


Import MonadNotation.
Local Open Scope monad.
Axiom proof_irrel : forall (P : Prop) (H1 H2 : P), H1 = H2.

Class OrderM (M : Type -> Type) :=
  lem : forall A, M A -> M A -> Prop.

Arguments lem { M OrderM A }.

Infix "<≈" := lem (at level 70).

Section OrderedMonad.
  Context (W : Type -> Type).
  Context {Eq : EqM W}.
  Context {MonadW : Monad W}.
  Context {MonadLawsW : MonadLaws W}.
  Context {OrderM : OrderM W}.

   
  Class OrderedMonad :=
    monot : forall A B w1 w2 (f1 f2 : A -> W B), w1 <≈ w2 ->
                            (forall (a : A), (f1 a) <≈  (f2 a) ) -> (bind w1 f1) <≈ (bind w2 f2).

End OrderedMonad.
Locate "~>".
Class EffectObs (M W : Type -> Type) := 
  obs : M ~> W.


Section EffectObservation.

  Context (M W : Type -> Type).
  Context {MMonad : Monad M}.
  Context {WMonad : Monad W}.
  Context {EqW : EqM W}.
  Context {MonadLawsW : MonadLaws W}.
  Context {WOrder : OrderM W}.
  Context {WOrderLaws : OrderedMonad W}.
  Context (Obs : EffectObs M W). (*
  Definition retm := @ret M _.
  Definition retw := @ret W _.
  Definition bindm := @bind M _.
  Definition bindw := @bind W _.
*)

  Class MonadMorphism :=
    {
      ret_pres : forall A (a : A), obs A (ret a) ≈ ret a; 
      bind_pres : forall A B (m : M A) (f : A -> M B),
          obs _ (bind m f) ≈ bind (obs _ m) (fun a => obs _ (f a))
    }.

End EffectObservation.


Section DijkstraMonad.
  Context (M W : Type -> Type).
  Context {MMonad : Monad M}.
  Context {WMonad : Monad W}.
  Context {EqW : EqM W}.
  Context {MonadLawsW : MonadLaws W}.
  Context {WOrder : OrderM W}.
  Context { WOrderLaws : OrderedMonad W }.
  Context ( Obs : EffectObs M W ).

  Definition DijkstraMonad (A : Type) (w : W A) := 
    { m : M A |  obs A m <≈ w }.

  Definition DijkstraProp (A : Type) (w : W A) (m : M A) :=
    obs A m <≈ w.

End DijkstraMonad.
