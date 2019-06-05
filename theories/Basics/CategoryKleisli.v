From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function.

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Definition Kleisli m a b : Type := a -> m b.

Class EqM m : Type :=
  eqm : forall a, m a -> m a -> Prop.

Arguments eqm {m _ a}.

Notation "≈" := eqm (at level 40) : kleisli_scope.

Instance Eq2_Kleisli m `{EqM m} : Eq2 (Kleisli m) :=
  fun _ _ => pointwise_relation _ eqm.

Instance Cat_Kleisli m `{Monad m} : Cat (Kleisli m) :=
  fun _ _ _ u v x =>
    bind (u x) (fun y => v y).

Instance Id_Kleisli m `{Monad m} : Id_ (Kleisli m) :=
  fun _ x => ret x.

Instance CoprodCase_Kleisli m : CoprodCase (Kleisli m) sum :=
  fun _ _ _ l r => case_sum _ _ _ l r.

Instance CoprodInl_Kleisli m `{Monad m} : CoprodInl (Kleisli m) sum :=
  fun _ _ x => ret (inl x).

Instance CoprodInr_Kleisli m `{Monad m} : CoprodInr (Kleisli m) sum :=
  fun _ _ x => ret (inr x).

Instance Iter_Kleisli m `{Monad m} `{ALoop m} : Iter (Kleisli m) sum :=
  fun a b (f : Kleisli m a (a + b)) (a0 : a) =>
    aloop (fun ar =>
      match ar with
      | inl a => inl (f a)
      | inr r => inr r
      end) (inl a0) : m b.
