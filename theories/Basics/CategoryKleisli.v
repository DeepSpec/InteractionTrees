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

(** A trick to allow rewriting in pointful contexts. *)
Definition Kleisli_arrow {m a b} : (a -> m b) -> Kleisli m a b := fun f => f.
Definition Kleisli_apply {m a b} : Kleisli m a b -> (a -> m b) := fun f => f.

Definition Kleisli_pure {m} `{Monad m} {a b} (f : a -> b) : Kleisli m a b :=
  fun x => ret (f x).

Class EqM m : Type :=
  eqm : forall a, m a -> m a -> Prop.

Arguments eqm {m _ a}.

Infix "≈" := eqm (at level 70) : kleisli_scope.

(* SAZ: What is the right way to express that [eqm] is an equivalence at every type? 
   SAZ: Also... move to PERs here?
*)
Class EqMProps m `{Monad m} `{EqM m} :=
   {
       eqm_equiv :> forall a, Equivalence (@eqm _ _ a)
   }.


Section Instances.
  Context {m : Type -> Type}.
  Context `{Monad m}.
  Context `{EqM m}.

  Definition pure {a b} (f:a -> b) : Kleisli m a b :=
    fun (x:a) => ret (f x).

  Global Instance Eq2_Kleisli : Eq2 (Kleisli m) :=
    fun _ _ => pointwise_relation _ eqm.

  Global Instance Cat_Kleisli : Cat (Kleisli m) :=
    fun _ _ _ u v x =>
      bind (u x) (fun y => v y).

  Definition map {a b c} (g:b -> c) (ab : Kleisli m a b) : Kleisli m a c :=
     cat ab (pure g).
  
  Global Instance Initial_Kleisli : Initial (Kleisli m) void :=
    fun _ v => match v : void with end.

  Global Instance Id_Kleisli : Id_ (Kleisli m) :=
    fun _ => pure id.

  Global Instance CoprodCase_Kleisli : CoprodCase (Kleisli m) sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  Global Instance CoprodInl_Kleisli : CoprodInl (Kleisli m) sum :=
    fun _ _ => pure inl.

  Global Instance CoprodInr_Kleisli : CoprodInr (Kleisli m) sum :=
    fun _ _ => pure inr.

  (* SAZ: Maybe get rid of the Aloop constraint and move to Iter *)
  (*
  Global Instance Iter_Kleisli `{ALoop m} : Iter (Kleisli m) sum :=
    fun a b (f : Kleisli m a (a + b)) (a0 : a) =>
      aloop (fun ar =>
               match ar with
               | inl a => inl (f a)
               | inr r => inr r
               end) (inl a0) : m b.
  *)
End Instances.
