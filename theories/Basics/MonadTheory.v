(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function.
(* end hide *)

Set Primitive Projections.

Class EqM (m:Type -> Type) : Type :=
  eqm : forall a, m a -> m a -> Prop.

Class EqMProps (m:Type -> Type) `{Monad m} `{EqM m} :=
      eqm_equiv :> forall a, Equivalence (eqm a).

Arguments eqm {m _ _}.
Infix "≈" := eqm (at level 70) : monad_scope.

Section Laws.

  Context (m : Type -> Type).
  Context {EqM : @EqM m}.
  Context {Mm : Monad m}.
  Context {EqMP : @EqMProps m _ EqM}.

  Local Open Scope monad_scope.
  
  (* SAZ: Where should these next two typeclasses live? *)
  (* SAZ: Where should the instances for itree be declared? *)
  Class MonadLaws :=
    {
      bind_ret :> forall a b (f : a -> m b) (x : a), bind (ret x) f ≈ f x
    ; ret_bind :> forall a (x : m a), bind x (fun y => ret y) ≈ x
    ; bind_bind :> forall a b c (x : m a) (f : a -> m b) (g : b -> m c), bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    }.                                             

  (* This should be just a notation *)
  Class MonadProperOps :=
      Proper_bind :> forall {a b},
          (@Proper (m a%type -> (a -> m b) -> m b)
           (eqm ==> pointwise_relation _ eqm ==> eqm)
           bind).

End Laws.
Arguments bind_ret {m _ _ _}.
Arguments ret_bind {m _ _ _}.
Arguments bind_bind {m _ _ _}.
