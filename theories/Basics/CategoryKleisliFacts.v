From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Basics.Function.

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Notation Proper_bind m a b :=
  (@Proper (m a%type -> (a -> m b) -> m b)
           (eqm ==> pointwise_relation _ eqm ==> eqm)
           bind).

Instance Proper_cat_Kleisli m `{Monad m} `{EqM m}
         (Proper_bind : forall a b, Proper_bind m a b)
         {a b c}
  : @Proper (Kleisli m a b -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  unfold cat, Cat_Kleisli.
  apply Proper_bind; auto.
Qed.

Instance Proper_case_Kleisli m `{Monad m} `{EqM m}
         {a b c}
  : @Proper (Kleisli m a c -> Kleisli m b c -> _)
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro; destruct (_ : _ + _); cbn; auto.
Qed.

Notation Proper_aloop m a b :=
  (@Proper ((a -> m (sum a b)%type) -> (a -> m b%type))
           (pointwise_relation _ eqm ==> pointwise_relation _ eqm)
           bind).

Instance Proper_iter_Kleisli m `{EqM m} `{Monad m} `{ALoop m}
         {a b}
  : @Proper (Kleisli m a (a + b) -> Kleisli m a b)
            (eq2 ==> eq2) iter.
Proof.
Admitted.
