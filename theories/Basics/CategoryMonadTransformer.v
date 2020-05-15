From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryTheory
     CategoryFunctor
     CategoryMonad
     CategoryNaturalTransformation
.

Import CatNotations.
Local Open Scope cat_scope.

Section MonadTransformer.

  Context {obj: Type}
          {C: obj-> obj-> Type}
          `{Category_C: Category obj C}
          {M : obj -> obj} {N : obj -> obj}
  .

  (** *Monad Transformer Definition *)

  (* A monad transformer is a natural transformation on two monads with two
   * additional functor laws over lift. This is also known as a [monad morphism],
   * but without additional categorical formalism over our [CategoryMonad.v], it is
   * cumbersome to try to define the functor laws categorically. *)

  Context {M_Monad : Monad C M} {N_Monad : Monad C N}
          {M_ML : MonadLaws M_Monad} {N_ML : MonadLaws N_Monad}.

  (* "lift" should be equivalent to the [eta] in a natural transformation. *)
  Context {lift : forall a, C (M a) (N a)}.

  Arguments ret : clear implicits.
  Arguments ret {_ _} _ {_} _.

  Arguments bind : clear implicits.
  Arguments bind {_ _} _ {_ _ _}.

  Arguments monad_fmap {_ _ _} _ {_}.

  Class MonadTransformer :=
    {
      lift_NT :> NaturalTransformation C C M N (monad_fmap M) (monad_fmap N) lift;

      (* lift . return = lift *)
      lift_ret : forall A, ret M A >>> lift A ⩯ ret N A;

      (* lift (`bind` ma k) = `bind` (lift ma) (lift . k) *)
      lift_bind :
        forall (a b: obj) (k : C a (M b)),
          bind M k >>> lift b ⩯ lift a >>> bind N (k >>> lift b)
    }.

  Context `{forall (a b : obj), PER (@eq2 obj C _ a b)}.

  (* TODO Give StateT Instance of MonadTransformer. *)
End MonadTransformer.
