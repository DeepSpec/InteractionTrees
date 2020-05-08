From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryTheory
     CategoryFunctor.

Import Carrier.
Import CatNotations.
Local Open Scope cat_scope.

(* Monads are monoid in the category of endofunctors.
 * For ease of use, we define a monad using programmatic convention of "ret" and
 * "bind", and the monad laws are Haskell-like (bind unit and composition laws). *)
Section Monad.

  Context {obj : Type} {C : obj -> obj -> Type}
          `{Eq2 _ C} `{Id_ _ C} `{Cat _ C}.

(* IY: Do we want to show that a monad is a monoid in the category of endofunctors?
       We don't *need* these definitions here for stating the monad laws. *)
(* {bif : binop obj} *)
(* {fmap : forall a b, C a b -> C (M a) (M b)} *)
(* {endofunctor : Functor C C M (@fmap)} *)

  (* A monad is defined with an endofunctor. *)
  Class Monad (M : obj -> obj) : Type :=
  {
    ret {a} : C a (M a);
    bind {a b} (f : C a (M b)) : C (M a) (M b)
  }.

  Context {M : obj -> obj}.

  (* Monad laws, annotated with equivalent Haskell-like monad laws in comments. *)
  Class MonadLaws `(Monad M) : Prop :=
  {
    (* bind (ret x) f = f a *)
    bind_ret_l {a b} (f : C a (M b)): ret >>> bind f ⩯ f;

    (* bind ma (fun x => ret x) = ret x *)
    bind_ret_r {a} : bind ret ⩯ id_ (M a);

    (* bind (bind ma f) g = bind ma (fun y => bind (f y) g) *)
    bind_bind {a b c} (f : C a (M b)) (g : C b (M c)) :
      bind f >>> bind g ⩯ bind (f >>> bind g);

    bind_proper {a b} :> Proper (eq2 ==> eq2) (@bind _ _ a b)
  }.

End Monad.

Arguments Monad : clear implicits.
Arguments Monad {_} C M.
Arguments MonadLaws {_ _ _ _ _ _} monad : rename.

Section MonadFunctor.

  Context {obj : Type} {C : obj -> obj -> Type}
          `{Eq2 _ C} `{Id_ _ C} `{Cat _ C} `{Category _ C}.

  Context `{forall (a b : obj), PER (@eq2 obj C _ a b)}.
  Context (M : obj -> obj) (CM : Monad C M) (ML : MonadLaws CM).

  Instance Monad_Functor : @Functor _ _  C C M.
    red. intros. refine (bind (X >>> ret)).
  Defined.

  Instance Monad_FunctorLaws : FunctorLaws Monad_Functor.
  constructor.
  - intros a. cbn. unfold fmap, Monad_Functor.
    rewrite cat_id_l. apply bind_ret_r.
  - intros a b c f g.
  Admitted.

End MonadFunctor.
