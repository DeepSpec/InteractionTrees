(** Definition of a Natural Transformation. *)

From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps
     CategoryTheory
     CategoryFunctor
.

Import CatNotations.
Local Open Scope cat_scope.


Section NaturalTransformation.

  Context {obj1 obj2 : Type}
          {C1 : obj1 -> obj1 -> Type}
          {C2 : obj2 -> obj2 -> Type}
          `{Category obj1 C1} `{Category obj2 C2}
          {F : obj1 -> obj2} {G : obj1 -> obj2}
          {eta: forall (a : obj1), C2 (F a) (G a)}.

  Context {f_fmap : forall a b, C1 a b -> C2 (F a) (F b)}
          {g_fmap : forall a b, C1 a b -> C2 (G a) (G b)}
          {F_Functor: Functor C1 C2 F f_fmap}
          {G_Functor: Functor C1 C2 G g_fmap}
  .

  Class NaturalTransformation: Prop :=
      naturality: forall (a b : obj1) (f : C1 a b),
          f_fmap _ _ f >>> eta b ⩯ eta a >>> g_fmap _ _ f
    .

End NaturalTransformation.

Arguments NaturalTransformation {_ _} _ _ _.
