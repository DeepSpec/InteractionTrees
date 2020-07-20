(** * Definition of a functor *)

From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     CategoryOps.

Import CatNotations.
Local Open Scope cat_scope.

Section Functor.

  Context
    {obj1 obj2 : Type}
    {C1 : obj1 -> obj1 -> Type}
    {C2 : obj2 -> obj2 -> Type}
    `{Eq2 _ C1} `{Id_ _ C1} `{Cat _ C1}
    `{Eq2 _ C2} `{Id_ _ C2} `{Cat _ C2}
    (F : obj1 -> obj2)
    (fmap : forall a b, C1 a b -> C2 (F a) (F b)).

  Arguments fmap {_ _}.

  Class Fmap_Id : Prop :=
    fmap_id : forall a, fmap (id_ a) ⩯ id_ (F a).

  Class Fmap_Cat : Prop :=
    fmap_cat : forall a b c (f : C1 a b) (g : C1 b c),
          fmap (cat f g) ⩯ cat (fmap f) (fmap g).

  Class Fmap_Proper : Prop :=
    fmap_proper : forall a b, Proper (eq2 ==> eq2) (@fmap a b).

  Class Functor : Prop :=
    {
      functor_fmap_id :> Fmap_Id;
      functor_fmap_cat :> Fmap_Cat;
      functor_fmap_proper :> Fmap_Proper
    }.

End Functor.

Arguments Functor : clear implicits.
Arguments Functor {_ _} _ _ {_ _ _ _ _ _ } F fmap.

Section FunctorId.

  Context
    {obj : Type} {C1 C2 : obj -> obj -> Type}
    `{Eq2 _ C1} `{Id_ _ C1} `{Cat _ C1}
    `{Eq2 _ C2} `{Id_ _ C2} `{Cat _ C2}
    `{Functor_id : Functor _ _ C1 C2 (fun x => x)}
  .

  Lemma fmap_id0 : forall a, fmap _ _ (id_ a) ⩯ id_ a.
  Proof. apply functor_fmap_id. eauto. Qed.

  Lemma fmap_cat0 : forall a b c (f : C1 a b) (g : C1 b c),
      fmap _ _ (f >>> g) ⩯ fmap _ _ f >>> fmap _ _ g.
  Proof. apply functor_fmap_cat. eauto. Qed.

End FunctorId.
