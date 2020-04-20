Polymorphic Class Functor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
  { fmap : forall {A B : Type@{d}}, (A -> B) -> F A -> F B }.

Module FunctorNotation.
  Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 52, left associativity).
End FunctorNotation.

