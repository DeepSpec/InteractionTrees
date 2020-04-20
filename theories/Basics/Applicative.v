Class Applicative@{d c} (T : Type@{d} -> Type@{c}) :=
{ pure : forall {A : Type@{d}}, A -> T A
; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 52, left associativity).
End ApplicativeNotation.

