(* Heterogeneous relation definition, modified from https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)

Section Relation_Definition.

  Definition relationH (A B : Type) := A -> B -> Prop.

  Definition compose1 {A B C} (g : relationH B C) (f : relationH A B) :=
    fun (a : A) (c : C) => forall b, (f a b) /\ (g b c).

  Definition compose2 {A B C} (g : relationH B C) (f : relationH A B) :=
    fun (a : A) (c : C) => exists b, (f a b) /\ (g b c).

End Relation_Definition.

Module RelNotations.
 
  Declare Scope relation_scope.
  Open Scope relation_scope.

  Notation " g ∘ f " := (compose1 g f)
    (at level 40, left associativity) : relation_scope.
  
End RelNotations.


Section General_Properties_of_Relations.

  Variable A B C : Type.
  Import RelNotations. 

  Open Scope relation_scope. 
  Definition reflexive : Prop := forall (x : A) (R : relationH A A), R x x.
  Definition transitive : Prop := forall (x y z : A) (R : relationH A A), R x y -> R y z -> R x z.
  Definition symmetric : Prop := forall (x y : A) (R : relationH A A), R x y -> R y x.
  Definition antisymmetric : Prop := forall (x y : A) (R : relationH A A), R x y -> R y x -> x = y.

  Definition transitiveH : Prop := forall (a : A) (b : B) (c : C) (R1 : relationH A B) (R2 : relationH B C), R1 a b -> R2 b c -> (R2 ∘ R1) a c.

  Definition equiv := reflexive /\ transitive /\ symmetric.

End General_Properties_of_Relations.

Section Sets_of_Relations.

  Variable A : Type.
  
  Record preorder : Prop :=
    { preord_refl : reflexive A; preord_trans : transitive A}.

  Record order : Prop :=
    { ord_refl : reflexive A;
      ord_trans : transitive A;
      ord_antisym : antisymmetric A}.

  Record equivalence : Prop :=
    { equiv_refl : reflexive A;
      equiv_trans : transitive A;
      equiv_sym : symmetric A}.

  Record PER : Prop := {per_sym : symmetric A; per_trans : transitive A}.

End Sets_of_Relations.

Section Relations_of_Relations.

  Definition inclusion {A B} (R1 R2 : relationH A B) : Prop :=
    forall (x : A) (y : B), R1 x y -> R2 x y.

  Definition same_relation {A B} (R1 R2:relationH A B) : Prop :=
    inclusion R1 R2 /\ inclusion R2 R1.

  Definition commut {A B C} (R1 : relationH A B) (R2 : relationH B C): Prop :=
    forall (x : A) (y : B),
      R1 x y -> forall z : C, R2 y z -> exists2 y' : B, R2 y z & R1 x y.

End Relations_of_Relations.


Hint Unfold reflexive transitive antisymmetric symmetric: sets.

Hint Resolve Build_preorder Build_order Build_equivalence Build_PER
  preord_refl preord_trans ord_refl ord_trans ord_antisym equiv_refl
  equiv_trans equiv_sym per_sym per_trans: sets.

Hint Unfold inclusion same_relation commut: sets.
