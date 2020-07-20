From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.

Definition rel A := A -> A -> Prop.

(* Definition of [typ] as a class whose carrier is exposed as a parameter.
 *)
Class typ (A: Type): Type :=
  equal : rel A.
Arguments equal {A T}: rename.
Notation "'equalE' T" := (@equal _ T) (at level 5).

(* Our usual [Type]s are recovered by setting the relation to [eq] *)
Instance typ_eq (A: Type) : typ A := @eq A.

(* A [typ A] can be thought as the sub-type of elements of [A] over which [equal] is reflexive *)
Definition contains {A} (T : typ A) (a:A) : Prop := equal a a.
Notation "a ∈ T" := (contains T a) (at level 75).

(* In particular, all elements are in their [typ_eq] *)
Fact type_eq_full : forall A (a: A), a ∈ (typ_eq A).
Proof.
  reflexivity.
Qed.  

(** ** top, bot
    Given a carrier [A], two particular [typ A] can be defined: [top] where no elements are distinguished,
    and [bot] which is basically the empty type seen as a subtype of [A]
    (no reflexive elements for the relation, so no elements in [bot A])
 *)
Definition top_typ A : typ A := fun a b : A => True.
Definition bot_typ A : typ A := fun a b : A => False.

(* All elements are also in [top_typ] *)
Fact top_typ_full : forall A (a: A), a ∈ (top_typ A).
Proof.
  reflexivity.
Qed.  

(* But none are in [bot_typ] *)
Fact bot_typ_empty : forall A (a: A), ~a ∈ (bot_typ A).
Proof.
  intros ? ? abs; inversion abs.
Qed.  

(** ** prod
    Cartesian product of two [typ].
    In this approach, we have a lot of type annotations, but the term is straightforward to write.
 *)
Instance prod_typ {A B} (TA: typ A) (TB: typ B) : typ (A * B) :=
  fun '(pa,pb) '(qa,qb) => equal pa qa /\ equal pb qb.
Notation "e × f" := (prod_typ e f) (at level 70).

(* We indeed picked the most general product of typs in that all pairs of elements _belonging_ to the crossed typs are in: *)
Fact prod_typ_gen : forall A B TA TB (a: A) (b : B),
    a ∈ TA -> b ∈ TB -> (a,b) ∈ TA × TB.
Proof.
  intros * INA INB; split; [apply INA | apply INB].
Qed.

(** ** arr
    Exponential of two [typ].
 *)
Definition arr_typ {A} {B} (TA: typ A) (TB: typ B) : typ (A -> B) :=
  fun f g => forall a1 a2, equal a1 a2 -> equal (f a1) (g a2).
Notation "e ~~> f" := (arr_typ e f) (at level 60).

(* Elements in the arrow [typ] are exactly the functions respecting the equivalences *)
Fact arr_typ_gen : forall A B TA TB (f: A -> B),
     f ∈ TA ~~> TB <-> Proper (equalE TA ==> equalE TB) f.
Proof.
  intros *; split; intros H; apply H.
Qed.

