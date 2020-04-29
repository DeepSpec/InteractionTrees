From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.

Definition rel A := A -> A -> Prop.

(**
   Definition of [typ] as a class whose carrier is internal to the class.
   In contrast to [Typ_Class1], we often need to use the constructor explicitly to build values
   of the class since although we can define a coercion via [typ], the coercion requires the
   type checker to see the relation considered explicitly as a [rel A] and not a [A -> A -> Prop].

   _Warning_: you want to be a bit careful with what goes on behind the scene with this version.
   Jumping ahead to the definition of the product, you can readily write the following:
   Instance prod_typ (TA TB: typ) : typ :=
     Typ (fun '(pa,pb) '(qa,qb) => equal pa qa /\ equal pb qb).
   But you won't get what you're looking for!
 *)
Class typ : Type :=
  Typ {
      Ty : Type; 
      equal : rel Ty
    }.
Arguments equal {T}: rename.
Arguments Typ {Ty}.
Notation "'equalE' T" := (@equal T) (at level 5).
(* This coercion allows us to write [(a: T)] to mean [(a : Ty T)] *)
Coercion Ty  : typ >-> Sortclass.
Coercion Typ : rel >-> typ.

(* Our usual [Type]s are recovered by setting the relation to [eq] *)
Instance typ_eq (A: Type) : typ := Typ (@eq A).
(* Note that we could have used the coercion instead of the constructor as follows:
Instance typ_eq (A: Type) : typ := (@eq A): rel A.
But that the simplest version cannot be inferred:
Instance typ_eq (A: Type) : typ := @eq A.
*)

(* A [typ A] can be thought as the sub-type of elements of [A] over which [equal] is reflexive *)
Definition contains (T : typ) (a:T) : Prop := equal a a.
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
Definition top_typ A : typ := Typ (fun a b : A => True).
Definition bot_typ A : typ := Typ (fun a b : A => False).

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
Instance prod_typ (TA TB: typ) : typ :=
  Typ (fun (p q: TA * TB) => equal (fst p) (fst q) /\ equal (snd p) (snd q)).
Notation "e × f" := (prod_typ e f) (at level 70).

(* We indeed picked the most general product of typs in that all pairs of elements _belonging_ to the crossed typs are in: *)
Fact prod_typ_gen : forall (TA TB: typ) (a: TA) (b : TB),
    a ∈ TA -> b ∈ TB -> (a,b) ∈ TA × TB.
Proof.
  intros * INA INB; split; [apply INA | apply INB].
Qed.

(** ** arr
    Exponential of two [typ].
 *)
Definition arr_typ (TA TB: typ) : typ :=
  Typ (fun (f g: TA -> TB) => forall a1 a2, equal a1 a2 -> equal (f a1) (g a2)).
Notation "e ~~> f" := (arr_typ e f) (at level 60).

(* Elements in the arrow [typ] are exactly the functions respecting the equivalences *)
Fact arr_typ_gen : forall (TA TB: typ) (f: TA -> TB),
     f ∈ TA ~~> TB <-> Proper (equalE TA ==> equalE TB) f.
Proof.
  intros *; split; intros H; apply H.
Qed.

