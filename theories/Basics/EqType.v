From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
.

Import ProperNotations.

Definition rel A := A -> A -> Prop.


(* Definition of "Type with equality", inspired by Eddy Westbrook and Gregory Malecha's OrderedType.
 * https://github.com/eddywestbrook/predicate-monads/blob/master/theories/CtxFuns/OrderedType.v
 *)
Class EqType (A : Type) : Type :=
  {
    equal : rel A;
    equal_PER :> PER equal
  }.
Notation "x =t= y" := (equal x y) (no associativity, at level 70).

(* Our usual [Type]s are recovered by setting the relation to [eq] *)
Instance typ_eq (A : Type) : EqType A := {| equal := @eq A |}.

(* Note that we could have used the coercion instead of the constructor as follows:
Instance typ_eq (A: Type) : typ := (@eq A): rel A.
But that the simplest version cannot be inferred:
Instance typ_eq (A: Type) : typ := @eq A.
*)

(* A [typ A] can be thought as the sub-type of elements of [A] over which [equal] is reflexive *)
Definition contains `{A : Type} (T : EqType A) (a : A) : Prop := equal a a.
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
Instance top_PER {A} : PER (fun a b : A => True).
Proof.
  split; eauto.
Qed.

Instance bot_PER {A} : PER (fun a b : A => False).
Proof.
  split; eauto.
Qed.

Definition top_typ A : EqType A := {| equal := fun a b : A => True |}.
Definition bot_typ A : EqType A := {| equal := fun a b : A => False |}.

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

Instance pair_PER (A B:Type) (RA : rel A) `{PER A RA} (RB : rel B) `{PER B RB}:
  PER (fun (p q: A * B) => RA (fst p) (fst q) /\ RB (snd p) (snd q)).
Proof.
  split.
  repeat red. intros x y (H1 & H2). split; symmetry; assumption.
  repeat red. intros x y z (H1 & H2) (H3 & H4). split; eapply transitivity; eauto.
Qed.

Instance prod_typ {A B} (TA : EqType A) (TB: EqType B) : EqType (A * B) :=
  {| equal := (fun (p q: A * B) => equal (fst p) (fst q) /\ equal (snd p) (snd q)) |}.
Notation "e × f" := (prod_typ e f) (at level 70).

(* We indeed picked the most general product of typs in that all pairs of elements _belonging_ to the crossed typs are in: *)
Fact prod_typ_gen {A B} : forall (TA : EqType A) (TB: EqType B) (a : A) (b : B),
    (a ∈ TA /\ b ∈ TB) <-> (a,b) ∈ TA × TB.
Proof.
  intros *; split; (intros [INA INB]; split; [apply INA | apply INB]).
Qed.

Instance fun_PER (A B:Type) (RA : rel A) `{PER A RA} (RB : rel B) `{PER B RB}
  : PER (fun (f g: A -> B) => forall a1 a2, RA a1 a2 -> RB (f a1) (g a2)).
Proof.
  split.
  - repeat red. intros x y H1 a1 a2 H2.  symmetry. apply H1. symmetry. apply H2.
  - repeat red. intros x y z H1 H2 a1 a2 H3.
    eapply transitivity. apply H1. apply H3. apply H2. eapply transitivity. symmetry. apply H3. apply H3.
Qed.

(** ** arr
    Exponential of two [typ].
 *)
Definition arr_typ {A B} (TA : EqType A) (TB: EqType B) : EqType (A -> B) :=
  {| equal := (fun (f g: A -> B) => forall a1 a2, equal a1 a2 -> equal (f a1) (g a2)) |} .
Notation "e ~~> f" := (arr_typ e f) (at level 60).

(* Elements in the arrow [typ] are exactly the functions respecting the equivalences *)
Fact arr_typ_gen {A B} : forall (TA : EqType A) (TB: EqType B) (f: A -> B),
     f ∈ TA ~~> TB <-> Proper (@equal A TA ==> @equal B TB) f.
Proof.
  intros *; split; intros H; apply H.
Qed.


Arguments equal _ {_}.
(*
    Typ forms a Category. We are working in a category C, where:

    Objects:    Typ
    Hom (Typ eqA) (Typ eqB) := { f | Proper (eqA ==> eqB) f }
    ID in Hom (Typ eqA) (Typ eqA) := fun (x:A) => x
*)
Section TypCat.

  Record TypFun A B `{EqType A} `{EqType B} :=
    {
      tfun_app : A -> B;
      tfun_Proper : Proper (equal A ==> equal B) tfun_app
    }.

  Arguments tfun_app {_ _ _ _} !t _.
  Arguments tfun_Proper [_ _ _ _] _ _ _ _.


  Notation "A '-t->' B" :=
    (TypFun A B) (right associativity, at level 99).

  Notation "x @@ y" :=
    (tfun_app x y) (left associativity, at level 20).

  (* Non-dependent function ordered type. *)
  Program Instance TArrow A B `{EqType A} `{EqType B} : EqType (A -t-> B) :=
    {|
      equal :=
        fun f g =>
          forall a1 a2, a1 =t= a2 -> (f @@ a1) =t= (g @@ a2)
    |}.
  Next Obligation.
    repeat constructor; repeat intro.
    symmetry. apply H1. symmetry. apply H2.
    transitivity (tfun_app y a2).
    apply H1. apply H3.
    apply H2. transitivity a1. symmetry. apply H3.
    apply H3.
  Defined.

  Context {A : Type}.

  (* Instance eq2_typ_proper : Eq2 (@TypFun A A) := *)
  (*   (fun a b tp tp' => *)
  (*      let f := proj1_sig tp in *)
  (*      let g := proj1_sig tp' in *)
  (*      forall x y, x ∈ a -> y ∈ a -> equal A x y -> equal A (f x) (g y)). *)

  (* Lemma id_ok: forall (TA : typ), *)
  (*     Proper (equalE TA ==> equalE TA) (fun x => x). *)
  (* Proof. *)
  (*   intros. *)
  (*   repeat red. tauto. *)
  (* Qed. *)

  (* Lemma compose: forall (TA TB TC : typ) (f : TA -> TB) (g : TB -> TC) *)
  (*     (P1: Proper (equalE TA ==> equalE TB) f) *)
  (*     (P2: Proper (equalE TB ==> equalE TC) g), *)
  (*     Proper (equalE TA ==> equalE TC) (fun x => g (f x)). *)
  (* Proof. *)
  (*   intros TA TB TC f g P1 P2. *)
  (*   repeat red. *)
  (*   intros. *)
  (*   apply P2. apply P1. assumption. *)
  (* Qed. *)

  (* Instance id_typ_proper : Id_ typ_proper := *)
  (*   fun TA : typ => *)
  (*   exist (fun f : TA -> TA => Proper (equalE TA ==> equalE TA) f) *)
  (*     (fun x : TA => x) (id_ok TA). *)

  (* Instance cat_typ_proper : Cat typ_proper := *)
  (*   fun (a b c : typ) (TA : typ_proper a b) (TB : typ_proper b c) => *)
  (*   exist (fun f : a -> c => Proper (equalE a ==> equalE c) f) *)
  (*     (fun x : a => (` TB) ((` TA) x)) *)
  (*     (compose a b c (` TA) (` TB) (proj2_sig TA) (proj2_sig TB)). *)

  (* Instance cat_IdL_typ_proper : CatIdL typ_proper. *)
  (*   repeat intro. destruct f. cbn. apply p. assumption. *)
  (* Defined. *)

  (* Instance cat_IdR_typ_proper : CatIdR typ_proper. *)
  (*   repeat intro. destruct f. cbn. apply p. assumption. *)
  (* Defined. *)

  (* Instance cat_assoc_typ_proper : CatAssoc typ_proper. *)
  (*   refine (fun a b c d TA TB TC => _). repeat intro. *)
  (*   destruct TA, TB, TC. eapply p1. eapply p0. eapply p. assumption. *)
  (* Defined. *)

  (* Instance proper_typ_proper (a b c : typ) : Proper ((@eq2 typ _ _ a b) ==> (@eq2 typ _ _ b c) ==> (@eq2 typ _ _ a c)) (cat). *)
  (*   repeat intro. *)
  (*   destruct x, y, x0, y0. unfold eq2, eq2_typ_proper in H0. *)
  (*   cbn in H0. unfold eq2, eq2_typ_proper in H. cbn in H. cbn. *)
  (*   specialize (H x1 y1 H1 H2 H3). *)
  (*   specialize (H0 (x x1) (x2 y1)). *)
  (*   apply H0. 3 : apply H. apply p. apply H1. apply p0. apply H2. *)
  (* Defined. *)

  (* Global Instance category_typ_proper : Category typ_proper. *)
  (*   constructor; try typeclasses eauto. *)
  (* Defined. *)

End TypCat.
