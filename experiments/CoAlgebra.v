(* A theory of final coalgebras. *)
(* Someone probably already wrote a better version of this. *)

From Coq Require Import
     Relations RelationClasses.

From ExtLib.Structures Require Import
     Functor Applicative Monad.

Set Implicit Arguments.
Set Contextual Implicit.

(* [nu F] is the final coalgebra of a functor [F]. *)
(* A coinductive type can be seen as a final coalgebra of a functor
   [F], denoted [nu F]. This should be equivalent to the sigma type
   [{ St : Type & St * (St -> F St) }], which thus provides one
   possible definition of [nu].
   For [itree], this functor [F] is [output], defined below. *)
Polymorphic Variant nu (F : Type -> Type) : Type :=
| Nu : forall St, St -> (St -> F St) -> nu F.

Module Nu.

Definition type {F} (n : nu F) : Type :=
  match n with
  | @Nu _ St _ _ => St
  end.

Definition state {F} (n : nu F) : type n :=
  match n with
  | Nu s _ => s
  end.

Definition step {F} (n : nu F) : type n -> F (type n) :=
  match n with
  | Nu _ f => f
  end.

Definition step_once {F} (n : nu F) : F (type n) :=
  match n with
  | Nu s f => f s
  end.

Lemma step_state {F} (m : nu F) :
  step m (state m) = step_once m.
Proof. destruct m; reflexivity. Qed.

(* A coalgebra of a functor [F : Type -> Type] is actually a pair
   of a type [A : Type] together with a function [A -> F A].
   This is the morphism which makes [nu F : Type] an [F]-coalgebra. *)
Definition run {F} `{Functor F} : nu F -> F (nu F)
  := fun n =>
  match n with
  | Nu s f => fmap (fun s' => Nu s' f) (f s)
  end.

Definition eq {F}
           (eq_F : forall A B, (A -> B -> Prop) ->
                               F A -> F B -> Prop) :
  nu F -> nu F -> Prop :=
  fun n1 n2 =>
    exists (eq0 : Nu.type n1 -> Nu.type n2 -> Prop),
      eq0 (Nu.state n1) (Nu.state n2) /\
      (forall s1 s2, eq0 s1 s2 ->
                     eq_F _ _ eq0 (Nu.step n1 s1) (Nu.step n2 s2)).

End Nu.

Record coalgebra F : Type := {
  carrier :> Type;
  coalgebra_ : carrier -> F carrier;
}.

Definition nu_coalgebra {F} `{Functor F} : coalgebra F := {|
  carrier := nu F;
  coalgebra_ := Nu.run;
|}.

Module Morphism.

(* A coalgebra morphism. *)
Definition lawful {F} `{Functor F}
           (A B : coalgebra F) (morphism : A -> B) : Prop :=
  forall a : A,
    coalgebra_ B (morphism a) = fmap morphism (coalgebra_ A a).

End Morphism.

Definition nu_morphism {F} (A : coalgebra F) : A -> nu F := fun a =>
  @Nu _ (carrier A) a (coalgebra_ A).

(* universe inconsistency! *)
(*
Polymorphic Definition nu_lawful_morphism {F} `{Functor F}
            (A : coalgebra F) :
  Morphism.lawful A nu_coalgebra (nu_morphism A).
*)

(* The universal property of coalgebras *)
(* Need a more general notion of equivalence on [F]. *)
(*
Theorem nu_final {F} `{Functor F} {A B : coalgebra F}
        (f : A -> B)
        (lawful_f : Morphism.lawful A B f) :
  forall a,
    nu_morphism A a = nu_morphism B (f a).
Proof.
Abort.
*)

Module Type Category.
Parameter object : Type.
Parameter arrow : object -> object -> Type.
Delimit Scope cat_scope with cat.
Open Scope cat.
Infix "-->" := arrow (at level 40) : cat_scope.
Parameter eq_arrow : forall A B,
    (A --> B) -> (A --> B) -> Prop.
Parameter compose : forall A B C,
    (A --> B) -> (B --> C) -> (A --> C).
Infix "*" := compose : cat_scope.
Infix "=~" := eq_arrow (at level 60) : cat_scope.
Parameter id : forall A, A --> A.
Parameter left_id : forall A B (a : A --> B), id * a =~ a.
Parameter right_id : forall A B (a : A --> B), a * id =~ a.
Parameter compose_assoc :
  forall A B C D
         (a : A --> B) (b : B --> C) (c : C --> D),
    (a * b) * c =~ a * (b * c).
End Category.

Module Type EndoFunctor (Cat : Category).
Import Cat.
Parameter F : object -> object.
Parameter F_map : forall A B, (A --> B) -> (F A --> F B).
Parameter F_id : forall A, F_map (@id A) =~ id.
Parameter F_compose : forall A B C (a : A --> B) (b : B --> C),
    F_map (a * b) =~ F_map a * F_map b.
End EndoFunctor.

Module CoAlgebra (Cat : Category) (Fun : EndoFunctor Cat).
Import Cat Fun.

Record coalgebra : Type := {
  carrier :> object;
  ops : carrier --> F carrier;
}.

Record ca_morphism (A B : coalgebra) := {
  morphism :> A --> B;
  comm : ops A * F_map morphism =~ morphism * ops B;
}.

Infix "~~>" := ca_morphism (at level 40) : cat_scope.
End CoAlgebra.

Module Type FinalCoAlgebra (Cat : Category) (Fun : EndoFunctor Cat).
Import Cat Fun.
Module Import CA := CoAlgebra Cat Fun.
Parameter nu_F : coalgebra.
Parameter ana : forall (A : coalgebra), A ~~> nu_F.
Parameter ana_final : forall A (m : A ~~> nu_F), m =~ ana.
End FinalCoAlgebra.

Module SetoidCategory <: Category.

Module Import Types.

Record object : Type := {
  carrier :> Type;
  equiv : relation carrier;
  equiv_equiv : Equivalence equiv;
}.

Notation "a == b" := (equiv _ a b) (at level 50).

Record arrow (A B : object) : Type := {
  apply :> A -> B;
  equiv_apply : forall a a' : A, a == a' -> apply a == apply a';
}.

End Types.

Definition object := object.
Definition arrow := arrow.

Delimit Scope cat_scope with cat.
Open Scope cat.
Infix "-->" := arrow (at level 40) : cat_scope.

Definition eq_arrow (A B : object)
           (f : A --> B) (g : A --> B) : Prop :=
  forall a a', a == a' -> f a == g a'.

Definition compose (A B C : object)
           (f : A --> B) (g : B --> C) : A --> C := {|
    apply := fun a => g (f a);
    equiv_apply := fun _ _ Eaa' =>
      equiv_apply _ _ _ (equiv_apply _ _ _ Eaa');
  |}.

Infix "*" := compose : cat_scope.
Infix "=~" := eq_arrow (at level 60) : cat_scope.

Definition id A : A --> A := {|
    apply := fun a => a;
    equiv_apply := fun _ _ Eaa' => Eaa';
  |}.

Lemma left_id A B (a : A --> B) : id * a =~ a.
Proof.
  intros x x'; simpl; apply a; auto.
Qed.

Lemma right_id A B (a : A --> B) : a * id =~ a.
Proof.
  intros x x'; simpl; apply a; auto.
Qed.

Lemma compose_assoc A B C D
      (a : A --> B) (b : B --> C) (c : C --> D) :
    (a * b) * c =~ a * (b * c).
Proof.
  intros x x' Exx'; simpl; apply c, b, a; auto.
Qed.

End SetoidCategory.
