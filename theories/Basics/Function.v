(** * The Category of Functions

  Definitions to reason about Coq functions [A -> B] categorically.

 *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category.

Import CatNotations.
Local Open Scope cat_scope.

(* end hide *)

Definition Fun (A B : Type) : Type := A -> B.

Definition applyFun {A B : Type} (f : Fun A B) : A -> B := f.

(** Extensional function equality *)
Instance eeq : Eq2 Fun :=
  fun A B f g => forall a : A, f a = g a.

Instance subrelation_eeq_eqeq {A B} :
  @subrelation (A -> B) eq2 (@eq A ==> @eq B)%signature := {}.
Proof. congruence. Qed.

Instance Equivalence_eeq {A B} : @Equivalence (Fun A B) eq2.
Proof. constructor; congruence. Qed.

Instance Id_Fun : Id_ Fun :=
  fun A => fun a => a.

Instance Cat_Fun : Cat Fun :=
  fun A B C f g => fun a => g (f a).

Instance Proper_cat {A B C : Type} :
  @Proper (Fun A B -> Fun B C -> Fun A C) (eq2 ==> eq2 ==> eq2) cat.
Proof. cbv; congruence. Qed.

Instance cat_Fun_CatIdL : CatIdL Fun.
Proof. red; reflexivity. Qed.

Instance cat_Fun_CatIdR : CatIdR Fun.
Proof. red; reflexivity. Qed.

Instance cat_Fun_assoc : AssocCat Fun.
Proof. red; reflexivity. Qed.

(** * [void] as an initial object. *)

Instance Initial_void : Initial Fun void :=
  fun _ v => match v : void with end.

Instance InitialObject_void : InitialObject Fun void :=
  fun _ _ v => match v : void with end.

(** * The [sum] coproduct. *)

(** ** Coproduct elimination *)

Instance sum_elim : CoprodElim Fun sum :=
  fun {A B C} (f : A -> C) (g : B -> C) (x : A + B) =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

Instance sum_inl : CoprodInl Fun sum := @inl.
Instance sum_inr : CoprodInr Fun sum := @inr.

(** ** Equational theory *)

Instance eeq_sum_elim {A B C} :
  @Proper (Fun A C -> Fun B C -> Fun (A + B) C)
          (eq2 ==> eq2 ==> eq2) elim.
Proof. cbv; intros; subst; destruct _; auto. Qed.

(** * Bijections *)

Class Iso {A B} (f : A -> B) (f' : B -> A) : Type :=
  { iso_ff' : forall a, f' (f a) = a;
    iso_f'f : forall b, f (f' b) = b;
  }.

Instance Iso_id {A} : Iso (id_ A) (id_ A) := {}.
Proof. all: auto. Qed.

Instance Iso_sum_assoc_l {A B C} : @Iso (A + (B + C)) _ assoc_l assoc_r := {}.
Proof.
  - intros. destruct a as [| []]; auto.
  - intros. destruct b as [[] |]; auto.
Qed.

Definition Iso_inv {A B} (f : A -> B) f' : Iso f f' -> Iso f' f.
Proof.
  intros []; split; auto.
Qed.

Instance Iso_sum_assoc_r {A B C} : @Iso ((A + B) + C) _ assoc_r assoc_l.
Proof.
  apply Iso_inv; typeclasses eauto.
Qed.

Instance Iso_compose {A B C} (f : A -> B) (g : B -> C)
         {f' : B -> A} `{Iso _ _ f f'}
         {g' : C -> B} `{Iso _ _ g g'} : Iso (f >=> g) (g' >=> f') := {}.
Proof.
  all: intro a; cbv; rewrite ?iso_ff', ?iso_f'f; auto.
Qed.

Instance Iso_sum_comm {A B} : @Iso (A + B) _ swap swap := {}.
Proof. all: intros []; auto. Qed.

Instance Iso_sum_bimap {A B C D} (f : A -> B) (g : C -> D)
         {f' : B -> A} `{Iso _ _ f f'}
         {g' : D -> C} `{Iso _ _ g g'} :
  Iso (bimap f g) (bimap f' g') := {}.
Proof.
  all: intros []; cbv; rewrite ?iso_ff', ?iso_f'f; auto.
Qed.
