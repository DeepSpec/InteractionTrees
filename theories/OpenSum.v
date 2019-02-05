(** Sums of effects *)

(* TODO Swap sums (changed associativity). *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib.Structures Require Import
     Monoid.

From ITree Require Import
     Core.

Variant void : Type := .

(** Sums for extensible event types. *)

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inlE (_ : E1 X)
| inrE (_ : E2 X).

Variant emptyE : Type -> Type := .

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

Definition swap1 {A B : Type -> Type} {X : Type}
           (ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inlE a => inrE a
  | inrE b => inlE b
  end.

Definition bimap_sum1 {A B C D : Type -> Type} {X Y : Type}
           (f : A X -> C Y) (g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inlE a => inlE (f a)
  | inrE b => inrE (g b)
  end.

Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.


(* Automatic application of commutativity and associativity for sums.
   TODO: This is still quite fragile and prone to
   infinite instance resolution loops.
 *)

Class Convertible (A B : Type -> Type) :=
  { convert : forall {X}, A X -> B X }.

(* Don't try to guess. *)
Global Instance fluid_id A : Convertible A A | 0 :=
  { convert X a := a }.

(* Destructure sums. *)
Global Instance fluid_sum A B C `{Convertible A C} `{Convertible B C}
: Convertible (sum1 A B) C | 7 :=
  { convert X ab :=
      match ab with
      | inlE a => convert a
      | inrE b => convert b
      end }.

(* Lean right by default for no reason. *)
Global Instance fluid_left A B `{Convertible A B} C
: Convertible A (sum1 B C) | 9 :=
  { convert X a := inlE (convert a) }.

(* Very incoherent instances. *)
Global Instance fluid_right A C `{Convertible A C} B
: Convertible A (sum1 B C) | 8 :=
  { convert X a := inrE (convert a) }.

Global Instance fluid_empty A : Convertible emptyE A :=
  { convert X v := match v with end }.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
(at level 50, left associativity) : type_scope.

Notation "E -< F" := (Convertible E F)
(at level 90, left associativity) : type_scope.

Module Import SumNotations.

(* Is this readable? *)

Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inrE x) : sum_scope.
Notation "( x |)" := (inlE x) : sum_scope.
Notation "(| x |)" := (inlE (inrE x)) : sum_scope.
Notation "(|| x )" := (inrE (inrE x)) : sum_scope.
Notation "(|| x |)" := (inrE (inrE (inlE x))) : sum_scope.
Notation "(||| x )" := (inrE (inrE (inrE x))) : sum_scope.
Notation "(||| x |)" := (inrE (inrE (inrE (inlE x)))) : sum_scope.
Notation "(|||| x )" := (inrE (inrE (inrE (inrE x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inrE (inrE (inrE (inrE (inlE x))))) : sum_scope.
Notation "(||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inrE (inrE (inrE (inrE (inrE (inlE x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE (inrE x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inrE (inrE (inrE (inrE (inrE (inrE (inlE x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE (inrE (inrE x))))))) : sum_scope.

End SumNotations.

Open Scope sum_scope.

Definition vis {E F R X} `{F -< E}
           (e : F X) (k : X -> itree E R) : itree E R :=
  Vis (convert e) k.

Definition lift {E F X} `{F -< E}
           (e : F X) : itree E X :=
  ITree.liftE (convert e).

(* Embedding effects into trees.

   For example:
[[
   embed :
     (forall x y z,       E (f x y z)) ->
     (forall x y z, itree E (f x y z))
]]
 *)
Class Embeddable U V :=
  embed : U -> V.

Instance Embeddable_forall {A : Type} {U : A -> Type} {V : A -> Type}
         `(forall a, Embeddable (U a) (V a)) :
  Embeddable (forall a, U a) (forall a, V a) :=
  fun u a => embed (u a).

Instance Embeddable_itree {E F : Type -> Type} {R : Type}
         `(Convertible E F) :
  Embeddable (E R) (itree F R) :=
  lift.
