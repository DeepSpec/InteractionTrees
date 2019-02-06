From ITree Require Import
     Basics
     Core
     Effect.Sum.

(** Automatic application of commutativity and associativity for
    sums types constructed with [sum1].

    N.B. This is prone to infinite instance resolution loops.
    Put the following option at the top of your [.v] files to
    bound the instance search depth:

[[
  Typeclasses eauto := 5.
]]

    Higher numbers allow bigger instances but grow the search
    space exponentially.
 *)

Class Subeffect (A B : Type -> Type) :=
  { subeffect : A ~> B }.

Notation "E -< F" := (Subeffect E F)
(at level 90, left associativity) : type_scope.

(** [Subeffect] defines a category, with the following identity
    arrow for every type [A]. *)
Instance Subeffect_refl {A} : A -< A | 0 :=
  { subeffect _ a := a }.

(** Composition of the [Subeffect] category. *)
(* TODO: Not sure whether making this an instance is a good idea. *)
Definition Subeffect_trans {A B C} `(A -< B) `(B -< C) : A -< C :=
  {| subeffect _ a := subeffect _ (subeffect _ a) |}.

(** Coproduct. *)
Instance Subeffect_sum1 {A B C} `(A -< C) `(B -< C) : A +' B -< C | 7 :=
  { subeffect _ ab :=
      match ab with
      | inl1 a => subeffect _ a
      | inr1 b => subeffect _ b
      end }.

(** Left inclusion. *)
Instance Subeffect_left {A B C} `(A -< B) : A -< B +' C | 8 :=
  { subeffect _ a := inl1 (subeffect _ a) }.

(** Right inclusion. *)
Instance Subeffect_right {A B C} `(A -< C) : A -< B +' C | 9 :=
  { subeffect _ a := inr1 (subeffect _ a) }.

(** The instance weights on [Subeffect_left] (8) and [Subeffect_right]
    (9) are so that, if you have a list [E +' E +' F] (associated to
    the right: [E +' (E +' F)]), then the first one will be picked
    for the inclusion [E -< E +' E +' F]. *)

(** Initial object of the [Subeffect] category. *)
Instance Subeffect_empty A : emptyE -< A :=
  { subeffect _ v := match v with end }.

(** Notations to construct and pattern-match on nested sums. *)
Module Import SumNotations.

Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inr1 x) : sum_scope.
Notation "( x |)" := (inl1 x) : sum_scope.
Notation "(| x |)" := (inl1 (inr1 x)) : sum_scope.
Notation "(|| x )" := (inr1 (inr1 x)) : sum_scope.
Notation "(|| x |)" := (inr1 (inr1 (inl1 x))) : sum_scope.
Notation "(||| x )" := (inr1 (inr1 (inr1 x))) : sum_scope.
Notation "(||| x |)" := (inr1 (inr1 (inr1 (inl1 x)))) : sum_scope.
Notation "(|||| x )" := (inr1 (inr1 (inr1 (inr1 x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inl1 x))))) : sum_scope.
Notation "(||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x))))))) : sum_scope.

End SumNotations.

Local Open Scope sum_scope.

(** A polymorphic version of [vis]. *)
Definition vis {E F X R} `{F -< E}
           (e : F X) (k : X -> itree E R) : itree E R :=
  Vis (subeffect _ e) k.

(* Called [send] in Haskell freer. *)
Definition lift {E F} `{F -< E} : F ~> itree E :=
  fun T e => ITree.liftE (subeffect _ e).

Arguments lift {E F _ T}.

Lemma lift_is_vis_ret {E F R} `{F -< E} (e : F R) :
  lift e = vis e (fun r => Ret r).
Proof. reflexivity. Qed.

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
         `(E -< F) :
  Embeddable (E R) (itree F R) :=
  lift.
