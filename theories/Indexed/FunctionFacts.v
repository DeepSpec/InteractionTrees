(** * Theorems for [ITree.Indexed.Function] *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Basics
     Indexed.Function
     Indexed.Relation.

Set Universe Polymorphism.
(* end hide *)

Instance Proper_apply_IFun {E F : Type -> Type} {T : Type}
         (RE : forall T, E T -> E T -> Prop)
         (RF : forall T, F T -> F T -> Prop)
  : Proper (i_respectful RE RF ==> RE T ==> RF T) apply_IFun.
Proof.
  repeat red; eauto.
Qed.

Lemma fold_apply_IFun {E F : Type -> Type} {T : Type}
  : forall (f : E ~> F) (t : E T),
    f _ t = apply_IFun f t.
Proof.
  reflexivity.
Qed.
