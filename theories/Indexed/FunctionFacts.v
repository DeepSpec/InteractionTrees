From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Indexed.Function
     Indexed.Relation.

Instance Proper_apply_IFun {E F : Type -> Type} {T : Type}
         (RE : forall T, E T -> E T -> Prop)
         (RF : forall T, F T -> F T -> Prop)
  : Proper (i_respectful RE RF ==> RE T ==> RF T) apply_IFun.
Proof.
  repeat red; eauto.
Qed.
