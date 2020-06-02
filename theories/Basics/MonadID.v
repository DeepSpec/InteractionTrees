
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.Typ_Class2
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
     Basics.HeterogeneousRelations
.

Import CatNotations.
Open Scope cat_scope.


Definition ID (X:typ) := X.

Instance MonadID : Monad typ_proper ID.
split.
- exact id_.
- unfold ID. intros a b f. exact f.
Defined.

Definition eqmR_ID : forall (A B : typ) (R : relationH A B), relationH (ID A) (ID B) :=
  fun _ _ R => R.

Program Instance EqmR_ID : EqmR ID :=
  {
  eqmR := eqmR_ID;
  }.
Next Obligation.
  split; red; tauto.
Qed.

Instance EqmR_OK_ID : EqmR_OK ID.
split; try tauto.
- intros. cbn in *. unfold eqmR_ID in *.
  red. exists mb. tauto.
- intros. cbn in *. unfold eqmR_ID in *.
  reflexivity.
- intros.
  repeat red.
  intros. apply H. apply H0.
Qed.  


Instance MonadLaws_ID : MonadLaws MonadID.
split.
- cbn. intros. apply cat_id_l.
- cbn. unfold ID. intros. reflexivity.
- intros.  cbn. reflexivity.
- intros. unfold bind. cbn. repeat red. intros. destruct b. apply H. assumption.
Qed.


Instance EqmRMonad_ID : EqmRMonad ID.
split; try tauto.
- intros.
  repeat red. unfold bind. cbn.  apply H0. apply H.
- intros.
  repeat red. destruct B. cbn.
  destruct f. apply p. assumption.
- intros. repeat red.
  destruct C. cbn.
  destruct f. destruct g.
  cbn. apply p0. apply p. assumption.
Qed.
