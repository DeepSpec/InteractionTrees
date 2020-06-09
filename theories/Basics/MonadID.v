
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.Typ
     Basics.HeterogeneousRelations
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
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
  exists mb. tauto.
- intros. cbn in *. unfold eqmR_ID in *.
  reflexivity.
- admit. 
- intros.
  repeat red. 
  intros. apply H.
- intros. do 2 red. cbn. unfold eqmR_ID. tauto.
Admitted.

(* SAZ: This instance should be implied by the one below. *)
(* Instance MonadLaws_ID : MonadLaws MonadID. *)
(* split. *)
(* - cbn. intros. apply cat_id_l. *)
(* - cbn. unfold ID. intros. reflexivity. *)
(* - intros.  cbn. reflexivity. *)
(* - intros. unfold bind. cbn. repeat red. intros. destruct b. apply H. assumption. *)
(* Qed. *)


Instance EqmRMonad_ID : EqmRMonad ID.
split; try tauto.
- intros.
  unfold ID in ma1, ma2.
  assert (mayRet ID ma1 @ ma1).
  { repeat red. cbn. intros. apply EQ. }
  specialize (H0 ma1 H2). destruct H0 as (a2 & RA1 & MR2 & EQ).
  do 6 red in MR2.
  epose ((-=->! (fun a => (a == ma2)) _) : A2 -=-> prop_typ) as Q.
  Unshelve. 2 : { repeat red. intros. split; intros. rewrite <- H0. assumption. rewrite H0. assumption. }
  assert (eqmR (diagonal_prop Q) @ (ma2, ma2)).
  { repeat red. split; cbn; reflexivity. }
  specialize (MR2 (diagonal_prop Q) (diagonal_prop_SymmetricH Q) (diagonal_prop_TransitiveH Q) H0).
  repeat red in MR2. destruct MR2 as (EQ2 & _).
  cbn in EQ2. rewrite <- EQ2. assumption.
- intros. reflexivity.
- intros. reflexivity.
- intros. reflexivity.
Qed.
