
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
- intros.
  repeat red. 
  intros. apply H.
- intros. do 2 red. cbn. unfold eqmR_ID. tauto.
Qed.

(* SAZ: This instance should be implied by the one below. *)
(* Instance MonadLaws_ID : MonadLaws MonadID. *)
(* split. *)
(* - cbn. intros. apply cat_id_l. *)
(* - cbn. unfold ID. intros. reflexivity. *)
(* - intros.  cbn. reflexivity. *)
(* - intros. unfold bind. cbn. repeat red. intros. destruct b. apply H. assumption. *)
(* Qed. *)


Lemma image_Id : forall (A:typ) (ma : ID A) (a1 a2 : A), image ID ma @ (a1, a2) -> a1 == ma /\ a2 == ma.
Proof.
  intros.
  epose ((-=->! (fun p => (fst p == ma) /\ (snd p == ma)) _) : relationH A A) as Q.
  Unshelve. 2 : { repeat red. intros. split; intros. rewrite <- H0. assumption. rewrite H0. assumption. }
  assert (eqmR Q @ (ma, ma)).
  { repeat red. split; cbn; reflexivity. }

  assert (SymmetricH Q).
  { repeat red. intros (x, y) HP; split; cbn in *; tauto. }
  assert (TransitiveH Q).
  { repeat red. intros (x, y1) (y2, z) (HX & HY) (HY' & HZ); split; intros; cbn in *; tauto. }
  assert (PER Q). constructor; auto.
  specialize (H Q H3 H0).
  repeat red in H. 
  apply H.
Qed.  


Lemma mayRet_Id : forall (A:typ) (ma : ID A) (a : A), mayRet ID ma @ a -> a == ma.
Proof.
  intros.
  epose ((-=->! (fun a => (a == ma)) _) : A -=-> prop_typ) as Q.
  Unshelve. 2 : { repeat red. intros. split; intros. rewrite <- H0. assumption. rewrite H0. assumption. }
  assert (eqmR (diagonal_prop Q) @ (ma, ma)).
  { repeat red. split; cbn; reflexivity. }
  assert (PER (diagonal_prop Q)). {
    split.
    exact (diagonal_prop_SymmetricH Q).
    exact (diagonal_prop_TransitiveH Q).
  }
  specialize (H (diagonal_prop Q) H1 H0).
  repeat red in H. destruct H as (EQ2 & _).
  apply EQ2.
Qed.  

Instance EqmRMonad_ID : EqmRMonad ID.
split; intros; try tauto.
- repeat red. intros. cbn in EQ. unfold eqmR_ID in EQ. assumption.
- repeat red in H. unfold bind in H. cbn in H.
  unfold eqmR_ID in H.
  exists ma.
  split; auto.
  repeat red. intros. assumption.

- exists ma2. split; auto. apply mayRet_Id in H. rewrite H. assumption.
  repeat red. intros. assumption.

- exists ma1. split; auto. apply mayRet_Id in H. rewrite H. assumption.
  repeat red; intros; assumption.

- intros.
  unfold ID in ma1, ma2.
  assert (mayRet ID ma1 @ ma1).
  { repeat red. cbn. intros. apply EQ. }
  assert (mayRet ID ma2 @ ma2).
  { repeat red. cbn. intros. apply EQ. }
  cbn. apply H0. assumption.  assumption.
- intros. reflexivity.
- intros. reflexivity.
- intros. reflexivity.
Qed.


Instance EqmRMonadInverses_ID : EqmRMonadInverses ID.
split; intros; unfold ID in *; try tauto.
- split.
  + cbn. intros. apply EQ.
  + intros.
    apply image_Id in H0. destruct H0 as (HA1 & HA2).
    rewrite HA1. 
    apply H.
Qed.

Instance EqmRBindInversion_ID : EqmRBindInversion ID.
constructor.
intros; unfold ID in *.
  epose ((-=->! ( fun p => True) _) : (A1 × A2) -=-> prop_typ) as Q.
  Unshelve. 2 : {repeat red. intros; tauto. } 
  
  (*
  epose ((-=->! (fun (p : (A1 × A2)) =>
                   eqmR RB @ (k1 @ (fst p), k2 @ (snd p))) _) : (A1 × A2) -=-> prop_typ) as Q.
   *)
  exists Q.
  split; auto. split. split.
  + intros. exists ma2. split. split.
    unfold bind in H. cbn in H. cbn.
    apply mayRet_Id in H0. rewrite H0. assumption.
  + intros. exists ma1. split. split.
    unfold bind in H. cbn in H. cbn.
    apply mayRet_Id in H0. rewrite H0. assumption.
Qed.
