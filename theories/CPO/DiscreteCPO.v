From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Logic.Classical
.

Require Import Lia.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq
     CPO.CPO
.

Definition discrete_cpo (A : Type) : weak_cpo A :=
  {|
  weak_leq := eq;
  strong_leq := eq;
  weak_eq := eq;
  strong_eq := eq;
  sup := fun seq => seq 0;
  |}.

Lemma partial_order_eq {A} : PartialOrder (@eq A) eq.
Proof.
  cbv. split; intros; subst; tauto.
Qed.

Program Global Instance discrete_cpo_laws (A : Type) : weak_cpo_laws (discrete_cpo A).
Next Obligation.
  apply partial_order_eq.
Qed.
Next Obligation.
  apply partial_order_eq.
Qed.
Next Obligation.
  red in H. cbn in H.
  constructor; cbn; auto.
  symmetry. apply H. lia.
Qed.
Next Obligation.
  repeat intro. red in H. cbn in H. auto.
Qed.
Next Obligation. 
  red in H. unfold advance.
  apply H. repeat constructor.
Qed.
