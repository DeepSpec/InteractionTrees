(** * Relations on indexed types *)

(* begin hide *)
From Coq Require Import
     Relations
     Setoid.

From ITree Require Import
     Basics.Basics.

Set Universe Polymorphism.
(* end hide *)

(** This is an indexed generalization of the standard [respectful]
    relation ([==>]). *)
Definition i_respectful {A B : Type -> Type}
           (RA : forall T, A T -> A T -> Prop)
           (RB : forall T, B T -> B T -> Prop)
           (f1 f2 : A ~> B)
  : Prop
  := forall T (a1 a2 : A T), RA T a1 a2 -> (RB T) (f1 T a1) (f2 T a2).

Definition i_pointwise {A B : Type -> Type}
           (RB : forall T, B T -> B T -> Prop)
           (f1 f2 : A ~> B)
  : Prop
  := forall T (a : A T), (RB T) (f1 T a) (f2 T a).

Instance Reflexive_i_pointwise {A B : Type -> Type}
         (RB : forall T, B T -> B T -> Prop)
         {Reflexive_R : forall T, Reflexive (RB T)}
  : Reflexive (@i_pointwise A B RB).
Proof.
  repeat red; intros; red in Reflexive_R; eauto.
Qed.

Instance Symmetric_i_pointwise {A B : Type -> Type}
         (RB : forall T, B T -> B T -> Prop)
         {Symmetric_R : forall T, Symmetric (RB T)}
  : Symmetric (@i_pointwise A B RB).
Proof.
  repeat red; intros; red in Symmetric_R; eauto.
Qed.

Instance Transitive_i_pointwise {A B : Type -> Type}
         (RB : forall T, B T -> B T -> Prop)
         {Transitive_R : forall T, Transitive (RB T)}
  : Transitive (@i_pointwise A B RB).
Proof.
  repeat red; intros; red in Transitive_R; eauto.
Qed.

Instance Equivalence_i_pointwise {A B : Type -> Type}
         (RB : forall T, B T -> B T -> Prop)
         {Equivalence_R : forall T, Equivalence (RB T)}
  : Equivalence (@i_pointwise A B RB).
Proof.
  split; try typeclasses eauto.
Qed.

Instance subrelation_i_pointwise_i_respectful {A B : Type -> Type}
           (RB : forall T, B T -> B T -> Prop)
  : subrelation (i_pointwise RB) (i_respectful (fun T => @eq (A T)) RB).
Proof.
  repeat red; intros; subst; auto.
Qed.

(* This is not an instance, to avoid instance resolution loops. *)
Definition subrelation_i_respectful_i_pointwise {A B : Type -> Type}
           (RB : forall T, B T -> B T -> Prop)
  : subrelation (i_respectful (fun T => @eq (A T)) RB) (i_pointwise RB).
Proof.
  repeat red; auto.
Qed.
