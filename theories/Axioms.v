(** * Axioms used in the ITree library. *)

(** Other ITree modules should import this to avoid accidentally using more
   axioms elsewhere. *)

From Coq Require Import
  Logic.Classical_Prop
  Logic.IndefiniteDescription
  Logic.EqdepFacts
.

(* Must be imported to use [ddestruction] *)
From Coq Require Export
  Program.Equality
.

Set Implicit Arguments.

(* The following tactics may be used:
   - [dependent destruction]
   - [dependent induction] *)
Ltac ddestruction :=
  repeat lazymatch goal with | H : existT _ _ _ = _ |- _ => dependent destruction H end.

(* Consequence of UIP; used by tactic [dependent destrcution] *)
Definition eq_rect_eq := Eqdep.Eq_rect_eq.eq_rect_eq.

Definition classic := Classical_Prop.classic.

Definition constructive_indefinite_description :=
  IndefiniteDescription.constructive_indefinite_description.

Lemma classicT : forall (P : Prop), {P} + {~ P}.
Proof.
  intros P.
  assert (H : exists b : bool, if b then P else ~ P).
  { destruct (classic P); [exists true | exists false]; assumption. }
  apply constructive_indefinite_description in H.
  destruct H as [[] ?]; [ left | right ]; assumption.
Qed.
