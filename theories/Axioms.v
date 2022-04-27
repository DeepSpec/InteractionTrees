(** * Axioms used in the ITree library. *)

(** Other ITree modules should import this to avoid accidentally using more
   axioms elsewhere. *)

From Coq Require Import
  Logic.Classical_Prop
  Logic.ClassicalChoice
  Logic.EqdepFacts
  Logic.FunctionalExtensionality
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

Definition choice := ClassicalChoice.choice.

Definition functional_extensionality := @FunctionalExtensionality.functional_extensionality.

(* From Coq.Logic.ChoiceFacts *)
Definition GuardedFunctionalChoice_on {A B} :=
  forall P : A -> Prop, forall R : A -> B -> Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).
Axiom guarded_choice : forall {A B}, @GuardedFunctionalChoice_on A B.

Inductive mwitness : Type :=
| Witness (P : Type) (_ : P)
| NoWitness.

Lemma classicT_inhabited : inhabited (forall (P : Type), P + (P -> False)).
Proof.
  destruct (choice (fun (P : Type) (b : mwitness) =>
    match b with @Witness Q _ => P = Q | NoWitness => P -> False end)) as [f H].
  { intros P; destruct (classic (inhabited P)) as [[x] | ];
      [exists (Witness x) | exists NoWitness]; auto. }
  constructor. intros P; specialize (H P); destruct (f P); [subst | ]; auto.
Qed.
