#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.


Ltac inverts h :=
  inversion h; subst; clear h.


(* Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  end. *)

Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Ltac break :=
  repeat match goal with
         | h : _ \/ _  |- _ => destruct h
         | h : _ /\ _  |- _ => destruct h
         | h : exists x, _ |- _ => destruct h
         end.

Ltac break_match_in H :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:? end.

(* A smarter version of this should be part of the [coinduction] library *)

Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y ?z => apply (proj1 (gfp_fp b x y z))
  | |- elem ?R ?x ?y ?z => apply (b_chain R x y z)
  | |- gfp ?b ?x ?y => apply (proj1 (gfp_fp b x y))
  | |- elem ?R ?x ?y => apply (b_chain R x y)
  | |- gfp ?b ?x => apply (proj1 (gfp_fp b x))
  | |- elem ?R ?x => apply (b_chain R x)
  end.

Ltac step := first [step_ | red; step_].

Ltac step_in H :=
  match type of H with
  | gfp ?b ?x ?y ?z => apply (gfp_fp b x y z) in H
  | gfp ?b ?x ?y => apply (gfp_fp b x y) in H
  | gfp ?b ?x => apply (gfp_fp b x) in H
  | _ => red in H; step_in H
  end.
Tactic Notation "step" "in" ident(H) := step_in H.


Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.
