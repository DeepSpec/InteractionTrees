Require Import Imp.
Require Import Paco.paco.
From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     StateFacts
     Eq.
From Coq Require Import
     String.

(**
   The chapter [Equiv] from _Programming Language Foundations_ introduced a
   notion of behavioral equivalence over _Imp_ programs.
   Two _com_ [c_1] and [c_2] were said to be equivalent if for any initial state,
   [c_1] reduced according to the language's big step semantics to a final state
   if and only if [c_2] reduced to the same final state.
   We investigate in this chapter how behavioral equivalence is phrased at the
   level of itrees, and how it can be proved on simple examples.
*)

(* Defining the notion at the itree level offers the benefit of uniformity:
   the notion is language independent.
   YZ: Not really though, depends on the interpretation obviously
 *)

Definition aequiv_strong (a1 a2: aexp): Prop :=
  denote_aexp a1 ≈ denote_aexp a2.

Definition eval_aexp (a: aexp) :=
  @interp_imp void1 value (denote_aexp a).

Definition aequiv (a1 a2: aexp): Prop :=
  forall s, eval_aexp a1 s ≈ eval_aexp a2 s.

Definition cequiv (c1 c2: com): Prop :=
  forall s, @interp_imp void1 _ (denote_com c1) s ≈ interp_imp (denote_com c2) s.

Section Examples.

  Import ImpNotations.

  Definition W : string := "W".
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".

  Theorem aequiv_example: aequiv (X - X) 0.
  Proof.
    