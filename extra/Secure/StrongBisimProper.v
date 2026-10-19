From Coinduction Require Import all. 
From Stdlib Require Import Morphisms.

From ITree Require Import
     ITree
     ITreeFacts
     Eq.EqAxiom
.


Global Instance strong_bisim_proper_chain {E R1 R2} b (c : Chain b) :
       Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> iff) (elem c).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.
