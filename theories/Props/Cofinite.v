(** * Relations between infiniteness and finiteness *)

From ITree Require Import
  Axioms
  ITree
  Props.Finite
  Props.Infinite.

From Paco Require Import paco.

Theorem not_all_infinite_any_finite {E A} (t : itree E A)
  : all_infinite t -> any_finite t -> False.
Proof.
  intros H1 H2. induction H2; punfold H1; inversion H1; try congruence.
  all: pclearbot; rewrite H in H0; inversion H0; subst; auto.
  ddestruction. exact (IHany_finite (H3 _)).
Qed.

Theorem not_any_infinite_all_finite {E A} (t : itree E A)
  : any_infinite t -> all_finite t -> False.
Proof.
  intros H1 H2; induction H2; punfold H1; inversion H1; try congruence.
  - pclearbot. rewrite H in H0; inversion H0; subst; auto.
  - pclearbot. rewrite H in H3. inversion H3; subst; ddestruction.
    exact (H2 _ H4).
Qed.
