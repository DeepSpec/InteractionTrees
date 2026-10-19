(** * Relations between infiniteness and finiteness *)

From ITree Require Import
  Axioms
  ITree
  Props.Finite
  Props.Infinite.

From Coinduction Require Import all.

Theorem not_all_infinite_any_finite {E A} (t : itree E A)
  : all_infinite t -> any_finite t -> False.
Proof.
  intros H1 H2. induction H2; apply (gfp_fp all_infinite_mon) in H1;
    cbn[all_infinite_mon body] in H1; unfold all_infinite_ in H1;
    inversion H1; try congruence.
  all: rewrite H in H0; inversion H0; subst; auto.
  ddestruction. exact (IHany_finite (H3 _)).
Qed.

Theorem not_any_infinite_all_finite {E A} (t : itree E A)
  : any_infinite t -> all_finite t -> False.
Proof.
  intros H1 H2; induction H2; apply (gfp_fp any_infinite_mon) in H1;
    cbn[any_infinite_mon body] in H1; unfold any_infinite_ in H1;
    inversion H1; try congruence.
  - rewrite H in H0; inversion H0; subst; auto.
  - rewrite H in H3. inversion H3; subst; ddestruction.
    exact (H2 _ H4).
Qed.
