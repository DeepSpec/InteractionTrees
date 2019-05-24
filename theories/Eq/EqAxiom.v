(** * Strong bisimulation is propositional equality *)

(** This is not provable but admissible as an axiom.

    This axiom is not used by this library, but only exported for
    convenience, as it can certainly simplify some developments.
 *)

(* begin hide *)
From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq.
(* end hide *)

(** Strong bisimulation is propositional equality.
    The converse is reflexivity of strong bisimulation
    (and is provable without axioms). *)
Axiom bisimulation_is_eq :
  forall {E : Type -> Type} {R : Type} (t1 t2 : itree E R),
    t1 ≅ t2 -> t1 = t2.

Lemma itree_eta_ {E R} (t : itree E R) : t = go (observe t).
Proof.
  apply bisimulation_is_eq. apply itree_eta.
Qed.
