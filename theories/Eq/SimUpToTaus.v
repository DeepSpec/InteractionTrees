(** * Simulation Up To Tau *)

Require Import Paco.paco.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core.

From ITree Require Import
     Eq.UpToTaus.

Section SUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive suttF (eutt : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itreeF E R1 (itree E R1))
          (ot2 : itreeF E R2 (itree E R2)) : Prop :=
| suttF_ (FIN: finite_tausF ot1 -> finite_tausF ot2)
         (EQV: forall ot1' ot2'
                  (UNTAUS1: unalltausF ot1 ot1')
                  (UNTAUS2: unalltausF ot2 ot2'),
               eq_notauF RR eutt ot1' ot2')
.
Hint Constructors suttF.

Definition sutt_ (eutt : itree E R1 -> itree E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
  suttF eutt (observe t1) (observe t2).
Hint Unfold sutt_.

(* [sutt_] is monotone. *)
Lemma monotone_sutt_ : monotone2 sutt_.
Proof. pmonauto. Qed.
Hint Resolve monotone_sutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition sutt : itree E R1 -> itree E R2 -> Prop := paco2 sutt_ bot2.

Global Arguments sutt t1%itree t2%itree.

End SUTT.

Hint Constructors suttF.
Hint Unfold sutt_.
Hint Resolve monotone_sutt_ : paco.

Theorem sutt_eutt {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    sutt RR t1 t2 -> sutt (flip RR) t2 t1 -> eutt RR t1 t2.
Proof.
  pcofix self; intros t1 t2 H1 H2.
  punfold H1. punfold H2.
  destruct H1 as [FIN1 EQV1], H2 as [FIN2 EQV2].
  pfold; constructor.
  - split; auto.
  - intros.
    eapply eq_notauF_and.
    + intros ? ? I1 I2; right.
      apply self; [ apply I1 | apply I2 ].
    + eapply monotone_eq_notauF; auto using EQV1.
      intros; pclearbot; auto.
    + apply eq_notauF_flip.
      eapply monotone_eq_notauF; auto using EQV2.
      intros; pclearbot; auto.
Qed.
