(** * Equivalence up to taus *)

(** We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eq.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)

(** Splitting things this way makes the library easier to build in parallel.
 *)

(* begin hide *)
Require Import Paco.paco.

From ITree Require Import
     Core.ITreeDefinition.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttF
              (eutt: itree E R1 -> itree E R2 -> Prop)
              (eutt0: itree E R1 -> itree E R2 -> Prop)
  : itree' E R1 -> itree' E R2 -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF eutt eutt0 (RetF r1) (RetF r2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, eutt (k1 x) (k2 x) \/ eutt0 (k1 x) (k2 x)):
    euttF eutt eutt0 (VisF e k1) (VisF e k2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt0 t1 t2):
    euttF eutt eutt0 (TauF t1) (TauF t2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF eutt eutt0 (observe t1) ot2):
    euttF eutt eutt0 (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF eutt eutt0 ot1 (observe t2)):
    euttF eutt eutt0 ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt0_ eutt eutt0 t1 t2 := euttF eutt eutt0 (observe t1) (observe t2).
Hint Unfold eutt0_.

Definition eutt0 eutt t1 t2 := wcpn2 (eutt0_ eutt) bot2 bot2 t1 t2.
Hint Unfold eutt0.

Lemma euttF_mon r r' s s' x y
    (EUTT: euttF r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF r' s' x y.
Proof.
  induction EUTT; eauto.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Lemma monotone_eutt0_ eutt : monotone2 (eutt0_ eutt).
Proof. repeat intro. eauto using euttF_mon. Qed.
Hint Resolve monotone_eutt0_ : paco.

Lemma monotone_eutt0 : monotone2 eutt0.
Proof. red. intros. eapply wcpn2_mon_bot; eauto using euttF_mon. Qed.
Hint Resolve monotone_eutt0 : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : itree E R1 -> itree E R2 -> Prop := wcpn2 eutt0 bot2 bot2.
Hint Unfold eutt.

Lemma eutt_fold :
  eutt <2= wcpn2 eutt0 bot2 bot2.
Proof. intros. apply PR. Qed.
Hint Resolve eutt_fold.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors euttF.
Hint Unfold eutt0_.
Hint Unfold eutt0.
Hint Resolve monotone_eutt0_ : paco.
Hint Resolve monotone_eutt0 : paco.
Hint Unfold eutt.
Hint Resolve eutt_fold.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.
