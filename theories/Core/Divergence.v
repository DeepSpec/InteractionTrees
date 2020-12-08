(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq. 

From ITree Require Export
     Eq.Shallow.

Import ITreeNotations.
Local Open Scope itree.

(** ** Divergence * *)

Inductive divergenceF {E X} (P : itree E X -> Prop) : itree' E X -> Prop :=
  | DivTau : forall (t : itree E X), P t -> divergenceF P (TauF t)
  | DivVis : forall {A} (k : A -> itree E X) (e: E A), forall (a : A), P (k a) -> divergenceF P (VisF e k). 
Hint Constructors divergenceF.

Definition divergence_ {E X} sim :=
  fun t1 => @divergenceF E X sim (observe t1).
Hint Unfold divergence_. 

Lemma divergenceF_mono {E X} sim sim' x0 
      (IN: divergenceF sim x0)
      (LE: sim <1= sim'):
  @divergenceF E X sim' x0.
Proof.
  intros. induction IN; eauto.
Qed. 

Lemma divergenceF__mono {E X} :
  monotone1 (@divergence_ E X).
Proof.
  do 2 red. intros. eapply divergenceF_mono; eauto. 
Qed. 
Hint Resolve divergenceF__mono : paco. 

Definition divergence {E A} : itree E A -> Prop :=
  paco1 (@divergence_ E A) bot1. 

Instance divergence_proper_eutt {E X R} : Proper (eutt R ==> iff) (@divergence E X).
Proof.
  repeat intro. split.
  - revert x y H. pcofix CH. intros.
    punfold H0. unfold_eqit. pfold. red. punfold H1. red in H1.
    induction H0.
    + inversion H1.
    + apply DivTau. inversion H1; subst. right. eapply CH.
      red in H0. pclearbot. apply REL.
      pclearbot. apply H0.
    + inversion H1; subst. dependent destruction H3. eapply DivVis. 
      pclearbot. right. eapply CH. apply REL. eapply H0.
    + apply IHeqitF. inversion H1; subst.
      pclearbot. punfold H2.
    + econstructor. left. pfold. red.
      apply IHeqitF. apply H1.
  - revert x y H. pcofix CH. intros.
    punfold H0. unfold_eqit. pfold. red. punfold H1. red in H1.
    induction H0.
    + inversion H1.
    + apply DivTau. inversion H1; subst. right. eapply CH.
      red in H0. pclearbot. apply REL.
      pclearbot. apply H0.
    + inversion H1; subst. dependent destruction H3. eapply DivVis.
      pclearbot. right. eapply CH. apply REL. eapply H0.
    + econstructor. left. pfold. red.
      apply IHeqitF. apply H1.
    + apply IHeqitF. inversion H1; subst.
      pclearbot. punfold H2.
Qed.

Theorem spin_diverge {E A} : @divergence E A ITree.spin.
Proof.
  unfold divergence, ITree.spin.
  pcofix H. pfold. constructor. right. apply H.
Qed. 
