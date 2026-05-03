From Stdlib Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Infinite.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Set Implicit Arguments.

(* Contains some useful definitions and lemmas regarding ITrees with no events*)

(** The itree Tau (Tau (Tau ...))*)
#[local] Notation spin := ITree.spin.

#[local] Tactic Notation "step" := repeat red; step. 
#[local] Tactic Notation "step" "in" ident(h) := repeat red in h; step in h. 
#[local] Tactic Notation "sinv" ident(h) := step in h; inv h. 

(*this implies that if a spec w accepts spin, then bind w f should too?   *)
Lemma spin_bind : forall (E : Type -> Type) (A B : Type) (f : A -> itree E B), spin ≈ ITree.bind spin f.
Proof.
  intros. bcoinduction. simpl.
  now constructor.
Qed.

(*Depreacated predicate on itree predicates. Intended to denote that a predicate is invariant wrt adding
  or subtracting a finite number of Tau's. Replaced with resp_eutt*)
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).

(*Characterizes predicates that respect the eutt relation on itrees. Captures the notion that a predicate
  is invariant wrt adding or subtracting a finite number of Tau's*)
Notation resp_eutt P := (Proper (eutt eq ==> iff) P).

Lemma tau_invar_resp_eutt1: forall (E : Type -> Type) (A : Type) (P : itree E A -> Prop),
                                 (forall t1 t2, t1 ≈ t2 ->(P t1 <-> P t2)) -> tau_invar P.
  Proof.
    intros. unfold tau_invar. split; intros;
    eapply H; try eassumption; rewrite tau_eutt; reflexivity.
  Qed.

(*spin is the only divergent itree with the void1 event type,*)
Lemma div_spin_eutt : forall (A : Type) (t : itree void1 A), any_infinite t -> t ≈ spin.
Proof.
  intros A. bcoinduction. intros. cbn.
  destruct (observe t) eqn : Heqt.
  - specialize (itree_eta t) as Heta. rewrite Heqt in Heta. rewrite Heta in H. sinv H. 
  - constructor. apply CIH. specialize (itree_eta t) as Heta. rewrite Heqt in Heta.
    assert (t ≈ Tau t0).
    + rewrite Heta. reflexivity.
    + rewrite <- tau_eutt. rewrite <- H0. auto.
  - destruct e.
Qed.

Lemma eutt_reta_or_div_aux : forall A (t : itree void1 A), ~(exists a, ret a ≈ t) -> any_infinite t.
Proof.
  intro A. unfold any_infinite, any_infinite_. 
  coinduction c CIH. 
  intros. destruct (observe t) eqn : Heqt.
  - exfalso. specialize (itree_eta t) as Heta. rewrite Heqt in Heta. apply H.
    exists r. rewrite Heta. reflexivity.
  - repeat red; simpobs; constructor. eapply CIH; eauto. intro. apply H.
    destruct H0 as [a Ha]. exists a. specialize (itree_eta t) as Ht. rewrite Heqt in Ht.
    rewrite Ht. rewrite tau_eutt. auto.
  - destruct e.
Qed.

  (*All itrees with void1 event type either just return a value a, or they diverge (requires the law of the excluded middle to prove) *)
Lemma eutt_reta_or_div : forall A (t : itree void1 A), (exists a, ret a ≈ t) \/ (any_infinite t).
Proof.
  intros A t.  specialize (classic (exists a, ret a ≈ t) ) as Hlem. destruct Hlem; auto.
  right. apply eutt_reta_or_div_aux. auto.
Qed.

Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@any_infinite E A (ret a)).
Proof.
  intros. intro Hcontra. sinv Hcontra. 
Qed.

Lemma not_ret_eutt_spin : forall A E (a : A), ~ (Ret a ≈ @spin E A).
Proof.
  intros. intro Hcontra. symmetry in Hcontra. revert Hcontra; apply no_infinite_ret.
  apply spin_infinite.
Qed.

Lemma eutt_ret_euttge : forall (E : Type -> Type) (A : Type) (a : A) (t : itree E A),
      t ≈ Ret a -> t ≳ Ret a.
Proof.
  intros. generalize dependent t. icoinduction c CIH. intros. sinv H. 
  - taul. 
  (* Unset Printing Notations.  *)
    remember (observe (Ret a)).
    induction REL; try easy. 
    + eret. 
    + taul. now apply IHREL.  
Qed.

Lemma unfold_spin : forall (E : Type -> Type) (A : Type), (@spin E A) ≅ Tau spin.
Proof.
  intros. step. cbn. reflexivity. 
Qed.

Lemma burn_eutt_r : forall (A : Type) (t t' : itree void1 A) (n : nat), t≈ t' -> burn n t ≈ t'.
Proof.
  intros. generalize dependent t. generalize dependent t'. induction n; intros; simpl; auto.
  destruct (observe t) eqn : Heq; try destruct e.
  - specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite <- Ht. auto.
  - apply IHn. specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite Ht in H.
    rewrite tau_eutt in H. auto.
Qed.
