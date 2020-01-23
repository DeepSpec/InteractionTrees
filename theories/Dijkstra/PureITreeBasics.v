From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.DijkstraMonad
   (*  Simple *)
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** The itree Tau (Tau (Tau ...))*)
Definition spin {E: Type -> Type} {A : Type}  : itree E A := ITree.spin.

Lemma spin_div : forall E A, @divergence E A spin.
Proof.
  intros. pcofix CIH. pfold. unfold divergence_. 
  cbn. constructor. right. auto.
Qed.

(*this implies that if a spec w accepts spin, then bind w f should too?   *)
Lemma spin_bind : forall (E : Type -> Type) (A B : Type) (f : A -> itree E B), spin ≈ ITree.bind spin f.
Proof.
  intros. pcofix CIH. pfold. unfold bind. simpl. red.
  cbn. constructor. right. auto.
Qed.

Inductive Void : Type -> Type := .

(*Depreacated predicate on itree predicates. Intended to denote that a predicate is invariant wrt adding
  or subtracting a finite number of Tau's. Replaced with resp_eutt*)
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).

(*Characterizes predicates that respect the eutt relation on itrees. Captures the notion that a predicate
  is invariant wrt adding or subtracting a finite number of Tau's*)
Definition resp_eutt (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
  forall (t1 t2 : itree E A), t1 ≈ t2 -> (P t1 <-> P t2).

Lemma tau_invar_resp_eutt1: forall (E : Type -> Type) (A : Type) (P : itree E A -> Prop),
                                 (forall t1 t2, t1 ≈ t2 ->(P t1 <-> P t2)) -> tau_invar E A P.
  Proof.
    intros. unfold tau_invar. split; intros;
    eapply H; try eassumption; rewrite tau_eutt; reflexivity.
  Qed.

(*Derives contradiction from evidence that a return tree is divergent*)
Ltac inv_div_ret := match goal with [ H : divergenceF _ (RetF _) |- _  ] => inversion H end.

(*Divergent trees never return a value*)
Lemma div_ret_eutt : forall (E : Type -> Type) (A : Type) (t: itree E A) (a : A),
      divergence t -> ~(t ≈ ret a).
  Proof.
    intros. intros HContra. rewrite HContra in H. pinversion H.
  Qed.  

(*Trees that return a value do not diverge*)
Lemma ret_eutt_div : forall (E : Type -> Type) (A : Type) (t : itree E A) (a : A),
      t ≈ ret a -> ~ (divergence t).
  Proof.
    intros. intros HContra. rewrite H in HContra. pinversion HContra.
  Qed.

(*spin is the only divergent itree with the Void event type,*)
Lemma div_spin_eutt : forall (A : Type) (t : itree Void A), divergence t -> t ≈ spin.
Proof.
  intros A. pcofix CIH. intros. pfold. red. cbn.
  destruct (observe t) eqn : Heqt.
  - specialize (itree_eta t) as H. rewrite Heqt in H. rewrite H in H0. pinversion H0.
  - constructor. right. apply CIH. specialize (itree_eta t) as H. rewrite Heqt in H.
    assert (t ≈ Tau t0).
    + rewrite H. reflexivity.
    + rewrite <- tau_eutt. rewrite <- H1. auto.
  - destruct e.
Qed.

Lemma eutt_reta_or_div_aux : forall A (t : itree Void A), ~(exists a, ret a ≈ t) -> divergence t.
  Proof.
    intro A. pcofix CIH. pfold. unfold divergence_. intros. destruct (observe t) eqn : Heqt.
    - exfalso. specialize (itree_eta t) as H. rewrite Heqt in H. apply H0.
      exists r0. rewrite H. reflexivity.
    - constructor. right. eapply CIH; eauto. intro. apply H0.
      destruct H as [a Ha]. exists a. specialize (itree_eta t) as Ht. rewrite Heqt in Ht.
      rewrite Ht. rewrite tau_eutt. auto.
    - destruct e.
  Qed.

  (*All itrees with Void event type either just return a value a, or they diverge (requires the law of the excluded middle to prove) *)
Lemma eutt_reta_or_div : forall A (t : itree Void A), (exists a, ret a ≈ t) \/ (divergence t).
  Proof.
    intros A t.  specialize (classic (exists a, ret a ≈ t) ) as Hlem. destruct Hlem; auto.
    right. apply eutt_reta_or_div_aux. auto.
  Qed.

Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@divergence E A (ret a)).
Proof.
  intros. intro Hcontra. pinversion Hcontra.
Qed.

Lemma not_ret_eutt_spin : forall A E (a : A), ~ (Ret a ≈ @spin E A).
Proof.
  intros. intro Hcontra. simpl in Hcontra. specialize (spin_div E A) as Hdiv. rewrite <- Hcontra in Hdiv.
  pinversion Hdiv.
Qed.

Lemma inv_ret : forall (A : Type) (E : Type -> Type) (a b : A),
    @eutt E A A eq (ret a) (ret b) -> a = b.
Proof. 
  intros. pinversion H; subst. auto.
Qed.

Lemma inv_tau : forall (A : Type) (E : Type -> Type) (t1 t2 : itree E A),
    Tau t1 ≅ Tau t2 -> t1 ≅ t2.
Proof.
  intros. pinversion H; try discriminate. auto.
Qed.

Lemma inv_vis : forall (R A: Type) (E : Type -> Type) (e1 e2 : E A) (k1 k2 : A -> itree E R),
    Vis e1 k1 ≅ Vis e2 k2 -> (e1 = e2) /\ (forall (a : A), k1 a ≅ k2 a).
Proof.
  intros. pinversion H; subst. repeat match goal with | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end.
  subst. split; auto.
Qed.

Lemma eutt_ret_euttge : forall (E : Type -> Type) (A : Type) (a : A) (t : itree E A),
      t ≈ Ret a -> t ≳ Ret a.
Proof.
  intros. generalize dependent t. pcofix CIH. intros. pfold. red. pinversion H0; subst; auto.
  - cbn. auto.
  - cbn. apply EqTauL; auto.
    genobs t1 ot1. genobs (go (@RetF E A _ a)) ot2.  clear H1.
    generalize dependent t1. generalize dependent t.
    induction REL; intros; subst; auto; try discriminate.
    + constructor. inversion Heqot2. auto.
    + constructor; auto. eapply IHREL; eauto.
Qed.

Lemma unfold_spin : forall (E : Type -> Type) (A : Type), (@spin E A) ≅ Tau spin.
Proof.
  intros.  pcofix CIH. cbn. pfold. red. cbn. apply EqTau. cbn.
  left. pcofix CIH'. pfold. red. cbn. auto.
Qed.
