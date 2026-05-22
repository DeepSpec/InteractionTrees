From Coinduction Require Import all.
From Stdlib Require Import Morphisms Program.Basics.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqProgInsens
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant case_rel {A1 A2 B : Type} (R1 : A1 -> B -> Prop) (R2 : A2 -> B -> Prop) : (A1 + A2) -> B -> Prop :=
  | crl a1 b : R1 a1 b -> case_rel R1 R2 (inl a1) b
  | crr a2 b : R2 a2 b -> case_rel R1 R2 (inr a2) b.

(* ===== Vis lemmas ===== *)

Lemma pi_eqit_secure_pub_vis E R1 R2 RR Label priv l b1 b2 A (e : E A)
      (k1 : A -> itree E R1) (k2 : A -> itree E R2) :
  leq (priv _ e) l ->
  (forall a, pi_eqit_secure Label priv RR b1 b2 l (k1 a) (k2 a) ) ->
  pi_eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2).
Proof.
  intros. step. constructor; auto.
Qed.

Lemma pi_eqit_secure_priv_vislr E R1 R2 RR Label priv l b1 b2 A B (e1 : E A) (e2 : E B)
      (k1 : A -> itree E R1) (k2 : B -> itree E R2) :
  ~ leq (priv _ e1) l -> ~ leq (priv _ e2) l ->
  (forall a b, pi_eqit_secure Label priv RR b1 b2 l (k1 a) (k2 b) ) ->
  pi_eqit_secure Label priv RR b1 b2 l (Vis e1 k1) (Vis e2 k2).
Proof.
  intros. step. constructor; auto.
Qed.

Lemma pi_eqit_secure_priv_visl E R1 R2 RR Label priv l b2 A (e1 : E A)
      (k1 : A -> itree E R1) (t2 : itree E R2) :
  ~ leq (priv _ e1) l ->
  (forall a, pi_eqit_secure Label priv RR true b2 l (k1 a) t2 ) ->
  pi_eqit_secure Label priv RR true b2 l (Vis e1 k1) t2.
Proof.
  intros. step. constructor; auto.
Qed.

Lemma pi_eqit_secure_priv_visr E R1 R2 RR Label priv l b1 A (e1 : E A)
      (t1 : itree E R1) (k2 : A -> itree E R2) :
  ~ leq (priv _ e1) l ->
  (forall a, pi_eqit_secure Label priv RR b1 true l t1 (k2 a) ) ->
  pi_eqit_secure Label priv RR b1 true l t1 (Vis e1 k2).
Proof.
  intros. step. constructor; auto.
Qed.

(* ===== use_simpobs Ltac ===== *)

Ltac use_simpobs :=
  repeat match goal with
         | H : TauF _ = observe ?t |- _ => apply simpobs in H
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

(* The [eq_itree]-based Proper in [SecureEqProgInsens.v] is [flip impl] only.
   For [rewrite H] in the forward direction we need an [iff] (or [impl])
   variant: derive it from the [flip impl] one using symmetry of [eq_itree]. *)
#[global] Instance pi_eqit_secure_eq_itree_proper_iff
  {E} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) :
  Proper (@eq_itree E R1 R1 eq ==> eq_itree eq ==> iff)
         (pi_eqit_secure Label priv RS b1 b2 l).
Proof.
  intros t1 t1' EQ1 t2 t2' EQ2.
  pose proof (pi_eqit_secure_eutt_proper (E := E) (RS := RS) (Label := Label)
                (priv := priv) (l := l) b1 b2) as Hfwd.
  unfold Proper, respectful in Hfwd.
  split; intros H.
  - (* P t1 t2 -> P t1' t2': use Proper with symmetric eqs *)
    eapply (Hfwd _ _ (symmetry EQ1) _ _ (symmetry EQ2)). exact H.
  - (* P t1' t2' -> P t1 t2: direct *)
    eapply (Hfwd _ _ EQ1 _ _ EQ2). exact H.
Qed.

(* Iff variant on the chain element [elem c] (needed for forward rewrites
   inside [coinduction c CIH] proofs). Derived from the [flip impl] chain
   Proper [pi_eqit_secure_proper_secureC] in [SecureEqProgInsens.v]. *)
#[global] Instance pi_eqit_secure_chain_proper_iff
  {E R1 R2} b1 b2 Label priv (RR : R1 -> R2 -> Prop) l
  (c : Chain (pi_secure_eqit_mon Label priv RR b1 b2 l)) :
  Proper (@eq_itree E R1 R1 eq ==> eq_itree eq ==> iff) (elem c).
Proof.
  intros t1 t1' EQ1 t2 t2' EQ2.
  pose proof (pi_eqit_secure_proper_secureC b1 b2 Label priv RR l c) as Hfwd.
  unfold Proper, respectful in Hfwd.
  split; intros H.
  - eapply (Hfwd _ _ (symmetry EQ1) _ _ (symmetry EQ2)). exact H.
  - eapply (Hfwd _ _ EQ1 _ _ EQ2). exact H.
Qed.

(* ===== Transitivity through Ret ===== *)

(* I believe we could generalize this lemma for any t2 that converges along all paths *)
Lemma pi_eqit_secure_trans_ret E R1 R2 R3 Label priv l b1 b2
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (t1 : itree E R1) (r : R2) (t3 : itree E R3) :
  pi_eqit_secure Label priv RR1 b1 b2 l t1 (Ret r) ->
  pi_eqit_secure Label priv RR2 b1 b2 l (Ret r) t3 ->
  pi_eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  revert t1 t3. coinduction c CIH. 
  intros. sinv H; subst; use_simpobs.
  - step. rewrite H1. generalize dependent t3. icoinduction c' CIH'. intros t3 Ht3.
  cbn. 
    sinv Ht3; use_simpobs.
    + constructor; auto. econstructor; eauto.
    + rewrite itree_eta' at 1. constructor; auto. eapply CIH'.
      symmetry in H. use_simpobs. now rewrite H in H2. 
    + rewrite itree_eta' at 1. constructor; auto. intros.
      eapply CIH'. symmetry in H. use_simpobs. setoid_rewrite H in H2. apply H2.
  - symmetry in H2. use_simpobs. rewrite H1. constructor; auto.
    eapply CIH; auto. rewrite <- H2. auto.
  - symmetry in H2. use_simpobs. rewrite H1. constructor; auto.
    intros. apply CIH; auto. rewrite <- H2. apply H3.
Qed.

(* ===== Iter through Ret ===== *)

Lemma pi_eqit_secure_iter_ret E R S1 S2 Label priv l b2 s body
      (Rinv : R -> S2 -> Prop) (RS : S1 -> S2 -> Prop)
  (HRinv : (forall r', Rinv r' s ->
            pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (body r') (Ret s) )) :
  forall r,
  Rinv r s ->
  @pi_eqit_secure E S1 S2 Label priv RS true b2 l (ITree.iter body r) (Ret s).
Proof.
  coinduction. intros r0 Hr0. setoid_rewrite unfold_iter.
  assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (body r0) (Ret s))
  by auto. 
  remember (body r0) as t. clear Heqt. step. generalize dependent t.
  coinduction c' CIH'. intros t Ht.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq.
    assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Ret r) (Ret s) )
    by now 
    rewrite <- Heq.
    sinv H. subst. inv H2.
    + rewrite bind_ret_l. constructor; auto.
      rewrite unfold_iter. eapply CIH'; eauto.
    + rewrite bind_ret_l. constructor. auto.
  - rewrite Heq. rewrite bind_tau. constructor; auto.
    eapply CIH'.
    assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Tau t0) (Ret s)).
    rewrite <- Heq. auto. sinv H. rewrite <- itree_eta. auto.
  - destruct (classic (leq (priv _ e) l ) ).
    + exfalso. apply HRinv in Hr0.
      assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Vis e k) (Ret s) ).
      { rewrite <- Heq. auto. }
      sinv H0; subst. ddestruction. subst. contradiction.
    + rewrite Heq. rewrite bind_vis.
      constructor; auto. intros x. eapply CIH'.
      assert ( pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Vis e k) (Ret s)) .
      rewrite <- Heq. auto. sinv H0; subst; ddestruction; subst.
      rewrite <- itree_eta. apply H2.
Qed.

(* ===== Bind compatibility =====

    This is already proved of the chain; here just instantiated at the gfp.  *)
Lemma pi_secure_eqit_bind'
     : forall (E : Type -> Type) (R1 R2 S1 S2 : Type) (RR : R1 -> R2 -> Prop)
         (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
         (priv : forall A : Type, E A -> L) (l : L)
         (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1)
         (k2 : R2 -> itree E S2),
       (forall (r1 : R1) (r2 : R2),
        RR r1 r2 -> pi_eqit_secure Label priv RS b1 b2 l (k1 r1) (k2 r2)) ->
       pi_eqit_secure Label priv RR b1 b2 l t1 t2 ->
       pi_eqit_secure Label priv RS b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. eapply pi_eqit_secure_bind; eauto.
Qed.
