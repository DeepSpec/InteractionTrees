From Stdlib Require Import
     Morphisms
.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Eq.Shallow
     Props.Infinite
.

From Coinduction Require Import all.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Set Implicit Arguments.

(** Defines euttNoRet, a relation for relating ITrees 
    over different return types, that never return and whose events are bisimilar. Also contains noret_cast, a function that casts ITrees that never return from one return type to another while preserving its events.
*)

Definition euttNoRet {E} {A B : Type} (ta : itree E A) (tb : itree E B) := 
  eutt (fun a b => False) ta tb.


Lemma euttNoRet_spin : forall (E : Type -> Type) (A B : Type), @euttNoRet E A B ITree.spin ITree.spin.
Proof.
  intros. unfold euttNoRet. icoinduction c cih. cbn. constructor. exact cih.
Qed.

Lemma noret_bind_nop : forall (E : Type -> Type) (A B : Type) (t : itree E A) (f : A -> itree E B),
    all_infinite t -> euttNoRet t (t >>= f).
Proof.
  intros E A B. unfold euttNoRet. icoinduction c cih. intros t f Hdiv.
  apply (gfp_fp all_infinite_mon) in Hdiv.
  cbn[all_infinite_mon body] in Hdiv. unfold all_infinite_ in Hdiv.
  inversion Hdiv; subst.
  - unfold bind, Monad_itree.
    rewrite observe_bind. rewrite <- H. cbn. apply EqTau.
    change (ITree.subst f t0) with (ITree.bind t0 f).
    apply cih. auto.
  - unfold bind, Monad_itree.
    rewrite observe_bind. rewrite <- H. cbn. apply EqVis.
    intros v. change (ITree.subst f (k v)) with (ITree.bind (k v) f).
    apply cih. apply H0.
Qed.   

Lemma euttNoRet_subrel : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                               (ta : itree E A) (tb : itree E B), 
    euttNoRet ta tb -> eutt R ta tb.
Proof.
  intros.
  eapply eqit_mono with (b1 := true) (b2 := true) (RR := fun _ _ => False);
    try (repeat intro; contradiction); auto.
Qed.

Lemma all_infinite_euttNoRet : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                            (ta : itree E A) (tb : itree E B),
    all_infinite ta -> eutt R ta tb -> euttNoRet ta tb.
Proof.
  intros E A B R. unfold euttNoRet. icoinduction c cih. intros ta tb Hdiv Heutt.
  step in Heutt. cbn[eqit_mon body] in Heutt. unfold eqit_ in Heutt.
  cbn[eqit_mon body]. unfold eqit_.
  apply (gfp_fp all_infinite_mon) in Hdiv.
  cbn[all_infinite_mon body] in Hdiv. unfold all_infinite_ in Hdiv.
  dependent induction Heutt.
  - exfalso. rewrite <- x0 in Hdiv. inversion Hdiv.
  - rewrite <- x0. rewrite <- x. apply EqTau. apply cih.
    + rewrite <- x0 in Hdiv. inversion Hdiv; subst. auto.
    + auto.
  - rewrite <- x0. rewrite <- x. apply EqVis. intros v. apply cih.
    + rewrite <- x0 in Hdiv. inversion Hdiv; subst. ddestruction. apply H0.
    + apply REL.
  - rewrite <- x. apply EqTauL; auto. apply IHHeutt; auto.
    rewrite <- x in Hdiv. inversion Hdiv; subst.
    apply (gfp_fp all_infinite_mon) in H0.
    cbn[all_infinite_mon body] in H0. unfold all_infinite_ in H0. exact H0.
  - rewrite <- x. apply EqTauR; auto.
Qed.
     
Lemma euttNoRet_all_infinite : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    euttNoRet t1 t2 -> all_infinite t1.
Proof.
  intros E A B. unfold all_infinite. coinduction c cih. intros t1 t2 H.
  cbn[all_infinite_mon body]. unfold all_infinite_.
  unfold euttNoRet in H. step in H. cbn[eqit_mon body] in H. unfold eqit_ in H.
  dependent induction H; try contradiction.
  - rewrite <- x0. constructor. apply cih with (t2 := m2). unfold euttNoRet. auto.
  - rewrite <- x0. constructor. intros v. apply cih with (t2 := k2 v).
    unfold euttNoRet. apply REL.
  - rewrite <- x. constructor. apply cih with (t2 := t2). unfold euttNoRet.
    step. cbn[eqit_mon body]. unfold eqit_. auto.
  - eapply IHeqitF; eauto.
Qed.


Lemma euttNoRet_sym : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    euttNoRet t1 t2 -> euttNoRet t2 t1.
Proof.
  intros E A B. unfold euttNoRet. icoinduction c cih. intros t1 t2 H.
  unfold euttNoRet in H. step in H. cbn[eqit_mon body] in H. unfold eqit_ in H.
  dependent induction H; try contradiction.
  - rewrite <- x0. rewrite <- x. apply EqTau. apply cih. auto.
  - rewrite <- x0. rewrite <- x. apply EqVis. intros v. apply cih. apply REL.
  - rewrite <- x. apply EqTauR; auto.
  - rewrite <- x. apply EqTauL; auto.
Qed.

Lemma all_infinite_bind : forall (E : Type -> Type) (R U: Type) (t : itree E R) 
                                 (f : R -> itree E U),
    all_infinite t -> all_infinite (bind t f).
Proof.
  intros. apply noret_bind_nop with (B := U) (f := f) in H.
  apply euttNoRet_sym in H. apply euttNoRet_all_infinite in H. auto.
Qed.
     
Lemma euttNoRet_trans : forall (E : Type -> Type) (A B C : Type) (t1 : itree E A) 
                              (t2 : itree E B) (t3 : itree E C),
    euttNoRet t1 t2 -> euttNoRet t2 t3 -> euttNoRet t1 t3.
Proof.
  intros. unfold euttNoRet in *.
  eapply eqit_mono with (b1 := true) (b2 := true)
    (RR := rcompose (fun (_:A)(_:B) => False) (fun (_:B)(_:C) => False)); auto.
  - intros x y Hc. inversion Hc; contradiction.
  - eapply eqit_trans; eauto.
Qed.


#[global] Instance proper_euttNoRet {E A B} {R R'} : Proper ((@eutt E A A R) ==> (@eutt E B B R') ==> iff) (euttNoRet).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34. split; intros.
  - apply euttNoRet_all_infinite in H as Ht1. apply euttNoRet_sym in H. 
    apply euttNoRet_all_infinite in H as Ht3.
    apply euttNoRet_trans with (t2 := t3).
    + apply euttNoRet_trans with (t2 := t1).
      * apply euttNoRet_sym. eapply all_infinite_euttNoRet; eauto.
      * apply euttNoRet_sym. auto.
    + eapply all_infinite_euttNoRet; eauto.
  - apply euttNoRet_all_infinite in H as Ht2. 
    apply euttNoRet_sym in H. apply euttNoRet_all_infinite in H as Ht3.
    assert (euttNoRet t1 t2).
    { 
      apply euttNoRet_sym. apply eutt_flip in Ht12. 
      eapply all_infinite_euttNoRet; eauto.
    }
    assert (euttNoRet t3 t4).
    {
      apply euttNoRet_sym. apply eutt_flip in Ht34.
      eapply all_infinite_euttNoRet; eauto.
    }
    apply euttNoRet_sym in H.
    apply euttNoRet_trans with (t2 := t4).
    + apply euttNoRet_trans with (t2 := t2); auto.
    + apply euttNoRet_sym. auto.
Qed.

Definition noret_cast {E A B} (t : itree E A) : itree E B :=
  t >>= fun _ => ITree.spin.

Lemma noret_cast_nop : forall (E : Type -> Type) (A : Type) (t : itree E A),
    all_infinite t -> t ≈ noret_cast t.
Proof.
  intros. apply euttNoRet_subrel. apply noret_bind_nop. auto.
Qed.

#[global] Instance proper_noret_cast {E R1 R2} : Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq) noret_cast.
Proof.
  intros t1 t2 Heutt. unfold noret_cast. cbn. rewrite Heutt. reflexivity.
Qed.

Ltac infer_noret H :=
  match type of H with
  | euttNoRet ?t1 ?t2 =>
      apply euttNoRet_sym in H as ?H1;
      apply euttNoRet_all_infinite in H1;
      apply euttNoRet_all_infinite in H as ?H
  end.

Lemma noret_cast_cast E (A B : Type) (t1 t2 : itree E A) (R : A -> A -> Prop) (R' : B -> B -> Prop)
  : all_infinite t1 -> eutt R t1 t2 -> eutt R' (noret_cast t1) (noret_cast t2).
Proof.
  intros. apply euttNoRet_subrel.
  apply all_infinite_euttNoRet in H0; auto.
  infer_noret H0.
  apply euttNoRet_trans with (t2 := t2); try apply noret_bind_nop; auto.
  apply euttNoRet_trans with (t2 := t1); auto.
  apply euttNoRet_sym. apply noret_bind_nop. auto.
Qed.
