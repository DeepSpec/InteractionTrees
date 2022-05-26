From Coq Require Import
     Morphisms
.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Infinite
.

From Paco Require Import paco.

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
  intros. pcofix CIH. pfold. red. cbn. constructor. right.
  eauto.
Qed.

Lemma noret_bind_nop : forall (E : Type -> Type) (A B : Type) (t : itree E A) (f : A -> itree E B),
    all_infinite t -> euttNoRet t (t >>= f).
Proof.
  intros. einit. generalize dependent t. ecofix CIH. intros t Hdivt. pinversion Hdivt.
  - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
    cbn. rewrite Ht.
    assert (ITree.bind (Tau t0) f ≅ Tau (ITree.bind t0 f)); try apply bind_tau.
    setoid_rewrite H1. etau.
  - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
    cbn. rewrite Ht. rewrite bind_vis. evis.
Qed.   

Lemma euttNoRet_subrel : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                               (ta : itree E A) (tb : itree E B), 
    euttNoRet ta tb -> eutt R ta tb.
Proof.
  intros.
  eapply eutt_subrel with (R1 := fun a b => False); tauto.
Qed.

Lemma all_infinite_euttNoRet : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                            (ta : itree E A) (tb : itree E B),
    all_infinite ta -> eutt R ta tb -> euttNoRet ta tb.
Proof.
  (* oddly had trouble doing this with euttG, maybe I should reread the gpaco paper*)
  intros E A B R. pcofix CIH. pstep. intros ta tb Hdiv Heutt.
  punfold Heutt. unfold_eqit. dependent induction Heutt; pclearbot.
  - exfalso. clear CIH. specialize (itree_eta ta) as Hta.
    rewrite <- x0 in Hta. rewrite Hta in Hdiv. pinversion Hdiv.
  - rewrite <- x0. rewrite <- x. constructor. right.
    assert (m1 ≈ ta).
    { specialize (itree_eta ta) as Hta. rewrite <- x0 in Hta.
      rewrite Hta. rewrite tau_eutt. reflexivity. }
    assert (m2 ≈ tb).
    { specialize (itree_eta tb) as Htb. rewrite <- x in Htb.
      rewrite Htb. rewrite tau_eutt. reflexivity. }
    apply CIH; auto.
    rewrite H. auto.
  - rewrite <- x0. rewrite <- x. constructor.
    intros. right. apply CIH; auto with itree.
    specialize (itree_eta ta) as Hta. rewrite <- x0 in Hta.
    rewrite Hta in Hdiv. pinversion Hdiv.
    dependent destruction H2. apply H0.
  - rewrite <- x. constructor; auto. eapply IHHeutt; eauto.
    assert (t1 ≈ ta).
    { specialize (itree_eta ta) as Hta. rewrite <- x in Hta.
      rewrite Hta. rewrite tau_eutt. reflexivity. }
    rewrite H. auto.
  - rewrite <- x. constructor; auto.
Qed.
     
Lemma euttNoRet_all_infinite : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    euttNoRet t1 t2 -> all_infinite t1.
Proof.
  intros A B. pcofix CIH. intros. pfold. red.
  punfold H0.
  unfold_eqit.
  dependent induction H0; try contradiction; pclearbot.
  - rewrite <- x0. constructor. right. eapply CIH; eauto.
  - rewrite <- x0. constructor. intros. right. eapply CIH; eauto. eapply REL.
  - rewrite <- x. constructor. right. eapply CIH with (t2 := t2); eauto. 
    pfold. auto.
  -  eapply IHeqitF; eauto.
Qed.


Lemma euttNoRet_sym : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    euttNoRet t1 t2 -> euttNoRet t2 t1.
Proof.
  intros E A B. pcofix CIH. intros. pfold. red.
  punfold H0. unfold_eqit.
  dependent induction H0; try contradiction; pclearbot.
  - rewrite <- x0. rewrite <- x. constructor. right. auto.
  - rewrite <- x0. rewrite <- x. constructor. intros. unfold id.
    right. apply CIH. apply REL.
  - rewrite <- x. constructor; auto.
  - rewrite <- x. constructor; auto.
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
  apply eutt_subrel with (R1 := @rcompose A B C (fun a b => False) (fun b c => False) ).
  - intros. inversion H1; contradiction.
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
