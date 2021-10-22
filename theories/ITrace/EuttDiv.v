From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Core.Divergence
     (* Dijkstra.PureITreeBasics
     Dijkstra.DelaySpecMonad *)
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Defines eutt_div, a relation for relating ITrees 
    over different return types, that never return and whose events are bisimilar. Also contains div_cast, a function that casts ITrees that never return from one return type to another while preserving its events.
*)

Definition eutt_div {E} {A B : Type} (ta : itree E A) (tb : itree E B) := 
  eutt (fun a b => False) ta tb.


Lemma eutt_div_spin : forall (E : Type -> Type) (A B : Type), @eutt_div E A B ITree.spin ITree.spin.
Proof.
  intros. pcofix CIH. pfold. red. cbn. constructor. right.
  eauto.
Qed.


Lemma bind_tau : forall (E : Type -> Type) (A B : Type) (t : itree E A) (f : A -> itree E B),
    ITree.bind (Tau t) f ≅ Tau (ITree.bind t f).
Proof.
  intros. pfold. red. cbn. constructor. left. 
  assert ( (ITree.bind t f) ≅  (ITree.bind t f)); try reflexivity; auto.
Qed.

Lemma bind_vis : forall (E : Type -> Type) (A B C : Type) (e : E C) (k : C -> itree E A) (f : A -> itree E B),
    ITree.bind (Vis e k) f ≅ Vis e (fun a => ITree.bind (k a) f). 
Proof.
  intros. cbn. pfold. red. cbn. constructor. intros. unfold id. left.
  assert (ITree.bind (k v) (fun x => f x) ≅ ITree.bind (k v) (fun x => f x)); try reflexivity. 
  auto.
Qed.

Lemma div_bind_nop : forall (E : Type -> Type) (A B : Type) (t : itree E A) (f : A -> itree E B),
    must_diverge t -> eutt_div t (t >>= f).
Proof.
  intros. einit. generalize dependent t. ecofix CIH. intros t Hdivt. pinversion Hdivt.
  - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
    cbn. rewrite Ht.
    assert (ITree.bind (Tau t0) f ≅ Tau (ITree.bind t0 f)); try apply bind_tau.
    setoid_rewrite H1. etau.
  - specialize (itree_eta t) as Ht. rewrite <- H in Ht.
    cbn. rewrite Ht. rewrite bind_vis. evis. intros.
    apply euttG_base. left. apply CIHH. apply H0.
Qed.   

Lemma eutt_subrel : forall (E : Type -> Type) (A B : Type) (R1 R2 : A -> B -> Prop)
                           (ta : itree E A) (tb : itree E B),
    (forall a b, R1 a b -> R2 a b) -> eutt R1 ta tb -> eutt R2 ta tb.
Proof.
  intros.
  eapply eqit_mon; eauto.
Qed.

Lemma eutt_flip : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop)
                         (ta : itree E A) (tb : itree E B),
    eutt R ta tb -> eutt (flip R) tb ta.
Proof.
  intros. apply eqit_flip. 
  eapply eutt_subrel with (R1 := R); eauto.
Qed.
    
Lemma eutt_div_subrel : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                               (ta : itree E A) (tb : itree E B), 
    eutt_div ta tb -> eutt R ta tb.
Proof.
  intros.
  eapply eutt_subrel with (R1 := fun a b => False); tauto.
Qed.


Lemma eutt_imp_div : forall (E : Type -> Type) (A B : Type) (R : A -> B -> Prop) 
                            (ta : itree E A) (tb : itree E B),
    must_diverge ta -> eutt R ta tb -> eutt_div ta tb.
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
    intros. right. apply CIH; auto.
    specialize (itree_eta ta) as Hta. rewrite <- x0 in Hta.
    rewrite Hta in Hdiv. pinversion Hdiv.
    apply inj_pair2 in H2. subst. apply H0.
  - rewrite <- x. constructor; auto. eapply IHHeutt; eauto.
    assert (t1 ≈ ta).
    { specialize (itree_eta ta) as Hta. rewrite <- x in Hta.
      rewrite Hta. rewrite tau_eutt. reflexivity. }
    rewrite H. auto.
  - rewrite <- x. constructor; auto.
Qed.
     
Lemma eutt_div_imp_div : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    eutt_div t1 t2 -> must_diverge t1.
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


Lemma eutt_div_sym : forall (E : Type -> Type) (A B : Type) (t1 : itree E A) (t2 : itree E B),
    eutt_div t1 t2 -> eutt_div t2 t1.
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

Lemma must_diverge_bind : forall (E : Type -> Type) (R U: Type) (t : itree E R) 
                                 (f : R -> itree E U),
    must_diverge t -> must_diverge (bind t f).
Proof.
  intros. apply div_bind_nop with (B := U) (f := f) in H.
  apply eutt_div_sym in H. apply eutt_div_imp_div in H. auto.
Qed.
     
Lemma eutt_div_trans : forall (E : Type -> Type) (A B C : Type) (t1 : itree E A) 
                              (t2 : itree E B) (t3 : itree E C),
    eutt_div t1 t2 -> eutt_div t2 t3 -> eutt_div t1 t3.
Proof.
  intros. unfold eutt_div in *.
  apply eutt_subrel with (R1 := @rcompose A B C (fun a b => False) (fun b c => False) ).
  - intros. inversion H1; contradiction.
  - eapply eqit_trans; eauto.
Qed.


Global Instance proper_eutt_div {E A B} {R R'} : Proper ( (@eutt E A A R) ==> (@eutt E B B R') ==> iff) (eutt_div).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34. split; intros.
  - apply eutt_div_imp_div in H as Ht1. apply eutt_div_sym in H. 
    apply eutt_div_imp_div in H as Ht3.
    apply eutt_div_trans with (t2 := t3).
    + apply eutt_div_trans with (t2 := t1).
      * apply eutt_div_sym. eapply eutt_imp_div; eauto.
      * apply eutt_div_sym. auto.
    + eapply eutt_imp_div; eauto.
  - apply eutt_div_imp_div in H as Ht2. 
    apply eutt_div_sym in H. apply eutt_div_imp_div in H as Ht3.
    assert (eutt_div t1 t2).
    { 
      apply eutt_div_sym. apply eutt_flip in Ht12. 
      eapply eutt_imp_div; eauto.
    }
    assert (eutt_div t3 t4).
    {
      apply eutt_div_sym. apply eutt_flip in Ht34.
      eapply eutt_imp_div; eauto.
    }
    apply eutt_div_sym in H.
    apply eutt_div_trans with (t2 := t4).
    + apply eutt_div_trans with (t2 := t2); auto.
    + apply eutt_div_sym. auto.
Qed.

Definition div_cast {E A B} (t : itree E A) : itree E B :=
  t >>= fun _ => ITree.spin.

Lemma div_cast_nop : forall (E : Type -> Type) (A : Type) (t : itree E A),
    must_diverge t -> t ≈ div_cast t.
Proof.
  intros. apply eutt_div_subrel. apply div_bind_nop. auto.
Qed.

Global Instance proper_div_cast {E R1 R2} : Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq) div_cast.
Proof.
  intros t1 t2 Heutt. unfold div_cast. cbn. rewrite Heutt. reflexivity.
Qed.
