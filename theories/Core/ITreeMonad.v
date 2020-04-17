(* SAZ: I'm not sure where in the library this should live.
    The Monad instance for itree is in ITreeDefinition but we want
    to define EqM and MonadLaws instances too.
*)
From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus.

Import RelNotations.
Open Scope relationH_scope.

Instance EqmR_ITree {E} : EqmR (itree E) := {| eqmR := fun a b => eutt |}.

From Coq Require Import
     Morphisms
     Program.Equality.

Lemma compose_rcompose_equiv : forall {A B C} (R1 : relationH A B) (R2 : relationH B C),
  (rcompose R1 R2) ≡ (compose R2 R1) .
Proof.
  intros.
  split; unfold compose, subrelationH.
  - intros. inversion H. exists r2; split; assumption.
  - intros. edestruct H as (? & ? & ?).
    econstructor; eassumption.
Qed.

Instance EqmR_OK_ITree {E} : EqmR_OK (itree E).
Proof.
  split; try typeclasses eauto; unfold eqmR, EqmR_ITree.
  - intros until C. unfold eutt in *.
    intros R1 R2 ma mb mc HR1 HR2.
    setoid_rewrite <- compose_rcompose_equiv.
    eapply eqit_trans; eassumption.
  - intros A B. unfold eq_rel. split.
    + pcofix CIH. intros x y H.
      pstep. red. punfold H. red in H.
      remember (observe x) as x'.
      remember (observe y) as y'.
      generalize dependent x. generalize dependent y.
      induction H; intros.
      * constructor. red in REL. assumption.
      * constructor. destruct REL. right.
        eapply CIH. apply H.
        destruct H.
      * constructor. red in REL. intros. unfold id.
        specialize (REL v).
        destruct REL. right. eapply CIH. apply H.
        destruct H.
      * constructor. assumption. eapply IHeqitF. eassumption.
        reflexivity.
      * constructor. assumption. eapply IHeqitF. reflexivity.
        eassumption.
    + pcofix CIH. intros x y H.
      pstep. red. punfold H. red in H.
      remember (observe x) as x'.
      remember (observe y) as y'.
      generalize dependent x. generalize dependent y.
      induction H; intros.
      * constructor. red. assumption.
      * constructor. destruct REL. right.
        eapply CIH. apply H.
        destruct H.
      * constructor. red in REL. intros. unfold id.
        specialize (REL v).
        destruct REL. right. eapply CIH. apply H.
        destruct H.
      * constructor. assumption. eapply IHeqitF.
        reflexivity. eassumption.
      * constructor. assumption. eapply IHeqitF.
        eassumption. reflexivity.
  - intros A B. constructor.
    + intro H2. rewrite <- H.
      Typeclasses eauto := 7.
      rewrite H0 in H2. rewrite <- H1.
      (* IY: Why doesn't this rewrite work? *)
      (* rewrite H1 in H2.  *)
      apply H2.
    + intro H2. rewrite H.
      rewrite <- H0 in H2.
      rewrite H1. apply H2.
  - intros A B. do 3 red.
    intros x y. pcofix CIH. pstep. red.
    intros sub a b H.
    do 2 red in H. punfold H. red in H.
    remember (observe a) as a'.
    remember (observe b) as b'.
    generalize dependent a. generalize dependent b.
    induction H; intros; eauto.
    + constructor. red in REL. destruct REL.
      right. apply CIH. assumption. assumption.
      destruct H.
    + constructor. red in REL. intros.
      specialize (REL v). unfold id.
      destruct REL. right. apply CIH. assumption. assumption.
      destruct H.
Qed.

Instance EqmRMonad_ITree {E} : EqmRMonad (itree E).
Proof.
  split.
  - intros. apply eqit_Ret. assumption.
  - intros.
    eapply eqit_bind'; eassumption.
  - intros.
    unfold bind, ret, Monad_itree. rewrite bind_ret_l.
    apply f_OK. assumption.
  - intros.
    unfold bind, ret, Monad_itree. rewrite bind_ret_r.
    assumption.
  - intros.
    unfold bind, Monad_itree. rewrite bind_bind.
    eapply eutt_clo_bind; [ eassumption | ].
    intros; eapply eutt_clo_bind.
    apply f_OK; assumption.
    intros; apply g_OK; assumption.
Qed.


Instance MonadLaws_ITree {E} : MonadLaws (itree E).
Proof.
  constructor.
  - intros a b f x.
    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqmR_ITree. rewrite bind_ret_l. reflexivity.
  - intros a x.    unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqmR_ITree. rewrite bind_ret_r. reflexivity.
  - intros a b c x f g. unfold Monad.bind, Monad.ret, Monad_itree.
    unfold eqm, EqmR_ITree. rewrite bind_bind. reflexivity.
  - unfold Monad.bind, Monad_itree.
    intros.
    repeat red.
    intros.
    apply eqit_bind; auto.
Qed.
