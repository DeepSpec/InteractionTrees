From Coq Require Import Logic.Classical_Prop.
From Paco Require Import paco.
Require Import Omega.
Section IterRel.

  Context (A : Type).
  Context (r : A -> A -> Prop).

  Variant not_wf_F (F : A -> Prop) (a : A) : Prop :=
    | not_wf (a' : A) (Hrel : r a a') (Hcorec : F a') .
  Hint Constructors not_wf_F.

  Lemma not_wf_F_mono sim sim' a 
        (IN : not_wf_F sim a)
        (LE : sim <1= sim') : not_wf_F sim' a.
  Proof.
    destruct IN. eauto.
  Qed.
        
  Lemma not_wf_F_mono' : monotone1 not_wf_F.
  Proof.
    red. intros. eapply not_wf_F_mono; eauto.
  Qed.
  Hint Resolve not_wf_F_mono' : paco.

  Definition not_wf_from : A -> Prop :=
    paco1 not_wf_F bot1.

  Inductive wf_from (a : A) : Prop :=
    | base : (forall a', ~ (r a a')) -> wf_from a
    | step : (forall a', r a a' -> wf_from a') -> wf_from a
  .
  Hint Constructors wf_from.
  Lemma neg_wf_from_not_wf_from_l : forall (a : A),
      ~(wf_from a) -> not_wf_from a.
  Proof.
    pcofix CIH. intros. pfold. destruct (classic (exists a', r a a' /\ ~ ( wf_from a') )).
    - destruct H as [a' [Hr Hwf] ]. econstructor; eauto.
    - assert (forall a', ~ r a a' \/ wf_from a').
      {
        intros.
        destruct (classic (r a a')); auto. destruct (classic (wf_from a')); auto.
        exfalso. apply H. exists a'. auto.
      }
      clear H.
      exfalso. apply H0. clear H0. apply step. intros. destruct (H1 a'); auto.
  Qed.

  Lemma neg_wf_from_not_wf_from_r : forall (a : A),
      not_wf_from a -> ~ (wf_from a).
  Proof.
    intros. intro Hcontra. punfold H.  inversion H. pclearbot. clear H. generalize dependent a'. 
    induction Hcontra; intros.
    - apply H in Hrel. auto.
    - punfold Hcorec. inversion Hcorec. pclearbot. specialize (H0 a' Hrel a'0 Hrel0).
      auto.
  Qed.

  Lemma neg_wf_from_not_wf_from : forall (a : A),
      not_wf_from a <-> ~(wf_from a).
  Proof.
    split; try apply neg_wf_from_not_wf_from_r; try apply neg_wf_from_not_wf_from_l.
  Qed.

  Lemma classic_wf : forall (a : A), wf_from a \/ not_wf_from a.
  Proof.
    intros. destruct (classic (wf_from a)); auto.
    apply neg_wf_from_not_wf_from in H. auto.
  Qed.

  Lemma intro_not_wf : forall (P : A -> Prop) (f : A -> A) (a : A),
    P a -> (forall a1 a2, P a1 -> r a1 a2 -> P a2 ) -> (forall a, P a -> r a (f a)) ->
    not_wf_from a.
  Proof.
    intros. generalize dependent a. pcofix CIH. intros. pfold.
    apply not_wf with (a' := f a).
    - auto using H1.
    - right. apply CIH. eapply H0; eauto.
  Qed.

  Lemma intro_wf : forall (P : A-> Prop) (m : A -> nat) (a : A),
      P a -> (forall a1 a2, P a1 -> r a1 a2 -> P a2 ) -> 
      (forall a1 a2, P a1 -> r a1 a2 -> m a2 < m a1) -> wf_from a.
  Proof.
    intros. remember (m a) as ma. assert (m a <= ma). omega. clear Heqma. 
    generalize dependent a.  
    induction (ma) as [  | n IHn] eqn : Heq.
    - subst. intros. apply base. intros. intro.  
      assert (~ m a' < m a).
      {  omega. }
      apply H4. clear H4. auto.
    - intros. Abort.


  
End IterRel.

Lemma no_inf_dec_seq_aux : forall  (r : nat -> nat -> Prop) (n n': nat),
    n' <= n ->
    (forall n1 n2, r n1 n2 -> n2 < n1) ->
     wf_from nat r n -> wf_from nat r n'.
  Proof.
    intros. generalize dependent n'. 
    induction H1 as [n Hn| n Hn].
    - 
        Abort.
