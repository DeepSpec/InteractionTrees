From Coq Require Import Logic.Classical_Prop.
From Paco Require Import paco.

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

  Inductive wf_from : A -> Prop :=
    | base (a : A) : (forall a', ~ (r a a')) -> wf_from a
    | step (a : A) : (forall a', r a a' -> wf_from a') -> wf_from a
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

  
End IterRel.


