From Paco Require Import paco2.
Require Import Program.

Set Implicit Arguments.

Section Respectful2.
  Variable T0: Type.
  Variable T1: forall (x0: @T0), Type.
  Definition rel := rel2 T0 T1.

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone2 gf.

  Inductive sound2 (clo: rel -> rel): Prop :=
  | sound5_intro
      (MON: monotone2 clo)
      (SOUND:
         forall r (PFIX: r <2= gf (clo r)),
           r <2= paco2 gf bot2)
  .
  Hint Constructors sound2.

  Structure respectful2 (clo: rel -> rel) : Prop := respectful2_intro {
    MON: monotone2 clo;
    RESPECTFUL:
      forall l r (LE: l <2= r) (GF: l <2= gf r),
        clo l <2= gf (clo r);
  }.
  Hint Constructors respectful2.

  Inductive gres2 (r: rel) e1 e2: Prop :=
  | gres2_intro
      clo
      (RES: respectful2 clo)
      (CLO: clo r e1 e2)
  .
  Hint Constructors gres2.

  Lemma gfclo2_mon: forall clo, sound2 clo -> monotone2 (compose gf clo).
  Proof. intros; destruct H; eauto using gf_mon. Qed.
  Hint Resolve gfclo2_mon : paco.

  Lemma sound2_is_gf: forall clo (UPTO: sound2 clo),
      paco2 (compose gf clo) bot2 <2= paco2 gf bot2.
  Proof.
    intros. punfold PR. edestruct UPTO.
    eapply (SOUND (paco2 (compose gf clo) bot2)); eauto.
    intros. punfold PR0.
    eapply (gfclo2_mon UPTO); eauto.
    intros. destruct PR1; eauto. contradiction.
  Qed.

  Lemma respectful2_is_sound2: respectful2 <1= sound2.
  Proof.
    intro clo.
    set (rclo := fix rclo clo n (r: rel) :=
           match n with
           | 0 => r
           | S n' => rclo clo n' r \2/ clo (rclo clo n' r)
           end).
    intros. destruct PR. econstructor; eauto.
    intros. set (rr e1 e2 := exists n, rclo clo n r e1 e2).
    assert (rr x0 x1) by (exists 0; eauto); clear PR.
    cut (forall n, rclo clo n r <2= gf (rclo clo (S n) r)).
    { intro X; revert x0 x1 H; pcofix CIH; intros.
      unfold rr in *; destruct H0; eauto 10 using gf_mon. }
    induction n; intros; [simpl; eauto using gf_mon|].
    simpl in *; destruct PR; [eauto using gf_mon|].
    eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
  Qed.

  Lemma respectful2_compose
        clo1 clo2
        (RES1: respectful2 clo1)
        (RES2: respectful2 clo2):
    respectful2 (compose clo1 clo2).
  Proof.
    intros. destruct RES1, RES2.
    econstructor.
    - repeat intro. eapply MON0; eauto.
    - intros. eapply RESPECTFUL0; [| |apply PR].
      + intros. eapply MON1; eauto.
      + intros. eapply RESPECTFUL1; eauto.
  Qed.

  Lemma grespectful2_respectful2: respectful2 gres2.
  Proof.
    econstructor; repeat intro.
    - destruct IN; destruct RES; exists clo; eauto.
    - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
  Qed.

  Lemma gfgres2_mon: monotone2 (compose gf gres2).
  Proof.
    destruct grespectful2_respectful2; eauto using gf_mon.
  Qed.
  Hint Resolve gfgres2_mon : paco.

  Lemma grespectful2_greatest: forall clo (RES: respectful2 clo), clo <3= gres2.
  Proof.
    eauto.
  Qed.

  Lemma grespectful2_incl: forall r, r <2= gres2 r.
  Proof.
    intros; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve grespectful2_incl.

  Lemma grespectful2_compose: forall clo (RES: respectful2 clo) r,
      clo (gres2 r) <2= gres2 r.
  Proof.
    intros; eapply grespectful2_greatest with (clo := compose clo gres2);
      eauto using respectful2_compose, grespectful2_respectful2.
  Qed.

  Lemma grespectful2_incl_rev: forall r,
      gres2 (paco2 (compose gf gres2) r) <2= paco2 (compose gf gres2) r.
  Proof.
    intro r; pcofix CIH; intros; pfold.
    eapply gf_mon, grespectful2_compose, grespectful2_respectful2.
    destruct grespectful2_respectful2; eapply RESPECTFUL0, PR; intros; [apply grespectful2_incl; eauto|].
    punfold PR0.
    eapply gfgres2_mon; eauto; intros; destruct PR1; eauto.
  Qed.

  Inductive rclo2 clo (r: rel): rel :=
  | rclo2_incl
      e1 e2
      (R: r e1 e2):
      @rclo2 clo r e1 e2
  | rclo2_step'
      r' e1 e2
      (R': r' <2= rclo2 clo r)
      (CLOR':clo r' e1 e2):
      @rclo2 clo r e1 e2
  | rclo2_gf
      r' e1 e2
      (R': r' <2= rclo2 clo r)
      (CLOR':@gf r' e1 e2):
      @rclo2 clo r e1 e2
  .
  
  Lemma rclo2_mon clo:
    monotone2 (rclo2 clo).
  Proof.
    repeat intro. induction IN; eauto using rclo2.
  Qed.
  Hint Resolve rclo2_mon: paco.

  Lemma rclo2_base
        clo
        (MON: monotone2 clo):
    clo <3= rclo2 clo.
  Proof.
    simpl. intros. econstructor 2; eauto.
    eapply MON; eauto using rclo2.
  Qed.

  Lemma rclo2_step
        (clo: rel -> rel) r:
    clo (rclo2 clo r) <2= rclo2 clo r.
  Proof.
    intros. econstructor 2; eauto.
  Qed.

  Lemma rclo2_rclo2
        clo r
        (MON: monotone2 clo):
    rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
  Proof.
    intros. induction PR; eauto using rclo2.
  Qed.

  Structure weak_respectful2 (clo: rel -> rel) : Prop := weak_respectful2_intro {
    WEAK_MON: monotone2 clo;
    WEAK_RESPECTFUL:
      forall l r (LE: l <2= r) (GF: l <2= gf r),
        clo l <2= gf (rclo2 clo r);
  }.
  Hint Constructors weak_respectful2.

  Lemma weak_respectful2_respectful2
        clo (RES: weak_respectful2 clo):
    respectful2 (rclo2 clo).
  Proof.
    inversion RES. econstructor; eauto with paco. intros.
    induction PR; intros.
    - eapply gf_mon; eauto. intros.
      apply rclo2_incl. auto.
    - eapply gf_mon. 
      + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR']. 
        intros. eapply rclo2_mon; eauto.
      + intros. apply rclo2_rclo2; auto.
    - eapply gf_mon; eauto using rclo2.
  Qed.

  Lemma upto2_init:
      paco2 (compose gf gres2) bot2 <2= paco2 gf bot2.
  Proof.
    apply sound2_is_gf; eauto.
    apply respectful2_is_sound2.
    apply grespectful2_respectful2.
  Qed.

  Lemma upto2_final:
    paco2 gf <3= paco2 (compose gf gres2).
  Proof.
    pcofix CIH. intros. punfold PR. pfold.
    eapply gf_mon; [|apply grespectful2_incl].
    eapply gf_mon; eauto. intros. right. inversion PR0; auto.
  Qed.

  Lemma upto2_step
        r clo (RES: weak_respectful2 clo):
    clo (paco2 (compose gf gres2) r) <2= paco2 (compose gf gres2) r.
  Proof.
    intros. apply grespectful2_incl_rev.
    assert (RES' := weak_respectful2_respectful2 RES).
    eapply grespectful2_greatest. eauto.
    eapply rclo2_base; eauto.
    inversion RES. auto.
  Qed.

  Lemma upto2_step_under
     r clo (RES: weak_respectful2 clo):
   clo (gres2 r) <2= gres2 r.
Proof.
  intros. apply weak_respectful2_respectful2 in RES; eauto.
  eapply grespectful2_compose; eauto. eauto using rclo2.
Qed.

End Respectful2.

Hint Constructors sound2.
Hint Constructors respectful2.
Hint Constructors gres2.
Hint Resolve gfclo2_mon : paco.
Hint Resolve gfgres2_mon : paco.
Hint Resolve grespectful2_incl.
Hint Resolve rclo2_mon: paco.
Hint Constructors weak_respectful2.

Ltac pupto2_init := eapply upto2_init; eauto with paco.
Ltac pupto2_final := first [eapply upto2_final; eauto with paco | eapply grespectful2_incl].
Ltac pupto2 H := first [eapply upto2_step|eapply upto2_step_under]; [|exact H|]; eauto with paco.
