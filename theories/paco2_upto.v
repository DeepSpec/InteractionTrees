Require Import Paco.paco2.
Require Export Program.
Set Implicit Arguments.

Section Respectful2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Inductive sound2 (clo: rel -> rel): Prop :=
| sound2_intro
    (MON: monotone2 clo)
    (SOUND:
       forall r (PFIX: r <2= gf (clo r)),
         r <2= paco2 gf bot2)
.
Hint Constructors sound2.

Structure respectful2 (clo: rel -> rel) : Prop :=
  respectful2_intro {
      MON: monotone2 clo;
      RESPECTFUL:
        forall l r (LE: l <2= r) (GF: l <2= gf r),
          clo l <2= gf (clo r);
    }.
Hint Constructors respectful2.

Inductive gres2 (r: rel) e0 e1 : Prop :=
| gres2_intro
    clo
    (RES: respectful2 clo)
    (CLO: clo r e0 e1)
.
Hint Constructors gres2.
Lemma gfclo2_mon: forall clo, sound2 clo -> monotone2 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo2_mon : paco.

Lemma sound2_is_gf: forall clo (UPTO: sound2 clo),
    paco2 (compose gf clo) bot2 <2= paco2 gf bot2.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco2 (compose gf clo) bot2)).
  - intros. punfold PR0.
    eapply (gfclo2_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful2_is_sound2: respectful2 <1= sound2.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \2/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 := exists n, rclo clo n r e0 e1).
  assert (rr x0 x1) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <2= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 H; pcofix CIH; intros.
    unfold rr in *; destruct H0.
    pfold. eapply gf_mon.
    - apply X. apply H.
    - intros. right. apply CIH. exists (S x). apply PR.
  }
  induction n; intros.
  - eapply gf_mon.
    + clear RESPECTFUL0. eapply PFIX, PR.
    + intros. right. eapply PR0.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H0|]. intros. left. apply PR.
    + eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; intros.
      * left; apply PR.
      * apply H0.
      * right; apply PR.
Qed.

Lemma respectful2_compose
      clo0 clo1
      (RES0: respectful2 clo0)
      (RES1: respectful2 clo1):
  respectful2 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful2_respectful2: respectful2 gres2.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
    constructor; [eapply MON0|].
    intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
    eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
    intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres2_mon: monotone2 (compose gf gres2).
Proof.
  destruct grespectful2_respectful2.
  unfold monotone2. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres2_mon : paco.

Lemma grespectful2_greatest: forall clo (RES: respectful2 clo), clo <3= gres2.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful2_incl: forall r, r <2= gres2 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful2_incl.

Lemma grespectful2_compose: forall clo (RES: respectful2 clo) r,
    clo (gres2 r) <2= gres2 r.
Proof.
  intros; eapply grespectful2_greatest with (clo := compose clo gres2); [|apply PR].
  apply respectful2_compose; [apply RES|apply grespectful2_respectful2].
Qed.

Lemma grespectful2_incl_rev: forall r,
    gres2 (paco2 (compose gf gres2) r) <2= paco2 (compose gf gres2) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful2_compose, grespectful2_respectful2.
  destruct grespectful2_respectful2; eapply RESPECTFUL0, PR; intros; [apply grespectful2_incl; right; apply CIH, grespectful2_incl, PR0|].
  punfold PR0.
  eapply gfgres2_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco2_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo2 clo (r: rel): rel :=
| rclo2_incl
    e0 e1
    (R: r e0 e1):
    @rclo2 clo r e0 e1
| rclo2_step'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR':clo r' e0 e1):
    @rclo2 clo r e0 e1
| rclo2_gf
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR':@gf r' e0 e1):
    @rclo2 clo r e0 e1
.
Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo2_mon: paco.

Lemma rclo2_base
      clo
      (MON: monotone2 clo):
  clo <3= rclo2 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo2_step
      (clo: rel -> rel) r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo2_rclo2
      clo r
      (MON: monotone2 clo):
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful2 (clo: rel -> rel) : Prop :=
  weak_respectful2_intro {
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
  inversion RES. econstructor; [eapply rclo2_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo2_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo2_mon; [apply R', PR|apply LE].
    + intros. apply rclo2_rclo2;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo2_mon; [apply R', PR| apply LE].
Qed.

Lemma upto2_init:
  paco2 (compose gf gres2) bot2 <2= paco2 gf bot2.
Proof.
  apply sound2_is_gf.
  apply respectful2_is_sound2.
  apply grespectful2_respectful2.
Qed.

Lemma upto2_final:
  paco2 gf <3= paco2 (compose gf gres2).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful2_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto2_step
      r clo (RES: weak_respectful2 clo):
  clo (paco2 (compose gf gres2) r) <2= paco2 (compose gf gres2) r.
Proof.
  intros. apply grespectful2_incl_rev.
  assert (RES' := weak_respectful2_respectful2 RES).
  eapply grespectful2_greatest; [apply RES'|].
  eapply rclo2_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto2_step_under
      r clo (RES: weak_respectful2 clo):
  clo (gres2 r) <2= gres2 r.
Proof.
  intros. apply weak_respectful2_respectful2 in RES.
  eapply grespectful2_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
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

Ltac pupto2_init := eapply upto2_init; [eauto with paco|].
Ltac pupto2_final := first [eapply upto2_final; [eauto with paco|] | eapply grespectful2_incl].
Ltac pupto2 H := first [eapply upto2_step|eapply upto2_step_under]; [eauto with paco|eapply H|].
