From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.Typ
     Basics.HeterogeneousRelations
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.CategoryMonad
     Basics.Monad
.

Import CatNotations.
Open Scope cat_scope.

(* Trying to define the EqmR version of PropM

   Problems:
   1. What does [eqmR R PA PB] mean?
        "equal propositions, modulo R"

    PA <= A

    PB <= B

    R <= (A * B) 

    PA * PB  <= R <= (A * B)


   Questions:
     -  must it be the case that [eq_rel (eqmR A A A) (m A)]  ?
     -  or would only one inclusion suffice?  (m A) <2= (eqmR A A A)
*)

Section PropM.

Definition PropM (X:typ) : typ := X ~~> prop_typ.

Definition ret_ (A:typ) (x:A) := 
  fun (y:A) => equalE A x y.


Program Definition ret_PropM (A:typ) : A -=-> (PropM A) :=
  -=->! (ret_ A) _.
Next Obligation.
  unfold ret_.
  do 2 red.
  intros; split; intros.
  - rewrite <- H. assumption.
  - rewrite H. assumption.
Qed.
Next Obligation.
  do 4 red.
  intros. cbn. 
  rewrite H0. rewrite H. reflexivity.
Qed.  

Program Definition bind_ (A B : typ) (k : A -=-> PropM B) (ma : PropM A) :=
  (fun b:B => exists (a:A), ma a /\ (k a b)).

Program Definition bind_PropM (A B : typ) (k : A -=-> PropM B) : (PropM A) -=-> (PropM B) :=
  -=->! (bind_ A B k) _.
Next Obligation.
  unfold bind_.
  do 2 red.
  intros.
  split; intros (a & PA & KA).
  - exists a. split; auto. rewrite <- H. assumption.
  - exists a. split; auto. rewrite H. assumption.
Qed.
Next Obligation.
  do 2 red.
  intros; cbn.
  unfold bind_.
  split; intros (a & PA & KA).
  - exists a. split. rewrite <- H. apply PA. 
    rewrite <- H0. assumption.
  - exists a. split. rewrite H. apply PA.
    rewrite H0. assumption.
Qed.    


Instance MonadPropM : Monad typ_proper PropM.
split.
- exact ret_PropM.
- exact bind_PropM.
Defined.  


Program Definition eqmR_PropM_ (A B : typ) (R : relationH A B) : relationH (PropM A) (PropM B) :=
  fun p : (PropM A × PropM B) =>
    (forall (a:A), (fst p @ a) -> exists (b:B), R @ (a, b) /\ (snd p @ b)) /\
    (forall (b:B), (snd p @ b) -> exists (a:A), R @ (a, b) /\ (fst p @ a)).
Next Obligation.
  do 2 red. 
  intros (PA1 & PB1) (PA2 & PB2) (HPA & HPB); cbn in *; split; intros (HA & HB); split; intros.
  - rewrite <- HPA in H.
    destruct (HA a H) as (b & Rb & H').
    exists b; split; auto. rewrite <- HPB. assumption.
  - rewrite <- HPB in H.
    destruct (HB b H) as (a & Ra & H').
    exists a; split; auto. rewrite <- HPA. assumption.
  - rewrite HPA in H.
    destruct (HA a H) as (b & Rb & H').
    exists b; split; auto. rewrite HPB. assumption.
  - rewrite HPB in H.
    destruct (HB b H) as (a & Ra & H').
    exists a; split; auto. rewrite HPA. assumption.
Qed.

Program Instance eqmR_PropM : EqmR PropM :=
  { eqmR := eqmR_PropM_ }.
Next Obligation.
  split.
  - repeat red.
    intros PA1 PA2 (HA & HB) a1 a2 HEQ; split; intros HX; cbn in *.
    + specialize (HA a1 HX). destruct HA as (a' & EQA & HP).
      rewrite <- HEQ. rewrite EQA. assumption.
    + specialize (HB a2 HX). destruct HB as (a' & EQA & HP).
      rewrite HEQ. rewrite <- EQA. assumption.
  - repeat red.
    intros PA1 PA2 HP; split; intros; cbn in *.
    exists a. split; [reflexivity|]. rewrite <- HP. assumption.
    exists b. split; [reflexivity|]. rewrite HP. assumption.
Qed.

Ltac destruct_all :=
  repeat match goal with
         | [ H : exists X, _ |- _ ] => destruct H
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ |- _ /\ _ ] => split
         end.

Ltac PER_symmetry :=
  match goal with
  | [ H : SymmetricH ?R,
      H1 : ?R @ (?x, ?y)
      |- ?R @ (?y, ?x) ] => apply (H _ H1)
  end.

Program Instance eqmR_OK_PropM : EqmR_OK PropM.
Next Obligation.
  repeat red.
  intros PA.
  split; intros; cbn in *.
  - exists a. split; auto. 
  - exists b. split; auto.
Qed.
Next Obligation.
  red.
  intros (PA & PB) (HA & HB); split; intros; cbn in *.
  - specialize (HB a H0). destruct_all.
    exists x. split; auto. PER_symmetry.
  - specialize (HA b H0). destruct_all.
    exists x. split; auto. PER_symmetry.
Qed.
Next Obligation.
  red.
  intros (P1 & P2) (Q1 & Q2) (EQP1 & EQP2) (EQQ1 & EQQ2) EQ; cbn in *.
  split; intros; cbn in *.
  - apply EQP1 in H0. destruct H0 as (b & HR1 & HB).
    rewrite EQ in HB.
    apply EQQ1 in HB.
    destruct_all.
    exists x. split. apply (H (a,b) (b,x)); auto. reflexivity. auto.


  - apply EQQ2 in H0. destruct H0 as (a & HR1 & HA).
    rewrite <- EQ in HA.
    apply EQP2 in HA. destruct HA as (c & HR2 & HC).
    exists c. split. apply (H (c,a) (a,b)); auto. reflexivity. auto.
Qed.    
Next Obligation.
  split.
  - intros a PA.
    apply H in PA. destruct PA as (b & HB & PB).
    apply H0 in PB. destruct PB as (c & HC & PC).
    exists c. split. exists b. split; auto. auto.
  - intros c PC.
    apply H1 in PC. destruct PC as (b & HB & PB).
    apply H2 in PB. destruct PB as (a & HA & PA).
    exists a. split. exists b. tauto. auto.
Qed.    
Next Obligation.
  split; repeat red; intros PA PB (HA & HB); split; cbn in *.
  - intros b HX. destruct (HB _ HX) as (b2 & HB2 & HPA).
    exists b2; tauto.
  - intros b HX. destruct (HA _ HX) as (b2 & HB2 & HPA).
    exists b2; tauto.
  - intros b HX. destruct (HB _ HX) as (b2 & HB2 & HPA).
    exists b2; tauto.
  - intros b HX. destruct (HA _ HX) as (b2 & HB2 & HPA).
    exists b2; tauto.
Qed.  
Next Obligation.
  do 2 red.
  intros R S (RS & SR). red in RS. red in SR.
  split; repeat red; intros PA PB (HX & HY); split; intros; cbn in *.
  - destruct (HX _ H) as (b & RB & PAB).
    exists b. split; auto.
  - destruct (HY _ H) as (a & RA & PAB).
    exists a. split; auto.
  - destruct (HX _ H) as (b & RB & PAB).
    exists b. split; auto.
  - destruct (HY _ H) as (a & RA & PAB).
    exists a. split; auto.
Qed.  
Next Obligation.
  do 2 red.
  intros R S RS. red in RS.
  repeat red. intros PA PB (HX & HY); split; intros; cbn in *.
  - destruct (HX _ H) as (b & RB & PAB).
    exists b. split; auto.
  - destruct (HY _ H) as (a & RA & PAB).
    exists a. split; auto.
Qed.

Lemma mayRet_PropM {A:typ} (ma : PropM A) (a : A) : (ma @ a) <-> mayRet PropM ma @ a.
Proof.
  split.
  - intros HM.
    do 6 red. intros.
    repeat red in EQ.
    destruct EQ.
    cbn in *.
    specialize (H a HM).
    destruct H as (b & RB & MAB).
    PER_reflexivityH; apply PH. 
  - intros HM.
    repeat red in HM.
    epose ((-=->! (fun a => (ma @ a)) _) : A -=-> prop_typ) as Q.
    assert (eqmR (diagonal_prop Q) @ (ma, ma)).
    { repeat red. split; cbn; intros; eauto. }
    assert (PER (diagonal_prop Q)) as PP.
    { constructor. apply (diagonal_prop_SymmetricH Q). apply (diagonal_prop_TransitiveH Q). }
    
    specialize (HM (diagonal_prop Q) PP H).
    destruct H as (HA & HB).
    cbn in *.
    tauto.
    
    
    Unshelve.
    cbn. repeat red. intros. split; intros. rewrite <- H. assumption. rewrite H. assumption. 
    
Qed.  


Lemma eqmR_bind_ProperH_PropM_old :
  forall {A1 A2 B1 B2 : typ}
    (RA : relationH A1 A2)
    (RB : relationH B1 B2)
    (ma1 : PropM A1) (ma2 : PropM A2)
    (kb1 : A1 -=-> PropM B1) (kb2 : A2 -=-> PropM B2),
    eqmR RA @ (ma1, ma2) ->
    (forall a1, mayRet PropM ma1 @ a1 ->
           exists (a2:A2), RA @ (a1, a2) /\ (mayRet PropM ma2 @ a2) /\ eqmR RB @ (kb1 @ a1, kb2 @ a2))
    ->
    (forall a2, mayRet PropM ma2 @ a2 ->
           exists (a1:A1), RA @ (a1, a2) /\ (mayRet PropM ma1 @ a1) /\ eqmR RB @ (kb1 @ a1, kb2 @ a2))
    ->
    eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2).
Proof.
  intros A1 A2 B1 B2 RA RB ma1 ma2 kb1 kb2 EQMA SL SR.
  do 4 red. cbn.
  split.
  - intros b1 (a1 & HA1 & HKA).
    assert (mayRet PropM ma1 @ a1).  { rewrite <- mayRet_PropM. assumption. }
    specialize (SL a1 H).
    destruct SL as (a2 & RA2 & MR2 & (HEQK1 & HEQK2)).
    cbn in HEQK1, HEQK2.
    specialize (HEQK1 _ HKA).
    destruct HEQK1 as (b2 & RB2 & KB2).
    exists b2. split; auto. repeat red. exists a2. split.
    rewrite <- mayRet_PropM in MR2.  assumption.
    assumption.

  - intros b2 (a2 & HA2 & HKA).
    apply mayRet_PropM in HA2.
    specialize (SR a2 HA2).
    destruct SR as (a1 & RA1 & MR1 & (HEQK2 & HEQK1)).
    cbn in HEQK1, HEQK2.
    specialize (HEQK1 _ HKA).
    destruct HEQK1 as (b1 & RB1 & KB1).
    exists b1. split; auto. repeat red. exists a1. split.
    rewrite <- mayRet_PropM in MR1.  assumption.
    assumption.
Qed.


Lemma image_eqmR_PropM {A : typ} (ma : PropM A) : eqmR (image PropM ma) @ (ma, ma).
Proof.
  repeat red.
  split.
  - intros a HMA; cbn in HMA.
    exists a. split; auto. do 3 red. intros.
    destruct EQ as (HX & HY).
    specialize (HX a HMA). destruct HX as (b & RB & HB).
    PER_reflexivityH; apply PH.
  - intros a HMA; cbn in HMA.
    exists a. split; auto. do 3 red. intros.
    destruct EQ as (HX & HY).
    specialize (HX a HMA). destruct HX as (b & RB & HB).
    PER_reflexivityH; apply PH.
Qed.    

Lemma eqmR_ret_inv_PropM : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
    eqmR RA @ ((ret @ a1 : PropM A1), (ret @ a2 : PropM A2)) -> RA @ (a1, a2).
Proof.
  intros.
  do 4 red in H.
  cbn in H.
  destruct H as (HX & HY). unfold ret_ in HX, HY.
  assert (a1 == a1) by reflexivity.
  specialize (HX a1 H).
  destruct HX as (b & HR & EQ).
  rewrite EQ. assumption.
Qed.  


Lemma mayRet_bind_PropM : forall {A B:typ} (ma : PropM A) (k : A -=-> PropM B) (b : B),
                    mayRet PropM (bind k @ ma) @ b -> exists a, mayRet PropM ma @ a /\ mayRet PropM (k @ a) @ b.
Proof.
  intros.
  rewrite <- mayRet_PropM in H.
  cbn in H. unfold bind_ in H.
  destruct H as (a & HA & HK).
  exists a. split. rewrite <- mayRet_PropM. assumption. rewrite <- mayRet_PropM. assumption.
Qed.

Lemma eqmR_mayRet_l_PropM : forall {A1 A2 : typ}
                      (ma1 : PropM A1) (ma2 : PropM A2)
                      (RA : relationH A1 A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
    forall a1, mayRet PropM ma1 @ a1 -> exists a2, RA @ (a1, a2) /\ mayRet PropM ma2 @ a2.
Proof.
  intros.
  destruct EQ as (HA & HB). cbn in HA, HB.
  rewrite <- mayRet_PropM in H.
  destruct (HA _ H) as (b & HR & HM).
  exists b. split; auto. rewrite <- mayRet_PropM. auto.
Qed.  
  

Lemma eqmR_mayRet_r_PropM : forall {A1 A2 : typ}
                      (ma1 : PropM A1) (ma2 : PropM A2)
                      (RA : relationH A1 A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
        forall a2, mayRet PropM ma2 @ a2 -> exists a1, RA @ (a1, a2) /\ mayRet PropM ma1 @ a1.
  intros.
  destruct EQ as (HA & HB). cbn in HA, HB.
  rewrite <- mayRet_PropM in H.
  destruct (HB _ H) as (a & HR & HM).
  exists a. split; auto. rewrite <- mayRet_PropM. auto.
Qed.  


Lemma eqmR_bind_refl_inv_PropM :
  forall {A : typ} {B : typ}
    (RB : relationH B B) (SH: SymmetricH RB) (TH: TransitiveH RB)
    (ma : PropM A) 
    (k : A -=-> PropM B),
    eqmR RB @ (bind k @ ma, bind k @ ma) ->
    exists (RA : relationH A A), 
      eqmR RA @ (ma, ma) /\
      (forall a, mayRet PropM ma @ a -> eqmR RB @ (k @ a, k @ a)).
Proof.
  intros.
  destruct H as (HX & HY).
  exists (A).
  split; intros; split; intros.
  - exists a. split. repeat red. cbn. reflexivity. assumption.
  - exists b. split. repeat red. cbn. reflexivity. assumption.
  - specialize (HX a0).
    assert (bind k @ ma @ a0).
    { repeat red. exists a. split. rewrite <- mayRet_PropM in H. apply H. apply H0. }
    apply HX in H1. destruct H1 as (b & HB & HK2).
    specialize (HY b).
    exists a0. cbn in *.

    split. PER_reflexivityH. cbn.  apply H0.
  - specialize (HX b).
    assert (bind k @ ma @ b).
    { repeat red. exists a. split. rewrite <- mayRet_PropM in H. apply H. apply H0. }
    apply HX in H1. destruct H1.
    specialize (HY b).
    assert (bind k @ ma @ b).
    { repeat red. exists a. split. rewrite <- mayRet_PropM in H. apply H. apply H0.  } 
    apply HY in H2. destruct H2.
    exists b.
    destruct H1 as (HR & HB).
    destruct H2 as (HS & HC).
    split. PER_reflexivityH. cbn. apply H0.
Qed.    

Lemma eqmR_bind_ProperH_PropM :
  forall {A1 A2 B1 B2 : typ}
    (RA : relationH A1 A2)
    (RB : relationH B1 B2)
    ma1 ma2
    (kb1 : A1 -=-> PropM B1) (kb2 : A2 -=-> PropM B2),
    eqmR RA @ (ma1, ma2) ->
    (forall (a1 : A1) (a2 : A2), mayRet PropM ma1 @ a1 -> mayRet PropM ma2 @ a2 -> RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2))
    ->
    eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2).
Proof.
  intros.
  repeat red.
  destruct H as (H1 & H2).
  Opaque mayRet.
  split; intros; cbn in *.
  - destruct H as (a1 & HA1 & HK1).
    specialize (H1 a1 HA1).
    destruct H1 as (a2 & HA2 & HM2).
    specialize (H0 a1 a2).
    assert (mayRet PropM ma1 @ a1).
    Transparent mayRet. 
    { cbn.  intros. destruct EQ as (HX &  HY). specialize (HX a1 HA1).
      destruct HX as (b & HR & _). PER_reflexivityH; apply PH. }
    assert (mayRet PropM ma2 @ a2).
    { cbn.  intros. destruct EQ as (HX &  HY). specialize (HX a2 HM2).
      destruct HX as (b & HR & _). PER_reflexivityH; apply PH. }
    specialize (H0 H H1 HA2).
    destruct H0.
    specialize (H0 a HK1). destruct H0 as (b2 & HB2 & HKB2).
    exists b2. split; auto. red. exists a2. split; auto.
 -  destruct H as (a2 & HA2 & HM2).
    specialize (H2 a2 HA2).
    destruct H2 as (a1 & HA1 & HK1).
    specialize (H0 a1 a2).
    assert (mayRet PropM ma1 @ a1).
    Transparent mayRet. 
    { cbn.  intros. destruct EQ as (HX &  HY). specialize (HX a1 HK1).
      destruct HX as (b1 & HR & _). PER_reflexivityH; apply PH. }
    assert (mayRet PropM ma2 @ a2).
    { cbn.  intros. destruct EQ as (HX &  HY). specialize (HX a2 HA2).
      destruct HX as (b2 & HR & _). PER_reflexivityH; apply PH. }
    specialize (H0 H H2 HA1).
    destruct H0.
    specialize (H3 b HM2). destruct H3 as (b2 & HB2 & HKB2).
    exists b2. split; auto. red. exists a1. split; auto.
Qed.    


Lemma eqmR_bind_ProperH_PropM' :
  forall {A1 A2 B1 B2 : typ}
    (RA : relationH A1 A2)
    (RB : relationH B1 B2)
    ma1 ma2
    (kb1 : A1 -=-> PropM B1) (kb2 : A2 -=-> PropM B2),
    eqmR RA @ (ma1, ma2) ->
    (forall (a1 : A1), mayRet PropM ma1 @ a1 -> forall a2, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2))
    ->
    (forall (a2 : A2), mayRet PropM ma2 @ a2 -> forall a1, RA @ (a1, a2) -> eqmR RB @ (kb1 @ a1, kb2 @ a2))
    ->
    eqmR RB @ (bind kb1 @ ma1, bind kb2 @ ma2).
Proof.
  intros.
  repeat red.
  destruct H as (HX & HY).
  Opaque mayRet.
  split; intros; cbn in *.
  - destruct H as (a1 & HA1 & HK1).
    assert (mayRet PropM ma1 @ a1).
    { rewrite <- mayRet_PropM. apply HA1. }
    apply HX in HA1.
    destruct HA1 as (a2 & R & MA).
    specialize (H0 a1 H a2 R).
    destruct H0 as (HA & HB).
    apply HA in HK1.
    destruct HK1 as (b2 & HRB & HKB).
    exists b2. split.  auto. red. exists a2. split; auto.
 -  destruct H as (a2 & HA2 & HK2).
    assert (mayRet PropM ma2 @ a2).
    { rewrite <- mayRet_PropM. apply HA2. }
    apply HY in HA2.
    destruct HA2 as (a1 & R & MA).
    specialize (H1 a2 H a1 R).
    destruct H1 as (HA & HB).
    apply HB in HK2.
    destruct HK2 as (b1 & HRB & HKB).
    exists b1. split.  auto. red. exists a1. split; auto.
Qed.

Lemma eqmR_bind_inv_PropM :
  forall {A : typ} {B : typ}
    (RB : relationH B B) (SH: SymmetricH RB) (TH: TransitiveH RB)
    (ma : PropM A) 
    (k : A -=-> PropM B),
    eqmR RB @ (bind k @ ma, bind k @ ma) ->
      eqmR (image PropM ma) @ (ma, ma) /\
      (forall a, mayRet PropM ma @ a -> eqmR RB @ (k @ a, k @ a)).
Proof.
  intros.
  destruct H as (HX & HY).
  split; intros; split; intros.
  - exists a. split. cbn. intros R HRB (HL & HR).
    specialize (HL a H). destruct HL as (b & Rb & Mb).
    PER_reflexivityH; apply HRB. cbn. apply H.
  - exists b. split. cbn. intros R HRB (HL & HR).
    specialize (HR b H). destruct HR as (a & Ra & Ma).
    PER_reflexivityH; apply HRB. cbn. apply H.
  - cbn.
    assert ((bind k @ ma) @ a0).
    { repeat red. exists a. split.
      apply mayRet_PropM in H. apply H. apply H0.  }
    apply HX in H1. destruct H1 as (b & HB & HK2).
    exists a0. split. 
    + PER_reflexivityH.
    + cbn. apply H0.
  - cbn.
    assert ((bind k @ ma) @ b).
    { repeat red. exists a. split.
      apply mayRet_PropM in H. apply H. apply H0.  }
    apply HY in H1. destruct H1 as (a0 & HA & HK2).
    exists b. split. 
    + PER_reflexivityH.
    + apply H0.
Qed.    

Program Definition PropM_INV {A:typ} (ma : PropM A) : relationH A A :=
  (-=->! (fun p => (ma @ (fst p) /\ ma @ (snd p))) _).
Next Obligation.
  repeat red.
  intros (x1 & x2) (y1 & y2) (HX & HY); split; intros (HZ & HW); split; cbn in *.
  - rewrite <- HX. assumption.
  - rewrite <- HY. assumption.
  - rewrite HX. assumption.
  - rewrite HY. assumption.
Qed.

Lemma SymmetricH_PropM_INV {A:typ} (ma : PropM A) : SymmetricH (PropM_INV ma).
Proof.
  repeat red.
  intros (x & y) (Q1 & Q2); split; cbn in *; auto.
Qed.

Lemma TransitiveH_PropM_INV {A:typ} (ma : PropM A) : TransitiveH (PropM_INV ma).
Proof.
  repeat red.
  intros (x & y1) (y2 & z) (Q1 & Q2) (Q3 & Q4); split; cbn in *.
  - assumption.
  - assumption.
Qed.    

Lemma PropM_INV_refl {A:typ} (ma : PropM A) : eqmR (PropM_INV ma) @ (ma, ma).
Proof.
  repeat red; split; intros; cbn in *.
  exists a; tauto.
  exists b; tauto.
Qed.  

Lemma image_PropM : forall (A:typ) (ma : PropM A) (a1 a2 : A), image PropM ma @ (a1, a2) -> ma @ a1 /\ ma @ a2.
Proof.
  intros.
  assert (PER (PropM_INV ma)). { constructor. apply (SymmetricH_PropM_INV ma). apply (TransitiveH_PropM_INV ma). }

  specialize (H (PropM_INV ma) H0 (PropM_INV_refl ma)).
  apply H.
Qed.  
  

  


Lemma eqmR_ret_PropM : forall {A1 A2 : typ} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        RA @ (a1, a2) -> eqmR RA @ (ret @ a1, (ret @ a2 : PropM A2)).
Proof.
  intros A1 A2 RA a1 a2 H.
  red. cbn.
  split; intros. unfold ret_ in H0. exists a2. rewrite <- H0. split; auto. reflexivity.
  unfold ret_ in H0. exists a1. rewrite <- H0. split; auto. reflexivity.
Qed.

(* TODO: FIX *)
(*
Program Instance eqmR_Monad_PropM : EqmRMonad PropM :=
  {
  image_eqmR := @image_eqmR_PropM;
  mayRet_bind := @mayRet_bind_PropM;
  eqmR_mayRet_l := @eqmR_mayRet_l_PropM;
  eqmR_mayRet_r := @eqmR_mayRet_r_PropM;
  eqmR_ret := @eqmR_ret_PropM;
  eqmR_bind_ProperH := @eqmR_bind_ProperH_PropM';
  }.
Next Obligation.
  repeat red. cbn.
  unfold bind_. cbn. unfold ret_. cbn.
  intros b1 b2 HB.
  split.
  - intros (a2 & HA & HK). rewrite HA. rewrite <- HB. assumption.
  - intros. exists a. split. reflexivity. destruct f. cbn in *.
    assert (a == a) by reflexivity.
    specialize (p _ _ H0 _ _ HB). rewrite p. assumption.
Qed.
Next Obligation.
  repeat red. unfold bind_. cbn.
  intros a1 a2 HA.
  split. 
  - unfold ret_. intros (a & HH & HR). rewrite <- HA. rewrite <- HR. assumption.
  - intros H. exists a2. split; auto. red. symmetry. assumption.
Qed.
Next Obligation.
  repeat red.
  unfold bind_. cbn.
  intros c1 c2 EQC.
  split.
  - intros (b & (a & HA & F) & G).
    exists a. split; auto. red. exists b. split; auto.  rewrite <- EQC. assumption.
  - unfold bind_. intros (a & HA & (b & F & G)).
    exists b. split. exists a. tauto. destruct g. cbn in *.
    assert (b == b) by reflexivity. specialize (p _ _ H _ _ EQC).  rewrite p. assumption.
Qed.    
*)
    

Global Instance EqmRMonadInverses_PropM : EqmRMonadInverses PropM :=
  {
  eqmR_ret_inv := @eqmR_ret_inv_PropM;
  eqmR_bind_refl_inv := @eqmR_bind_inv_PropM;
  }.


(* 

   P(a, b) ==  eqmR RB (k1 @ a) (k2 @ b)

   {x, y, z} >>= k1 = {1, 2, 3}       [k1 x = 1, k1 y = 2, k1 z = 2]
 
   {b, c} >>= k2 = {1, 2, 3}       [k2 b = 1, k2 c = {2, 3}]

   x ~ b    y ~ c    z ~ c
   

   a1 ~ a2 iff   forall b1, k1 @ a1 @ b1 -> exists b2, RB @ (b1, b2) /\ k2 @ a2 @ b2
             /\  forall b2, k2 @ a2 @ b2 -> exists b1, RB @ (b1, b2) /\ k1 @ a1 @ b1



   (exists b, mayRet (bind k1 @ ma1) @ b) \/ ~(exists b, mayRet (bind k1 @ ma1 @ b))


*)

(*  SAZ: The following inversion lemma is false for PropM.

    Consider:  ma1 = {1},  ka1 = fun x => {}
               ma2 = {},   ka2 = anything

    Then it is definitely _not_ the case that eqmR RA ma1 ma2 for any RA.  It is also
    not the case that [eqmR RB (ka1 @ a1) (ka2 @ a2)]
*)

Lemma  eqmR_bind_inv_PropM_FALSE :
  forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
    (ma1 : PropM A1) (ma2 : PropM A2)
    (k1 : A1 -=-> PropM B1)
    (k2 : A2 -=-> PropM B2),
    eqmR RB @ (bind k1 @ ma1, bind k2 @ ma2) ->
    exists (RA : relationH A1 A2),
      eqmR RA @ (ma1, ma2) /\
      (forall a1, mayRet PropM ma1 @ a1 -> exists (a2:A2), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
      /\
      (forall a2, mayRet PropM ma2 @ a2 -> exists (a1:A1), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2)).
Proof.
  intros A1 A2 B1 B2 RB ma1 ma2 k1 k2 (HX & HY).
Abort.  


(* SAZ: These can be proved generically, I think, for any EqmRMonadInverses *)
Lemma eqmr_not_mayRet_l : forall {A1 A2 : typ}
                      (ma1 : PropM A1) (ma2 : PropM A2)
                      (RA : relationH A1 A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
        (~ exists a1, mayRet PropM ma1 @ a1) -> ~exists a2, mayRet PropM ma2 @ a2.
Proof.
  intros.
  intro N.
  apply H.
  destruct N as (a2 & HA).
  destruct EQ as (HX & HY).
  rewrite <- mayRet_PropM in HA.
  specialize (HY _ HA).
  destruct HY as (a1 & _ & HA1).
  exists a1. rewrite <- mayRet_PropM. assumption.
Qed.  

Lemma eqmr_not_mayRet_r : forall {A1 A2 : typ}
                      (ma1 : PropM A1) (ma2 : PropM A2)
                      (RA : relationH A1 A2)
                      (EQ : eqmR RA @ (ma1, ma2)),
        (~ exists a2, mayRet PropM ma2 @ a2) -> ~exists a1, mayRet PropM ma1 @ a1.
Proof.
  intros.
  intro N.
  apply H.
  destruct N as (a1 & HA).
  destruct EQ as (HX & HY).
  rewrite <- mayRet_PropM in HA.
  specialize (HX _ HA).
  destruct HX as (a2 & _ & HA2).
  exists a2. rewrite <- mayRet_PropM. assumption.
Qed.  

(*
Lemma  eqmR_bind_inv_PropM_part :
  forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
    (ma1 : PropM A1) (ma2 : PropM A2)
    (k1 : A1 -=-> PropM B1)
    (k2 : A2 -=-> PropM B2),
    eqmR RB @ (bind k1 @ ma1, bind k2 @ ma2) ->
    (forall (a1:A1), mayRet PropM ma1 @ a1 -> exists (a2:A2), eqmR RB @ (k1 @ a1, k2 @ a2)) ->
    (forall (a2:A2), mayRet PropM ma2 @ a2 -> exists (a1:A1), eqmR RB @ (k1 @ a1, k2 @ a2)) ->
      eqmR (PropM_INV RB k1 k2)  @ (ma1, ma2) .
Proof.
Abort.
*)
(*
  intros.
  repeat red.
  split; cbn; intros.
  destruct H as (HX & HY). cbn in HX, HY.
  rewrite mayRet_PropM in H2.
  apply H0 in H2.
  destruct H2 as (a2 & HA).
  exists a2. split; auto. 
  cbn in HX. cbn in HY.
*)

(*
Lemma  eqmR_bind_inv_PropM_part :
  forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
    (ma1 : PropM A1) (m : PropM B2)
    (k1 : A1 -=-> PropM B1),
    eqmR RB @ (bind k1 @ ma1, m) ->
    exists (RA : relationH A1 A2), exists (ma2 : PropM A2), exists (k2 : A2 -=-> PropM B2),
      m == (bind k2 @ ma2) /\
      eqmR RA @ (ma1, ma2) /\
      (forall a1, mayRet PropM ma1 @ a1 -> exists (a2:A2), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
      /\
      (forall a2, mayRet PropM ma2 @ a2 -> exists (a1:A1), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2)).
Proof.
  intros A1 A2 B1 B2 RB ma1 m k1 (HX & HY).

  assert ((exists b1, mayRet PropM (bind k1 @ ma1) @ b1) \/ ~(exists b1, mayRet PropM (bind k1 @ ma1) @ b1)).
  { admit. (* TODO: Classical logic *) }  
  assert ((exists a1, mayRet PropM ma1 @ a1) \/ ~(exists a1, mayRet PropM ma1 @ a1)).
  { admit. (* TODO: Classical logic *) }
  destruct H as [(b1 & HB1) | NB]; destruct H0 as [(a1 & HA) | NA].
  - rewrite <- mayRet_PropM in HB1. rewrite <- mayRet_PropM in HA.
    specialize (HX b1 HB1).
    destruct HX as (b2 & RB2 & HB2).
    cbn in HB2.
    
    epose ((-=->! (fun p => (fst p == a1 -> snd p == a2)) _) : relationH A1 A2) as Q.
  
  
  (* Unshelve. 2 : {repeat red. intros. split; intros. rewrite H in H0. assumption. rewrite <- H in H0. assumption. } *)
  exists (PropM_INV RB k1 k2).
  split; [|split].
  - repeat red. split.
    intros. 
  
Abort.  
*)

(*  The PropM Monad doesn't have this inversion principle because of nondeterminism: 


  eqmR == ({3, 4} >>= k1) ({3, 4} >>=> k2)
           {5, 0}      ==    {0, 5}
         

  consider:   ma : PropM nat := fun (n:nat) => n = 3 \/ n = 4

              k1 : nat -> PropM nat := 
                 3 -> 5
                 4 -> 0

              k2 : nat -> PropM nat :=
                 3 -> 0
                 4 -> 5
*)

Definition nat_typ := Typ (@eq nat).

Ltac crunch :=
  repeat match goal with
         | [ H : exists X, _ |- _ ] => destruct H
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ |- _ /\ _ ] => split
         end.


Program Definition ambiguous : PropM nat_typ :=
  (-=->! (fun (n:nat) => n = 3 \/ n = 4) _).
Next Obligation.
  repeat red. intros. split; intros. subst; tauto. subst; tauto.
Qed.

Program Definition k1 : nat_typ -=-> PropM nat_typ :=
  (-=->! (fun (n:nat) => (-=->! (fun m => n = 3 /\ m = 5 \/ n = 4 /\ m = 0) _)) _).
Next Obligation.
  repeat red. intros. split; intros. subst; tauto. subst; tauto.
Qed.
Next Obligation.
  repeat red; intros; split; intros; cbn in *; subst; try tauto.
Qed.  

Program Definition k2 : nat_typ -=-> PropM nat_typ :=
  (-=->! (fun (n:nat) => (-=->! (fun m => (n = 3 /\ m = 0) \/ (n = 4 /\ m = 5)) _)) _).
Next Obligation.
  repeat red. intros. split; intros. subst; tauto. subst; tauto.
Qed.
Next Obligation.
  repeat red; intros; split; intros; cbn in *; subst; try tauto.
Qed.  

Program Definition eq_typ (A:typ) : relationH A A :=
  fun p => (fst p) == (snd p).
Next Obligation.
  repeat red.
  intros (x1 & x2) (y1 & y2); intros (EQA & EQB); split; intros X; cbn in *.
  - rewrite <- EQA, <- EQB. assumption.
  - rewrite EQA, EQB. assumption.
Qed.



Lemma binds_equal : (@eqmR PropM _ _ _ (eq_typ nat_typ)) @ (bind k1 @ ambiguous, bind k2 @ ambiguous).
Proof.
  repeat red; split; intros; cbn in *.
  - unfold bind_, ambiguous in *.  cbn in *.
    crunch; subst. 
    + exists 5. split; auto. exists 4. tauto.
    + exists 5. split; auto. exists 4. tauto.
    + exists 0. split; auto. exists 3. tauto.
    + exists 0. split; auto. exists 3. tauto.
  - unfold bind_, ambiguous in *.  cbn in *.
    crunch; subst. 
    + exists 0. split; auto. exists 4. tauto.
    + exists 0. split; auto. exists 4. tauto.
    + exists 5. split; auto. exists 3. tauto.
    + exists 5. split; auto. exists 3. tauto.
Qed.

Transparent mayRet.
Lemma ambiguous_mayRet3 : mayRet PropM ambiguous @ 3.
Proof.
  repeat red.
  intros. red in EQ. cbn in EQ.
  destruct R. cbn in *.
  crunch.
  specialize (H 3).
  assert (3 = 3 \/ 3 = 4). { left; auto. } apply H in H1. 
  crunch.
  subst. auto. subst.
  specialize (H0 3).
  assert (3 = 3 \/ 3 = 4). { left; auto. } apply H0 in H2.
  crunch.
  subst. auto.
  subst. destruct PH. unfold TransitiveH in per_trans.
  specialize (per_trans _ _ H1 H2). cbn in per_trans. apply per_trans. reflexivity.
Qed.  

Lemma ambiguous_mayRet :
      ~(forall (a : nat_typ), mayRet PropM ambiguous @ a -> eqmR (eq_typ nat_typ) @ (k1 @ a, k2 @ a)).
Proof.
  intro H.
  specialize (H 3). specialize (H ambiguous_mayRet3).
  repeat red in H.
  destruct H.
  cbn in *.
  specialize (H 5). crunch.
  assert (3 = 3 /\ 5 = 5 \/ 3 = 4 /\ 5 = 0).
  left; tauto.
  apply H in H1. crunch.
  subst. inversion H3.
  subst. inversion H2.
Qed.  

(* PropM doesn't satisfy this inversion principle -- see the counter example above *)
Lemma eqmR_bind_inv_PropM_FALSE2
  : forall {A : typ} {B1 B2 : typ} (RB : relationH B1 B2)
      (ma : PropM A)
      (k1 : A -=-> PropM B1)
      (k2 : A -=-> PropM B2),
    eqmR RB @ (bind k1 @ ma, bind k2 @ ma) -> 
    forall (a1 : A), mayRet PropM ma @ a1 ->
               exists (a2: A), (mayRet PropM ma @ a2) /\
                          eqmR RB @ (k1 @ a1, k2 @ a2). 
Proof.
Abort.

End PropM.

Section PropT.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {EqmRInverses : EqmRMonadInverses m}.
  
  Definition PropT (X:typ) : typ := (m X) ~~> prop_typ.

  Program Definition lift {A:typ} (ma : m A) : PropT A :=
    fun mb : m A => mb == ma.
  Next Obligation.
    do 2 red.
    intros. rewrite H. reflexivity.
  Qed.
  
  Definition retT_ (A:typ) (x:A) := 
    fun (ma : m A) => ma == (ret @ x).

  Program Definition ret_PropT (A:typ) : A -=-> (PropT A) :=
    -=->! (retT_ A) _.
  Next Obligation.
    unfold retT_.
    do 2 red.
    intros ma1 ma2; split; intros.
    - rewrite <- H. assumption.
    - rewrite H. assumption.
  Qed.
  Next Obligation.
    do 2 red.
    intros. cbn.
    unfold retT_.
    split; intros. cbn in *.
    rewrite <- H0. rewrite <- H. assumption.
    cbn in *.
    rewrite H0. rewrite H. assumption.
  Qed.  

    
  
  Definition bindT_ (A B : typ) (K : A -=-> PropT B) (PA : PropT A) :=
    (fun mb:m B =>
       exists (k : (A -=-> m B)), exists ma : m A,
         PA @ ma
         /\ mb == (bind k @ ma)
         /\ forall (p:A × A), image m ma @ p -> (K @ (fst_typ p)) @ (k @ snd_typ p)).
  
Program Definition bind_PropT (A B : typ) (K : A -=-> PropT B) : (PropT A) -=-> (PropT B) :=
  -=->! (bindT_ A B K) _.
Next Obligation.
  unfold bindT_.
  do 2 red.
  intros mb1 mb2 HB. 
  split; intros (k & ma & HMA & HK & HI); exists k; exists ma; repeat split; auto.
  - rewrite <- HB. assumption. 
  - rewrite  HB. assumption. 
Qed.
Next Obligation.
  do 2 red.
  unfold bind_.
  intros PMA1 PMA2 HP mb1 mb2 HMB; cbn.
  split; intros (k & ma & HMA & HK & HI); exists k; exists ma; repeat split; try auto.
  - rewrite <- HP. assumption.
  - rewrite <- HMB. assumption.
  - rewrite HP. assumption.
  - rewrite HMB. assumption.
Qed.


Instance MonadPropT : Monad typ_proper PropT.
split.
- exact ret_PropT.
- exact bind_PropT.
Defined.  

Require Import Coq.Logic.ChoiceFacts.

(* SAZ: is this the rigth way to do this ? *)
(* NOTE: we would choose to sue this statement from the library: 
Axiom guarded_choice : GuardedFunctionalChoice.
*)
(* But we additionally need some properness information: *)
Definition GuardedFunctionalChoice_typ :=
  forall (A B:typ), forall P : A -> Prop, forall R : A -> B -> Prop, 
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A -=-> B, forall x, P x -> R x (f @ x)).
Axiom guarded_choice : GuardedFunctionalChoice_typ.




Instance MonadLaws_PropT : MonadLaws MonadPropT.
constructor.
  - intros A B K.
    do 2 red.
    intros a1 a2 HA.
    cbn.
    intros mb1 mb2 HMB; cbn in *.
    split.
    + intros (k & ma & HMA & HK & HI).
      red in HMA. unfold retT_ in HMA.
      cbn in *.
      specialize (HI (a1, a1)).
      assert (image m ma @ (a1, a1)).
      { rewrite HMA.
        apply ret_image; auto.
        cbn. split; reflexivity. }
      apply HI in H. rewrite <- HMB. 
      assert (mb1 == k @ a1).
      { etransitivity. apply HK. rewrite HMA.
        apply eqmR_bind_ret_l. }
      rewrite H0.
      rewrite <- HA. apply H.
    + intros.
      red.  eexists (-=->! (fun (y:A) => mb2) _). exists (ret @ a1).
      Unshelve.
      2 : { do 2 red. intros; reflexivity. }

      split.
      * cbn. red. reflexivity.
      * cbn.
        split.
        ** rewrite eqmR_bind_ret_l. cbn. assumption.
        ** intros.
        destruct p as (a & c).
        assert (a == a2).
        { assert (PER (singletonR a1)) as PP. { constructor. apply (singletonR_SymmetricH a1).
                                                apply (singletonR_TransitiveH a1). }

          specialize (H0 (singletonR a1) PP).
          assert (eqmR (singletonR a1) @ (ret @ a1, ret @ a1)).
          { apply (eqmR_ret m). cbn.  split; reflexivity. }
          apply H0 in H1.
          cbn in H1. destruct H1. rewrite H2. assumption.
        }
        destruct K. cbn in *.
        specialize (p _ _ H1).
        red in p.
        assert (mb2 == mb2) by reflexivity.
        specialize (p _ _ H2).
        rewrite p. assumption.

  - intros A.
    do 2 red.
    intros PA1 PA2 HPA.
    do 4 red.
    intros ma1 ma2 HMA.
    do 2 red.
    split.
    + intros (k & ma & HMB & HK & HI).
      cbn.
      rewrite <- HPA.
      assert (ma1 == ma).
      { etransitivity. apply HK.
        repeat red in HI.

      specialize (image_ret_bind m ma k). intros. cbn in HI. 
      rewrite bind_ret_r in H. cbn in H.
      assert (ma1 == ma).
      { etransitivity. apply HK. apply H. intros.
        specialize (HI (a2, a1)). cbn in HI.
        apply HI. intros. apply SymmetricH_Symmetric; auto. apply PH. apply H0; auto. }
      rewrite <- HK. assumption. }
      rewrite <- HMA. rewrite H. assumption.
    + intros. red in H. cbn in H.
      repeat red. exists ret. exists ma2.
      split; [|split].
      rewrite HPA. assumption.
      rewrite bind_ret_r. cbn. assumption.
      intros. red. cbn. red. apply eqmR_equal. apply eqmR_ret. assumption.
      cbn in H0. specialize (H0 (A)).
      assert (PER A) by apply relationH_PER. apply H0 in H1.
      destruct p as (a1 & a2). cbn.
      symmetry.
      apply H0; auto.
      apply relationH_PER.
      apply eqmR_equal. change (ma2 == ma2). reflexivity.
      apply eqmR_equal. change (ma2 == ma2). reflexivity.
      
  - intros A B C KA KB.
    do 2 red.
    intros PA1 PA2 HPA.
    do 4 red.
    intros ma1 ma2 HMA.
    cbn.
    split. 
    + intros (kb & mb & HA & HKB & HIB); cbn in *. 
      destruct HA as (ka & ma & HA & HKA & HIA). 
      eexists (-=->! (fun a => bind kb @ (ka @ a)) _). exists ma.
      split; [| split].
      * rewrite <- HPA. assumption.
      * rewrite <- HMA. rewrite HKB. rewrite HKA.
        eapply eqmR_bind_bind. assumption.
      * intros. destruct p as (a1 & a2).
        red. cbn.   exists kb. exists (ka @ a2).
        split; [|split].
        ** cbn. cbn in HIA. apply (HIA (a1, a2)). assumption.
        ** cbn. reflexivity.
        ** intros. apply HIB.
           destruct p as (b1 & b2).
           change (image m mb @ (b1, b2)).
           rewrite HKA. eapply image_bind; eauto.
          
    + intros (ka & ma & HA & HKA & HI). 
      red in HI. red in HI.
      
      destruct HI as (kab & HKAB).
      red.
      epose ((-=->! (fun a => kab @ (a, a)) _) : A -=-> m B) as k.
      
      exists (bind k @ ma).
      
      ** exists ma. exists kab. split; [|split].
         --- rewrite HPA. assumption.
         --- reflexivity.
         --- intros. apply HKAB in H. destruct H as (_ & HX & _).
             assumption.
               
      ** rewrite HMA. rewrite HKA.
             
      
      assert ((exists a, mayRet m ma @ a) \/ ~(exists a, mayRet m ma @ a)).
      { admit. (* TODO CLASSICAL LOGIC *) }
      destruct H as [(a & HR) | N].
       * specialize (K a HR).
         destruct K as (kb & HKB1 & HEQ & HM2).
         exists kb.
         split; [|split].

         2 : { rewrite HMA. rewrite HKA.
               specialize (eqmR_bind_bind). intros.
               
         
         ** exists ma. epose ((-=->! (fun _ => (k a)) _) : A -=-> m B) as kab.
            exists kab.
            split; [|split].
            *** rewrite HPA. assumption.
            *** 
      


      
      

End PropT.






Program Definition eqmR_PropM {A B : typ} (R : relationH A B) : relationH (PropM A) (PropM B) := 
  fun (P : PropM A × PropM B) =>
    let PA := fst P in
    let PB := snd P in
    (forall (a:A) (b:B), PA @ a -> R @ (a, b) -> PB @ b) 
    /\
    (forall (a:A) (b:B), PA @ a -> R @ (a, b) -> PB @ b)     
    /\ 
    (forall (a:A),
        ~ (PA @ a) -> forall (b:B), R @ (a, b) -> ~(PB @ b))
    /\
    (forall (b:B),
        ~ (PB @ b) -> forall (a:A), R @ (a, b) -> ~(PA @ a)).
(*      
      ((fst P @ a) -> (forall (b2:B), R @ (a, b2) -> (snd P @ b2))) /\
      ((snd P @ b) -> (forall (a2:A), R @ (a2, b) -> (fst P @ a2))).
*)
Next Obligation.
(*
  do 2 red.
  intros (x1 & x2) (y1 & y2) (HA & HB); split;
    intros H; intros p; destruct p as (a & b); cbn in *; intros (HX & HY).
  - specialize (H (a, b)).
    cbn in *.
    apply H.
    split.
    + assert (a == a) by reflexivity. apply HA in H0. tauto.
    + assert (b == b) by reflexivity. apply HB in H0. tauto.
 -  specialize (H (a, b)).
    cbn in *.
    apply H.
    split.
    + assert (a == a) by reflexivity. apply HA in H0. tauto.
    + assert (b == b) by reflexivity. apply HB in H0. tauto.
Qed.
 *)
Admitted.

Program Instance EqmR_PropM : EqmR PropM :=
  {
  eqmR := @eqmR_PropM;
  }.
Next Obligation.
  split.
  - red. intros PA PB (HEQ & HPA & HPB).
    cbn in *.
    intros a1 a2 HA.
    split; intros HX.
    + assert ((PB @ a2) \/ ~(PB @ a2)) as [HY | HY].
      { admit. (* CLASSICAL *) }
      * assumption.
      * specialize (HPB a2 HY a1 HA). contradiction.
    + assert ((PA @ a1) \/ ~(PA @ a1)) as [HY | HY].
      { admit. (* CLASSICAL *) }
      * assumption.
      * specialize (HPA a1 HY a2 HA). contradiction.
  - red. intros PA PB H.
    cbn in *.
    split.
    + intros a H0 b H1. apply H in H1.  intro. apply H0. apply H1. assumption. 
    + intros a H0 b H1. apply H in H1.  intro. apply H0. apply H1. assumption.     
Admitted.
(*
  split.
  - red. intros. cbn in *.
    intros.
    specialize (H (a1, a2)).
    apply H.
    tauto.
  - red. intros. cbn in *.
    intros (a1 & a2).
    cbn. intros.  apply H.
    assumption.
Qed.
 *)

Instance EqmR_OK_PropM : EqmR_OK PropM.
split; try tauto.
Admitted.


Instance EqmRMonad_PropM : EqmRMonad PropM.
split; intros.
- do 2 red. cbn.
  split; intros. intro. apply H0. red. red in H2. 

    
  intros (a11 & a21). cbn. intros (HA1 & HA2).
  red in HA1. red in HA2.
  eapply rewrite_app_l. apply HA1.
  eapply rewrite_app_r. apply HA2.
  assumption.

- cbn. intros (b1 & b2). cbn.
  intros ((a1 & HM1 & K1) & (a2 & HM2 & K2)). cbn in *.
  specialize (H (a1, a2)). cbn in *.
  assert (RA @ (a1, a2)).
  { apply H. tauto. }
  specialize (H0 _ _ H1).
  specialize (H0 (b1, b2)).
  cbn in *. apply H0. tauto.

- repeat red.
  intros a1 a2 H.
  split.
  + intros (b & HM & K). cbn in *. red in HM.
    destruct f. cbn in *.
    symmetry in HM.
    specialize (p _ _ HM).
    cbn in p.
    specialize (p _ _ H). 
    apply p. assumption.
  + destruct f. intros HX.
    repeat (red; cbn).
    exists a. split.  red. reflexivity. eapply p in H. apply H. apply HX. reflexivity.

- red. cbn.
  intros a1 a2 HEQ.
  split.
  + intros (a & HM & K).
    destruct ma. cbn in *. rewrite <- HEQ. red in K. rewrite <- K. assumption.
  + intros.
    red. cbn.
    exists a1. split.  destruct ma. cbn in *. rewrite HEQ. assumption. red. reflexivity.

- cbn.
  intros c1 c2 HC.
  split; red.
  + intros (b & HB & KB). cbn in *.
    red in HB.
    destruct HB as (a & HA & KA).
    exists a. split. assumption. exists b. split.  assumption. rewrite <- HC. assumption.
  + cbn.
    intros (a & HA & KA).
    cbn in *.
    destruct KA as (b & HB & KB).
    exists b. split.  exists a.  tauto. cbn.
    destruct g. cbn.
    assert (b == b) by reflexivity.
    cbn in KB.
    specialize (p _ _ H).
    cbn in p.
    specialize (p c1 c2 HC).
    apply p. assumption.
Qed.    
