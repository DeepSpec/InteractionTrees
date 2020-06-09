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

Program Instance eqmR_OK_PropM : EqmR_OK PropM.
Next Obligation.
  repeat red.
  intros PA1 PA2 (HX & HY).
  split; intros; cbn in *.
  - apply HY in H0. destruct H0 as (a2 & HR & HA2).
    exists a2. split. apply SymmetricH_Symmetric in H. apply H in HR. apply HR. assumption.
  - apply HX in H0.  destruct H0 as (a1 & HR & HA1).
    exists a1. split. apply SymmetricH_Symmetric in H. apply H in HR. apply HR. assumption.
Qed.  
Next Obligation.
  intros PA PB PC (HA1 & HA2) (HB1 & HB2).
  apply TransitiveH_Transitive in H; cbn in *.
  split; intros; cbn in *.
  - apply HA1 in H0. destruct H0 as (b & HR1 & HB).
    apply HB1 in HB. destruct HB as (c & HR2 & HC).
    exists c. split. apply (H (a,b) (b,c)); auto. reflexivity. auto.

  - apply HB2 in H0. destruct H0 as (a & HR1 & HA).
    apply HA2 in HA. destruct HA as (c & HR2 & HC).
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
    PER_reflexivityH.
  - intros HM.
    repeat red in HM.
    epose ((-=->! (fun a => (ma @ a)) _) : A -=-> prop_typ) as Q.
    assert (eqmR (diagonal_prop Q) @ (ma, ma)).
    { repeat red. split; cbn; intros; eauto. }
    specialize (HM (diagonal_prop Q) (diagonal_prop_SymmetricH Q) (diagonal_prop_TransitiveH Q) H).
    destruct H as (HA & HB).
    cbn in *.
    tauto.
    
    
    Unshelve.
    cbn. repeat red. intros. split; intros. rewrite <- H. assumption. rewrite H. assumption. 
    
Qed.  


Lemma eqmR_bind_ProperH_PropM :
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
  

Program Instance eqmR_Monad_PropM : EqmRMonad PropM :=
  {
  eqmR_ret := _;
  eqmR_bind_ProperH := @eqmR_bind_ProperH_PropM;
  }.
Next Obligation.
  unfold ret_; split; intros.
  - exists a2. split; [|reflexivity]. rewrite <- H0. assumption.
  - exists a1. split; [|reflexivity]. rewrite <- H0. assumption.
Qed.
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

Lemma image_eqmR_PropM {A : typ} (ma : PropM A) : eqmR (image PropM ma) @ (ma, ma).
Proof.
  repeat red.
  split.
  - intros a HMA; cbn in HMA.
    exists a. split; auto. do 3 red. intros.
    destruct EQ as (HX & HY).
    specialize (HX a HMA). destruct HX as (b & RB & HB).
    PER_reflexivityH.
  - intros a HMA; cbn in HMA.
    exists a. split; auto. do 3 red. intros.
    destruct EQ as (HX & HY).
    specialize (HX a HMA). destruct HX as (b & RB & HB).
    PER_reflexivityH.
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


Lemma  eqmR_bind_inv_PropM :
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
  intros A1 A2 B1 B2 RB ma1 ma2 k1 k2 H.
  destruct H as (HX & HY).
  cbn in HX, HY.
  unfold bind_ in HX.
Abort.  
  
(*  
        

  Class EqmRMonadInverses :=
    {
    image_eqmR := @image_eqmR_PropM;
    
    eqmR_ret_inv := @eqmr_ret_inv_PropM;


    eqmR_bind_inv : forall {A1 A2 : typ} {B1 B2 : typ} (RB : relationH B1 B2)
                      (ma1 : m A1) (ma2 : m A2)
                      (k1 : A1 -=-> m B1)
                      (k2 : A2 -=-> m B2),
        eqmR RB @ (bind k1 @ ma1, bind k2 @ ma2) ->
        exists (RA : relationH A1 A2),
          eqmR RA @ (ma1, ma2) /\
          (forall a1, mayRet m ma1 @ a1 -> exists (a2:A2), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
          /\
          (forall a2, mayRet m ma2 @ a2 -> exists (a1:A1), RA @ (a1, a2) /\ eqmR RB @ (k1 @ a1, k2 @ a2))
    }.

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
  subst. unfold TransitiveH in TS.
  specialize (TS _ _ H1 H2). cbn in TS. apply TS. reflexivity.
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
Lemma eqmR_bind_inv_PropM
  : forall {A : typ} {B1 B2 : typ} (RB : relationH B1 B2)
      (ma : PropM A)
      (k1 : A -=-> PropM B1)
      (k2 : A -=-> PropM B2),
    eqmR RB @ (bind k1 @ ma, bind k2 @ ma) -> 
    forall (a1 : A), mayRet PropM ma @ a1 ->
               exists (a2: A), (mayRet PropM ma @ a2) /\
                          eqmR RB @ (k1 @ a1, k2 @ a2). 
Proof.
  intros A B1 B2 RB PA k1 k2 (HA & HB) a1 MA1.
  cbn in HA, HB.
  assert ((exists a2 : A, mayRet PropM PA @ a2 /\ eqmR RB @ (k1 @ a1, k2 @ a2))
          \/ ~(exists a2 : A, mayRet PropM PA @ a2 /\ eqmR RB @ (k1 @ a1, k2 @ a2))).
  { admit. (* TODO: classical logic *) }
  destruct H; [assumption|].
  assert (forall (a2:A), ~(mayRet PropM PA @ a2 /\ eqmR RB @ (k1 @ a1, k2 @a2))).
  intros a2.  intros N. apply H. exists a2. apply N.
  
  
  
  assert (diagonal_prop PA @ (a1, a1)).
    { specialize (MA1 (diagonal_prop PA) (diagonal_prop_SymmetricH PA) (diagonal_prop_TransitiveH PA)).
      apply MA1.
      split.
      + intros. exists a. split; auto. cbn. tauto.
      + intros. exists b. split; auto. cbn. tauto.
    }

(*    
    assert (bind_ A B1 k1 PA ).
    { red. exists a. split.  assumption. apply HK1. }
  
  
  split.
  - intros b1 HK1.
    (* SAZ: This is a nice trick to "manufacture" an element out of an image *)
    assert (diagonal_prop PA @ (a, a)).
    { specialize (MA (diagonal_prop PA) (diagonal_prop_SymmetricH PA) (diagonal_prop_TransitiveH PA)).
      apply MA.
      split.
      + intros. exists a0. split; auto. cbn. tauto.
      + intros. exists b. split; auto. cbn. tauto.
    }
    destruct H as (HX & HY). cbn in *.
    assert (bind_ A B1 k1 PA b1).
    { red. exists a. split.  assumption. apply HK1. }
    apply HA in H.
    destruct H as (b2 & HB2 & HK2).
    destruct HK2 as (a1 & Ha2 & HKK).
    exists b2. split. assumption.

Abort.
    
 *)     
(*
Program Instance EqmRMonadInverses_PropM : EqmRMonadInverses PropM.
    destruct EQ. destruct (H1 _ H) as (a & Ha & _). 
    PER_reflexivityH.
Qed.
Next Obligation.
  unfold ret_ in *.
  assert (a1 == a1) by reflexivity.
  specialize (H _ H1). destruct H as (b & HB & EQ).
  rewrite EQ. assumption.
Qed.
Next Obligation.
*)  
(*
Next Obligation.  
eexists (-=->! (fun (b:B) => False) _).
Unshelve. 2 : { repeat red. intros. tauto. }

intros R. split.
- intros. 

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




  Lemma mayret_bind {A B:typ} (ma : m A) (k : A -=-> m B) (b : B) :
    mayRet m (bind k @ ma) @ b -> exists a, mayRet m ma @ a /\ mayRet m (k @ a) @ b.
  Proof.
    pose proof (image_eqmR m (bind k @ ma)).
    
    
    intros HM.
    unfold mayRet in HM. cbn in HM.
    
    
    assert ((exists a, mayRet m ma @ a /\ mayRet m (k @ a) @ b) \/ not(exists a, mayRet m ma @ a /\ mayRet m (k @ a) @ b)).
    { admit. (* TODO: classical logic *) }
    destruct H.
    - assumption.
    - assert (forall (a:A), ~(mayRet m ma @ a /\ (mayRet m (k @ a) @ b))).
      { intros a N. apply H. exists a. assumption. }
      
    
  
  (*
  Lemma image_bind_pred {A B:typ} (ma : m A) (k : A -=-> m B)
        (PA : (m A) -=-> prop_typ) (HPA: PA @ ma)
        (PB : (m B) -=-> prop_typ)
        (HA: forall (a:A), mayRet m ma @ a -> PB @ (k @ a)) :
    PB @ (bind k @ ma).
  *)
*)
  
  (* Add to a typeclass?

     SAZ: This seems like something that should be provable for both
     itree and stateT 
  *)
Abort.
    Lemma image_bind {A B:typ} (ma1 ma2 : m A) (k1 k2 : A -=-> m B)
        (HM : ma1 == ma2)
        (HK : forall (a : A), mayRet m ma1 @ a -> (k1 @ a) == (k2 @ a)) :
    (bind k1) @ ma1 == (bind k2) @ ma2.
  Admitted.


  

  

  Lemma image_ret_bind {A:typ} (ma : m A) (k : A -=-> m A) : 
      (forall (a : A), mayRet m ma @ a -> k @ a == ret @ a) -> bind k @ ma == (bind ret) @ ma.
  Proof. 
    intros H.
    apply image_bind.
    - reflexivity.
    - assumption.
  Qed.
    
  
  Definition bindT_ (A B : typ) (K : A -=-> PropT B) (PA : PropT A) :=
    (fun mb:m B =>
       exists (ma:m A) (k : A -=-> m B),
         PA @ ma
         /\ mb == (bind k @ ma)
         /\ forall (a:A), mayRet m ma @ a -> (K @ a) @ (k @ a)).
                          
  
Program Definition bind_PropT (A B : typ) (K : A -=-> PropT B) : (PropT A) -=-> (PropT B) :=
  -=->! (bindT_ A B K) _.
Next Obligation.
  unfold bindT_.
  do 2 red.
  intros mb1 mb2 HB. 
  split; intros (ma & k & HMA & HK & HI); exists ma; exists k; repeat split; auto.
  - rewrite <- HB. assumption. 
  - rewrite  HB. assumption. 
Qed.
Next Obligation.
  do 2 red.
  unfold bind_.
  intros PMA1 PMA2 HP mb1 mb2 HMB; cbn.
  split; intros (ma & k & HMA & HK & HI); exists ma; exists k; repeat split; try auto.
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

Instance MonadLaws_PropT : MonadLaws MonadPropT.
constructor.
  - intros A B K.
    do 2 red.
    intros a1 a2 HA.
    cbn.
    intros mb1 mb2 HMB; cbn in *.
    split.
    + intros (ma & k & HMA & HK & HI).
      red in HMA. unfold retT_ in HMA.
      cbn in *.
      specialize (HI a1).
      assert (image m ma @ (a1, a1)).
      { rewrite (rewrite_image_app _ _ _ _ HMA).
        apply ret_image; auto.
        cbn. split; reflexivity. }
      apply HI in H. rewrite <- HMB. 
      assert (mb1 == k @ a1).
      { etransitivity. apply HK. rewrite HMA.
        apply eqmR_bind_ret_l. }
      rewrite H0.
      rewrite <- HA. apply H.
    + intros.
      red. exists (ret @ a1).
      eexists (-=->! (fun (y:A) => mb2) _).
      Unshelve.
      2 : { do 2 red. intros; reflexivity. }

      split.
      * cbn. red. reflexivity.
      * cbn.
        split.
        ** rewrite eqmR_bind_ret_l. cbn. assumption.
        ** intros.
        assert (a == a2).
        { specialize (H0 (singletonR a1) (singletonR_SymmetricH a1) (singletonR_TransitiveH a1)).
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
    + intros (ma & k & HMB & HK & HI).
      cbn.
      rewrite <- HPA.
      apply image_ret_bind in HI.
      rewrite bind_ret_r in HI. cbn in HI.
      assert (ma1 == ma).
      etransitivity. apply HK.  apply HI.
      rewrite <- HMA. rewrite H. assumption.
    + intros. red in H. cbn in H.
      repeat red.
      exists ma2. exists ret. split; [|split].
      rewrite HPA. assumption.
      rewrite bind_ret_r. cbn. assumption.
      intros. red. cbn. red. reflexivity.

  - intros A B C KA KB.
    do 2 red.
    intros PA1 PA2 HPA.
    do 4 red.
    intros ma1 ma2 HMA.
    cbn. unfold bindT_. Opaque image. cbn.
    split. 
    + intros (mb & kb & HA & HKB & HIB); cbn in *.
      destruct HA as (ma & ka & HA & HKA & HIA).
      exists ma. eexists (-=->! (fun a => bind kb @ (ka @ a)) _).
      
      split; [| split].
      * rewrite <- HPA. assumption.
      * rewrite <- HMA. rewrite HKB. rewrite HKA.
        eapply eqmR_bind_bind. assumption.
      * intros.
        red. exists mb. exists kb.
        split; [|split].
        ** rewrite HKA.
           exists Q, Q @ ma /\ forall (a:A), mayRet m ma @ a -> P (ka a)

           P @ (bind ka @ ma)
           
           (* SAZ: This fails: apply HIA.  why?  Different Univese levels? *)
           admit.
        ** cbn. rewrite HKA.
           apply eqmR_equal.
           eapply eqmR_bind_ProperH.
           --- assumption.
           --- apply eqmR_equal.
               
               
           --- destruct kb. cbn in *.
               intros. apply eqmR_equal. apply p. assumption.
        ** apply HIB.
    + intros (ma & ka & HA & HKA & HI).
      red in HI.
      eexists. eexists.
      split; [|split].
      exists ma. 
      
      assert ((exists (a:A), image m mb @ (a, a)) \/ ~exists(a:A), image m mb @ (a, a)).
      { admit. (* TODO: Classical logic *) }
      destruct H.
      * destruct H as (a & IM).
        specialize (HIB a IM).
        destruct HIB as (mbb & k & HKA & HK & HI).
        exists mbb. exists k.
        split; [|split].
        ** exists (ret @ a). eexists (-=->! (fun a => mbb) _).
           split;[|split].
           -- 

                                                                 

      cbn. split.


      
      

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
