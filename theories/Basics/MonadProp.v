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

Program Instance eqmR_Monad_PropM : EqmRMonad PropM.
Next Obligation.
  unfold ret_; split; intros.
  - exists a2. split; [|reflexivity]. rewrite <- H0. assumption.
  - exists a1. split; [|reflexivity]. rewrite <- H0. assumption.
Qed.
Next Obligation.
  unfold bind_; cbn in *; split; intros b1 (a1 & HA & HKA).
  - destruct (H a1 HA) as (a2 & RA2 & HA2).
    destruct (H0 a1 a2 RA2) as (HX & HY).
    specialize (HX b1 HKA). destruct HX as (b2 & RB2 & HB2).
    specialize (HY b2 HB2). destruct HY as (b & RBb & HKB).
    exists b2; split; auto. exists a2. split; auto.
  - destruct (H1 a1 HA) as (a2 & RA2 & HA2).
    destruct (H0 a2 a1 RA2) as (HX & HY).
    specialize (HY b1 HKA). destruct HY as (b2 & RB2 & HB2).
    specialize (HX b2 HB2). destruct HX as (b & RBb & HKB).
    exists b2; split; auto. exists a2. split; auto.
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

  
  (* Add to a typeclass?

     SAZ: This seems like something that should be provable for both
     itree and stateT 
  *)
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
