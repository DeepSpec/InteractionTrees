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

Instance MonadLaws_PropM : MonadLaws MonadPropM.
constructor.
- cbn. intros A B K.
  do 2 red. cbn.
  intros a1 a2 HA.
  split. 
  + intros (b & HR & HX); cbn in *.
    red in HR. destruct K. cbn in *.
    assert (b == a2).
    {  etransitivity. symmetry. apply HR. assumption. }
    specialize (p _ _ H0 _ _ H). rewrite <- p. assumption.
  + destruct K. cbn in *. intros HX.
    exists a1. cbn. split. red. reflexivity.
    symmetry in HA. symmetry in H.
    specialize (p _ _ HA _ _ H). rewrite <- p. assumption.

- intros A.
  cbn.
  do 2 red.
  intros PA1 PA2 HP.
  cbn.
  intros a1 a2 HA.
  split.
  + intros (b & HR & HX); cbn in *.
    red in HX. rewrite <- HP. rewrite <- HA. rewrite <- HX. assumption.
  + intros HX.
    exists a2. split. rewrite HP. assumption. cbn. red. symmetry. assumption.

- intros A B C KA KB.
  do 2 red.
  intros PA1 PA2 HP.
  do 3 red.
  intros c1 c2 HC.
  split.
  + intros (b & (a & HA & HKA) & HKB). cbn in *.
    exists a. split.
    * rewrite <- HP. assumption.
    * cbn. exists b. split. auto. rewrite <- HC. assumption.
  + intros (a & HA & (b & HKA & HKB)). cbn in *.
    exists b. cbn. split. exists a. split.
    * rewrite HP. assumption.
    * assumption.
    * destruct KB. cbn in *. assert (b == b) by reflexivity.
      specialize (p _ _ H _ _ HC). rewrite p. assumption.

- intros A B.
  do 2 red.
  intros KA1 KA2 HEQ.
  do 2 red.
  intros PA1 PA2 HPA.
  cbn.
  intros b1 b2 HB.
  split.
  + intros (a & HA & HKA).
    exists a. split. rewrite <- HPA. assumption. rewrite <- HEQ.
    rewrite <- HB. assumption.
  + intros (a & HA & HKA).
    exists a. split. rewrite HPA. assumption.
    rewrite HEQ. rewrite HB. assumption.
Qed.


Section PropT.
  Context (m : typ -> typ).
  Context {Mm : Monad typ_proper m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonad m} {EqmROKm : EqmR_OK m}.
  Context {EqmRInverses : EqmRMonadInverses m}.
  
  Definition PropT (X:typ) : typ := (m X) ~~> prop_typ.

  Definition retT_ (A:typ) (x:A) := 
    fun (ma:m A) => equalE (m A) ma (ret @ x).

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

  Definition emptyH {A:typ} (R : relationH A A) : Prop :=
    ~exists(a:A), R @ (a, a).

  (* SAZ: This one is probably not needed *)
  Lemma empty_image {A:typ} (ma : m A) : 
    emptyH (image m ma) -> forall (k : A -=-> m A), bind k @ ma == ma.
  Admitted.

  (* Add to typeclass? *)
  Lemma image_ret_bind {A:typ} (ma : m A) (k : A -=-> m A) : 
      (forall (a : A), image m ma @ (a, a) -> k @ a == ret @ a) -> bind k @ ma == ma.
  Admitted.

  (* SAZ: This formulation doesn't seem right:
     The predicate P is over the "whole" computation 
   *)
  Lemma image_bind_P {A B:typ} (ma : m A) (k : A -=-> m B) (P : m B -=-> prop_typ)
        (HI : forall (a:A), image m ma @ (a, a) -> P @ (k @ a)) :
    P @ (bind k @ ma).
  Admitted.
  
  Definition bindT_ (A B : typ) (K : A -=-> PropT B) (PA : PropT A) :=
    (fun mb:m B =>
       exists (ma:m A) (k : A -=-> m B),
         PA @ ma
         /\ mb == (bind k @ ma)
         /\ forall (a:A), (image m ma) @ (a, a) -> (K @ a) @ (k @ a)).
                          
  
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
      assert (ma1 == ma).
      etransitivity. apply HK. apply HI.
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
           apply image_bind_P.  
           (* SAZ: This fails: apply HIA.  why?  Different Univese levels? *)
           admit.
        ** cbn. rewrite HKA.
           apply eqmR_equal.
           eapply eqmR_bind_ProperH.
           --- assumption.
           --- apply eqmR_equal.  admit.
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
