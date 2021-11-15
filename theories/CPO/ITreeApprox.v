From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.

Local Open Scope itree_scope.


Section WeakITreeApprox.
  Context {E : Type -> Type}.
  Context {R1 R2: Type}.
  Context (RR : R1 -> R2 -> Prop).


  Inductive weak_itree_approxF (sim : itree E R1 -> itree E R2 -> Prop) vclo : itree' E R1 -> itree' E R2 -> Prop :=
  | weak_itree_approx_Ret r1 r2 : RR r1 r2 -> weak_itree_approxF sim vclo (RetF r1) (RetF r2)
  | weak_itree_approxF_Vis A (e : E A) k1 k2 : (forall a, vclo sim (k1 a) (k2 a) : Prop) ->
                                          weak_itree_approxF sim vclo (VisF e k1) (VisF e k2)
  | weak_itree_approxF_TauLR t1 t2 : vclo sim t1 t2 -> weak_itree_approxF sim vclo (TauF t1) (TauF t2)
  | weak_itree_approxF_TauL t1 t2 : vclo sim t1 t2 -> weak_itree_approxF sim vclo (TauF t1) (observe t2)
  | weak_itree_approxF_TauR ot1 t2 : weak_itree_approxF sim vclo ot1 (observe t2) -> weak_itree_approxF sim vclo ot1 (TauF t2)
  .
  (* Worth keeping in mind a more deterministic definition,
     replace TauL rule with a rule that says that if there is a Tau on left but not on right,
     then the left must be spin, that is a strictly stronger definition that I believe would 
     still be a partial order, and might be easier to prove complete

     might be worth defining that one next before writing the directed supremum function 

   *)
  Hint Constructors weak_itree_approxF.

  Definition weak_itree_approx_ vclo sim t1 t2 :=
    weak_itree_approxF sim vclo (observe t1) (observe t2).

    Lemma weak_itree_approxF_mono x0 x1 vclo vclo' sim sim'
        (IN: weak_itree_approxF sim vclo x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    weak_itree_approxF sim' vclo' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma weak_itree_approx__mono vclo (MON: monotone2 vclo) : monotone2 (weak_itree_approx_ vclo).
  Proof. do 2 red. intros. eapply weak_itree_approxF_mono; eauto. Qed.

  Definition weak_itree_approx : itree E R1 -> itree E R2 -> Prop :=
    paco2 (weak_itree_approx_ id) bot2.


End WeakITreeApprox.

#[global] Hint Constructors weak_itree_approxF: core.
#[global] Hint Unfold weak_itree_approx_: core.
#[global] Hint Resolve weak_itree_approx__mono : paco.
#[global] Hint Unfold weak_itree_approx: core.


Lemma weak_itree_approx_spin_bottom : forall E R1 R2 RR (t : itree E R2),
    weak_itree_approx RR (@ITree.spin E R1) t.
Proof.
  intros. pcofix CIH. pfold. red. cbn.
  constructor. right. eauto.
Qed.

Lemma weak_itree_approx_refl_eq_itree : forall E R (t1 t2 : itree E R),
    t1 ≅ t2 -> weak_itree_approx eq t1 t2.
Proof.
  intros E R. pcofix CIH. pfold. intros.
  punfold H0. red in H0. red. inv H0; pclearbot; eauto; try inv CHECK;
  constructor; right; eauto.
Qed.

Lemma weak_itree_approx_refl : forall E R (t : itree E R),
    weak_itree_approx eq t t.
Proof.
  intros; apply weak_itree_approx_refl_eq_itree. reflexivity.
Qed.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Lemma itree_approx_TauLR : forall E R1 R2 RR (t1: itree E R1) (t2 : itree E R2) ,
    weak_itree_approx RR (Tau t1) (Tau t2) -> weak_itree_approx RR t1 t2.
Proof. (*I feel like this proof could have been more direct *)
  intros E R1 R2 RR. pcofix CIH. intros.
  punfold H0. red in H0.
  cbn in *. remember (TauF t1) as x. remember (TauF t2) as y.
  hinduction H0 before r; intros; try inv Heqx; try inv Heqy; inj_existT; subst; pclearbot; eauto.
  - eapply paco2_mon; eauto. intros; contradiction.
  - punfold H. red in H. rewrite H1 in H. inv H; pclearbot.
    + pfold. red. rewrite <- H0. constructor. left. eapply paco2_mon; eauto.
      intros; contradiction.
    + pfold. red. rewrite <- H0. constructor. right. eapply CIH. pfold. red. rewrite <- H2.
      rewrite <- (itree_eta' (observe t4)). constructor. left. auto.
    + eapply paco2_mon with (r := bot2). 2 : intros; contradiction. pfold. auto.
  - pfold. red. inv H0; pclearbot.
    + constructor. enough (paco2 (weak_itree_approx_ RR id) r t1 t3).
      punfold H. eapply paco2_mon; eauto. intros; contradiction. 
    + enough (paco2 (weak_itree_approx_ RR id) r t1 t3). punfold H.
      eapply paco2_mon; eauto. intros; contradiction.
    + constructor. enough (paco2 (weak_itree_approx_ RR id) r t1 t2). punfold H0.
      eapply IHweak_itree_approxF; eauto.
Qed.

Lemma weak_itree_approx_proper_l : forall E R1 R2 (RR : R1 -> R2 -> Prop) 
                                     (RR' : R1 -> R1 -> Prop) (t1 t1': itree E R1) (t2 : itree E R2),
    (forall (x1 x2 : R1) (y : R2), RR' x1 x2 -> RR x1 y -> RR x2 y ) ->
    eutt RR' t1 t1' -> weak_itree_approx RR t1 t2 -> weak_itree_approx RR t1' t2.
Proof.
  intros E R1 R2 RR RR'. pcofix CIH. intros t1 t1' t2 HRR Ht1 Ht12.
  punfold Ht1. red in Ht1. punfold Ht12. red in Ht12. pfold. red.
  hinduction Ht1 before r; intros.
  - remember (RetF r1) as x. hinduction Ht12 before r; intros; inv Heqx; subst; eauto.
  - pclearbot. constructor. right. eapply CIH; eauto. pfold. red.
    remember (TauF m1) as x. hinduction Ht12 before r; intros; inv Heqx; subst; pclearbot; eauto.
    + constructor. punfold H.
    + punfold H.
  - pclearbot. remember (VisF e k1) as x. 
    hinduction Ht12 before r; intros; inv Heqx; inj_existT; subst; pclearbot; eauto.
    constructor. right. eapply CIH; eauto.
  - eapply IHHt1; eauto. remember (TauF t0) as x.
    hinduction Ht12 before r; intros; inv Heqx; subst; eauto.
    + pclearbot. constructor. punfold H.
    + pclearbot. punfold H.
  - constructor. right. eapply CIH; eauto. Unshelve.
    3 : apply (go ot1). pfold. red. cbn. auto.
    pfold. red. cbn. auto.
Qed.

Lemma weak_itree_approx_proper_r : forall E R1 R2 (RR : R1 -> R2 -> Prop)
                                     (RR' : R2 -> R2 -> Prop) (t1: itree E R1) (t2 t2': itree E R2),
    (forall (x : R1) (y1 y2 : R2), RR' y1 y2 -> RR x y1 -> RR x y2) ->
    eutt RR' t2 t2' -> weak_itree_approx RR t1 t2 -> weak_itree_approx RR t1 t2'.
Proof.
  intros E R1 R2 RR RR'. pcofix CIH. intros t1 t2 t2' HRR Ht2 Ht12.
  punfold Ht2. red in Ht2. punfold Ht12. red in Ht12. pfold. red.
  hinduction Ht2 before r; intros.
  - enough (paco2 (weak_itree_approx_ RR id) r t1 (Ret r2) ). punfold H.
    generalize dependent t1. pcofix CIH. intros.
    pfold. red. inversion Ht12; eauto.
    + constructor. eauto.
    + constructor. right. pclearbot. eapply CIH0; eauto.
      rewrite <- H in Ht12. inv Ht12. punfold H1. red in H1.
      rewrite H3. rewrite H0 in H1. auto.
  - pclearbot.
    assert ( (exists t3, observe t1 = TauF t3) \/ (forall t3, observe t1 <> TauF t3) ).
    { destruct (observe t1). right. repeat intro; discriminate.
      left. eexists. eauto. right. repeat intro; discriminate. }
    destruct H.
    + destruct H as [t3 Ht3]. rewrite Ht3. constructor. right. eapply CIH; eauto.
      apply itree_approx_TauLR. pfold. red.
      cbn. rewrite <- Ht3. auto.
    + remember (TauF m1) as x.
      hinduction Ht12 before r; intros; inv Heqx; subst;
        pclearbot; eauto.
      * constructor. right. eapply CIH; eauto.
      * constructor. right. eapply CIH; eauto. apply itree_approx_TauLR.
        pfold. red. cbn. rewrite <- H2. constructor.
        left. auto.
      * destruct ot1. 
        -- clear IHHt12. constructor. remember (RetF r0) as x.
           punfold REL. red in REL.
           hinduction Ht12 before r; intros; inv Heqx; eauto.
           ++ remember (RetF r2) as x. hinduction REL before r; intros; inv Heqx; eauto.
           ++ eapply IHHt12; eauto.
              enough (eutt RR' t2 m2). punfold H0. rewrite <- tau_eutt. pfold. auto.
       -- exfalso. eapply H; eauto.
       -- clear IHHt12. rewrite itree_eta' at 1. constructor. cbn.
          remember (VisF e k) as x. punfold REL. red in REL.
          hinduction Ht12 before r; intros; inv Heqx; inj_existT; subst; eauto.
          ++ pclearbot. remember (VisF e0 k2) as x.
             hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto.
             constructor. right. pclearbot. eapply CIH; eauto.
          ++ eapply IHHt12; eauto. enough (eutt RR' t2 m2). punfold H0.
             rewrite <- tau_eutt. pfold. auto.
  - remember (VisF e k1) as x. hinduction Ht12 before r; intros; inv Heqx; inj_existT; subst;
                                 pclearbot; eauto.
    + constructor. right. eapply CIH; eauto.
    + rewrite itree_eta'. constructor. right. eapply CIH; eauto. symmetry in H1.
      apply simpobs in H1. rewrite H1.  apply eqit_Vis. auto.
  - eapply IHHt2; eauto.
    remember (TauF t1) as x. hinduction Ht12 before r; intros; inv Heqx; subst; pclearbot; eauto.
    constructor. left. apply itree_approx_TauLR. pfold. red. cbn. rewrite <- H1.
    constructor. left. auto.
  - constructor. eapply IHHt2; eauto.
Qed.

Global Instance weak_itree_approx_eutt_RR_proper1 {E R1 R2 RR1 RR2 RR} : 
  Equivalence RR1 -> Equivalence RR2 ->
  (forall (x1 x2 : R1) (y : R2), (RR1 x1 x2 : Prop) -> (RR x1 y : Prop) -> RR x2 y) ->
  (forall (x : R1) (y1 y2 : R2), (RR2 y1 y2 : Prop) -> (RR x y1 : Prop) -> RR x y2) ->
  Proper (@eutt E R1 R1 RR1 ==> @eutt E R2 R2 RR2 ==> Basics.flip Basics.impl ) (weak_itree_approx RR).
Proof.
  repeat intro. symmetry in H3. eapply weak_itree_approx_proper_l; intros; subst; eauto.
  subst. auto.
  symmetry in H4. eapply weak_itree_approx_proper_r; eauto. 
Qed.


Global Instance weak_itree_approx_eutt_proper1 {E R1 R2 RR} : 
  Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq ==> Basics.flip Basics.impl ) (weak_itree_approx RR).
Proof.
  eapply weak_itree_approx_eutt_RR_proper1; auto.
  all : try (constructor; cbv; intros; subst; auto).
  all : intros; subst; auto.
Qed.

Global Instance weak_itree_approx_eutt_RR_proper2 {E R1 R2 RR1 RR2 RR} : 
  (forall (x1 x2 : R1) (y : R2), (RR1 x1 x2 : Prop) -> (RR x1 y : Prop) -> RR x2 y) ->
  (forall (x : R1) (y1 y2 : R2), (RR2 y1 y2 : Prop) -> (RR x y1 : Prop) -> RR x y2) ->
  Proper (@eutt E R1 R1 RR1 ==> @eutt E R2 R2 RR2 ==> Basics.impl ) (weak_itree_approx RR).
Proof.
  repeat intro. eapply weak_itree_approx_proper_l; intros; subst; eauto.
  subst. auto.
   eapply weak_itree_approx_proper_r; eauto. 
Qed.

Global Instance weak_itree_approx_eutt_proper2 {E R1 R2 RR} : 
  Proper (@eutt E R1 R1 eq ==> @eutt E R2 R2 eq ==> Basics.impl ) (weak_itree_approx RR).
Proof.
  eapply weak_itree_approx_eutt_RR_proper2; auto.
  all : intros; subst; auto.
Qed.

(*could be generalized? *)
Lemma weak_itree_approx_antisym : forall E R (t1 t2 : itree E R),
    weak_itree_approx eq t1 t2 -> weak_itree_approx eq t2 t1 ->
    t1 ≈ t2.
Proof.
  intros E R. pcofix CIH.
  intros t1 t2 H12 H21. pfold. red.
  punfold H12. punfold H21. red in H12. red in H21.
  remember (observe t1) as x. remember (observe t2) as y.
  hinduction H12 before r; intros; try inv Heqx; try inv Heqy; inj_existT; subst; pclearbot; eauto.
  - constructor. right. eapply CIH; eauto. inv H21. inj_existT. subst. pclearbot. auto.
  - clear H1 H2. remember (TauF t1) as x. remember (TauF t2) as y.
    hinduction H21 before r; intros; try inv Heqx; try inv Heqy; inj_existT; subst; pclearbot; eauto.
    + rewrite H2. constructor. right. eapply CIH; eauto.
      symmetry in H2. apply simpobs in H2. setoid_rewrite H2 in H. rewrite tau_eutt in H. auto.
    + inv H21. pclearbot.
      * constructor. right. eapply CIH; eauto.
        apply simpobs in H1. rewrite H1. rewrite tau_eutt. auto.
      * pclearbot. constructor. right. eapply CIH; eauto. pfold. red. rewrite <- H1.
        punfold H2.
      * constructor. right. eapply CIH; eauto.
        rewrite <- (tau_eutt t0). apply simpobs in H0. rewrite H0. rewrite (tau_eutt t2).
        pfold. auto.
  - assert ( (exists t3, observe t2 = TauF t3) \/ (forall t3, observe t2 <> TauF t3) ).
    { destruct (observe t2). right. repeat intro; discriminate. left. eexists. eauto.
      right. repeat intro; discriminate. }
    destruct H0.
    + destruct H0 as [t4 Ht4]. rewrite Ht4. constructor. right. eapply CIH; eauto.
      * symmetry in Ht4. apply simpobs in Ht4. rewrite Ht4 in H. rewrite tau_eutt in H. auto.
      * rewrite <- tau_eutt. rewrite <- (tau_eutt t1).
        pfold. red. cbn. rewrite <- Ht4. auto.
    + remember (TauF t1) as x. clear H2 t3. punfold H. red in H. remember (observe t2) as y. clear H1.  hinduction H21 before r; intros; inv Heqx; subst; pclearbot; try contradiction; eauto.
      * exfalso. eapply H1; eauto.
      * exfalso; eapply H1; eauto.
      * constructor; auto.
        destruct (observe t0); try (exfalso; eapply H0; eauto; fail).
        -- inv H21. constructor; auto. rewrite H1. eapply IHweak_itree_approxF; auto.
           3 : symmetry in H1; eauto. Unshelve. 3 :  exact (Ret r0). auto.
           rewrite <- H1 in H. inv H. pclearbot. punfold H5.
        -- inv H21. inj_existT. subst. constructor. pclearbot. right. eapply CIH; eauto.
           rewrite <- H5 in H. inv H. inj_existT. subst. pclearbot. auto.
           rewrite H1. eapply IHweak_itree_approxF; auto.
           3 : symmetry in H1; eauto. Unshelve. 3 : exact (Vis e k). auto.
           rewrite <- H1 in H. inv H. pclearbot. punfold H5.
  - constructor; auto. eapply IHweak_itree_approxF; auto. 
    enough (weak_itree_approx eq t2 t1). punfold H. rewrite <- tau_eutt. pfold. auto.
Qed.

Lemma eqitC_wcompat_weak_approx : forall E (R1 R2 : Type) (RR : R1 -> R2 -> Prop),
    wcompatible2 (@weak_itree_approx_ E R1 R2 RR id) (eqitC RR true true).
Proof.
  intros. econstructor. pmonauto.
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  red in REL. red. 
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. hinduction EQVl before r; intros; inv Heqx; subst; eauto.
    + remember (RetF r3) as x. hinduction EQVr before r; intros; inv Heqx; subst; eauto.
    + constructor. gstep. red. eauto.
  - remember (VisF e k1) as x. hinduction EQVl before r; intros; inv Heqx; inj_existT; subst; eauto.
    + remember (VisF e0 k3) as x. hinduction EQVr before r; intros; inv Heqx; inj_existT; subst; eauto.
      pclearbot. constructor. gclo. intros. econstructor; eauto. gfinal. left. apply H. 
    + constructor. gstep. red. eauto.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; subst; pclearbot; try inv CHECK; eauto.
    + remember (TauF t2) as x. hinduction EQVr before r; intros; inv Heqx; subst; pclearbot; try inv CHECK; eauto.
      constructor. gclo. econstructor; eauto. gfinal. left. apply H.
    + constructor. gstep. red. eapply IHEQVl; eauto.
  - remember (TauF t1) as x. hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; pclearbot; eauto.
    + constructor. gclo. econstructor; eauto. gfinal. left. apply H.
    + constructor. gstep. red. eapply IHEQVl; eauto.
  - eapply IHREL; eauto.
    remember (TauF t2) as x. 
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; subst; pclearbot; eauto.
    constructor; auto. pstep_reverse.
Qed.

Hint Resolve eqitC_wcompat_weak_approx : paco.

Global Instance geutt_cong_weak_itree_approx {E R1 R2 r rg RR} : Proper (@euttge E R1 R1 eq ==> @euttge E R2 R2 eq ==> flip impl) 
                                     (gpaco2 (weak_itree_approx_ RR id) (eqitC RR true true) r rg).  
Proof.
  repeat intro. gclo. econstructor; eauto. all : intros; subst; auto.
Qed.

Global Instance eq_itree_cong_weak_itree_approx {E R1 R2 r rg RR} : Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> flip impl) 
                                     (gpaco2 (weak_itree_approx_ RR id) (eqitC RR true true) r rg).  
Proof.
  repeat intro. gclo. econstructor; eauto.
  rewrite H. reflexivity. rewrite H0. reflexivity.
  all : intros; subst; auto.
Qed.

Ltac use_simpobs := repeat match goal with
                           | H : RetF _ = observe ?t |- _ => apply simpobs in H 
                           | H : TauF _ = observe ?t |- _ => apply simpobs in H
                           | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
                           end.

(*next *)
Lemma weak_itree_approx_trans : forall E R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) t1 t2 t3,
    @weak_itree_approx E R1 R2 RR1 t1 t2 -> weak_itree_approx RR2 t2 t3 -> weak_itree_approx (rcompose RR1 RR2) t1 t3.
Proof.
  ginit.
  intros E R1 R2 R3 RR1 RR2. gcofix CIH.
  intros t1 t2 t3 H12 H23. punfold H12. punfold H23.
  red in H12. red in H23. 
  remember (observe t1) as ot1. remember (observe t2) as ot2. remember (observe t3) as ot3.
  hinduction H12 before r; intros; use_simpobs; pclearbot.
  - rewrite Heqot1.
    remember (RetF r2) as x. hinduction H23 before r; intros; inv Heqx; subst; use_simpobs; eauto.
    + rewrite Heqot3. gstep. constructor. econstructor; eauto.
    + rewrite Heqot3. rewrite tau_euttge. eauto.
  - rewrite Heqot1. clear Heqot2. pclearbot. remember (VisF e k2) as x.
    hinduction H23 before r; intros; inv Heqx; inj_existT; subst; use_simpobs.
    + rewrite Heqot3. gstep. constructor. gfinal. left. pclearbot. eapply CIH; eauto.
    + rewrite Heqot3. rewrite tau_euttge. eauto.
  - rewrite Heqot1. remember (TauF t2) as x.
    hinduction H23 before r; intros; inv Heqx; inj_existT; subst; use_simpobs.
    + rewrite Heqot3. gstep. constructor. gfinal. left. pclearbot. eauto.
    + pclearbot. gstep. constructor. gfinal. left. eapply CIH; eauto. apply simpobs in Heqot3.
      rewrite <- itree_eta in Heqot3. rewrite Heqot3. auto.
    + rewrite Heqot3. rewrite (tau_euttge (t2) ). eauto.
  - rewrite Heqot1. gstep. constructor. gfinal. left. eapply CIH; eauto. apply simpobs in Heqot3.
    rewrite Heqot3. pstep. auto.
  - assert ( (exists t5, observe t3 = TauF t5) \/ (forall t5, observe t3 <> TauF t5) ).
    { destruct (observe t3). all : try (right; repeat intro; discriminate; fail). left. eexists; eauto. }
    destruct H.
    + destruct H as [t5 Ht5]. symmetry in Ht5. use_simpobs. rewrite Ht5. rewrite tau_euttge.
      eapply IHweak_itree_approxF; eauto.
      enough (weak_itree_approx RR2 t2 t5). punfold H. subst.
      assert (t3 ≈ t5). rewrite Ht5. rewrite tau_eutt. reflexivity. rewrite <- H.
      rewrite <- (tau_eutt t2). pfold. auto.
    + subst. remember (observe t3) as ot3. 
      remember (TauF t2) as x. hinduction H23 before r; intros; inv Heqx; subst; pclearbot; use_simpobs.
      * exfalso. eapply H0; eauto.
      * eapply IHweak_itree_approxF; eauto. punfold H.
      * exfalso. eapply H; eauto.
Qed.

Lemma weak_itree_approx_bind : forall E R S1 S2 (RS : S1 -> S2 -> Prop) (k : R -> itree E S2) (t : itree E R),
    weak_itree_approx RS (ITree.bind t (fun _ => ITree.spin)) (ITree.bind t k).
Proof.
  intros E R S1 S2 k. pcofix CIH.
  intros.
  destruct (observe t) eqn :  Heqt.
  - pfold. red. unfold observe at 1. unfold observe at 1. cbn. rewrite Heqt.
    cbn. constructor. left. eapply paco2_mon; try apply weak_itree_approx_spin_bottom.
    intros; contradiction.
  - pfold. red. unfold observe at 1. unfold observe at 1. cbn. rewrite Heqt.
    constructor. right. eapply CIH.
  - pfold. red. unfold observe at 1. unfold observe at 1. cbn. rewrite Heqt.
    constructor. right. eapply CIH.
Qed.

(*This may become the main definition of approximating ITrees*)
Section StrongITreeApprox.
  Context {E : Type -> Type}.
  Context {R1 R2: Type}.
  Context (RR : R1 -> R2 -> Prop).


  Variant strong_itree_approxF (sim : itree E R1 -> itree E R2 -> Prop) vclo : itree' E R1 -> itree' E R2 -> Prop :=
  | strong_itree_approx_Ret r1 r2 : RR r1 r2 -> strong_itree_approxF sim vclo (RetF r1) (RetF r2)
  | strong_itree_approxF_Vis A (e : E A) k1 k2 : (forall a, vclo sim (k1 a) (k2 a) : Prop) ->
                                          strong_itree_approxF sim vclo (VisF e k1) (VisF e k2)
  | strong_itree_approxF_TauLR t1 t2 : vclo sim t1 t2 -> strong_itree_approxF sim vclo (TauF t1) (TauF t2)
  | strong_itree_approxF_TauL t1 t2 : 
      (forall t3, observe t2 <> TauF t3) -> t1 ≅ ITree.spin -> strong_itree_approxF sim vclo (TauF t1) (observe t2)
  .

  
  Hint Constructors strong_itree_approxF.

  Definition strong_itree_approx_ vclo sim t1 t2 :=
    strong_itree_approxF sim vclo (observe t1) (observe t2).

    Lemma strong_itree_approxF_mono x0 x1 vclo vclo' sim sim'
        (IN: strong_itree_approxF sim vclo x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    strong_itree_approxF sim' vclo' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma strong_itree_approx__mono vclo (MON: monotone2 vclo) : monotone2 (strong_itree_approx_ vclo).
  Proof. do 2 red. intros. eapply strong_itree_approxF_mono; eauto. Qed.

  Definition strong_itree_approx : itree E R1 -> itree E R2 -> Prop :=
    paco2 (strong_itree_approx_ id) bot2.


End StrongITreeApprox.

#[global] Hint Constructors strong_itree_approxF: core.
#[global] Hint Unfold strong_itree_approx_: core.
#[global] Hint Resolve strong_itree_approx__mono : paco.
#[global] Hint Unfold strong_itree_approx: core.


Lemma strong_itree_approx_spin_bottom : forall E R1 R2 RR (t : itree E R2),
    strong_itree_approx RR (@ITree.spin E R1) t.
Proof.
  intros E R1 R2 RR. pcofix CIH. intros t. pfold. red. cbn.
  destruct (observe t).
  - rewrite itree_eta'. constructor. repeat intro; discriminate. reflexivity.
  - constructor. right. eauto.
  - rewrite itree_eta'. constructor. repeat intro; discriminate. reflexivity.
Qed.

Lemma strong_itree_approx_spin_unique : forall E R1 R2 RR (t : itree E R1),
    strong_itree_approx RR t (@ITree.spin E R2) -> t ≅ ITree.spin.
Proof.
  intros E R1 R2 RR. pcofix CIH.
  intros. pfold. red. cbn. punfold H0. red in H0. cbn in *.
  inv H0; pclearbot; eauto.
  exfalso. rewrite H1 in H2. eapply H2. reflexivity.
Qed.

Lemma strong_itree_approx_refl_eq_itree : forall E R (t1 t2 : itree E R),
    t1 ≅ t2 -> strong_itree_approx eq t1 t2.
Proof.
  intros E R. pcofix CIH. pfold. intros.
  punfold H0. red in H0. red. inv H0; pclearbot; eauto; try inv CHECK;
  constructor; right; eauto.
Qed.

Lemma strong_itree_approx_refl : forall E R (t : itree E R),
    strong_itree_approx eq t t.
Proof.
  intros; apply strong_itree_approx_refl_eq_itree. reflexivity.
Qed.

Lemma strong_itree_approx_TauLR : forall E R1 R2 RR (t1: itree E R1) (t2 : itree E R2) ,
    strong_itree_approx RR (Tau t1) (Tau t2) -> strong_itree_approx RR t1 t2.
Proof.
  intros E R1 R2 RR. pcofix CIH. intros.
  punfold H0. red in H0.
  cbn in *. inv H0; pclearbot; eauto.
  - eapply paco2_mon; eauto. intros; contradiction.
  - rewrite H1 in H2. exfalso. eapply H2. reflexivity.
Qed.

Lemma strong_itree_approx_antisym : forall E R (t1 t2 : itree E R),
    strong_itree_approx eq t1 t2 -> strong_itree_approx eq t2 t1 ->
    t1 ≅ t2.
Proof.
  intros E R. pcofix CIH.
  intros t1 t2 H12 H21. pfold. red.
  punfold H12. punfold H21. red in H12. red in H21.
  inv H12; try (rewrite <- H in H21; rewrite <- H0 in H21); inv H21; pclearbot; 
    inj_existT; subst; eauto.
  - constructor. right. eapply CIH; eauto.
  - rewrite H3 in H4. exfalso; eapply H4; eauto.
  - rewrite <- H3 in H1. exfalso. eapply H1; eauto.
  - rewrite <- H3 in H1. exfalso. eapply H1; eauto.
Qed.

Lemma strong_itree_approx_proper_l : forall E R1 R2 (RR : R1 -> R2 -> Prop) (t1 t1' : itree E R1) (t2 : itree E R2),
    t1 ≅ t1' -> strong_itree_approx RR t1 t2 -> strong_itree_approx RR t1' t2.
Proof.
  intros E R1 R2 RR. pcofix CIH. intros. pfold.
  red. punfold H1. red in H1. punfold H0. red in H0.
  inv H0; try rewrite <- H2 in H1; inv H1; try inv CHECK; pclearbot; eauto.
  - constructor. right. eapply CIH; eauto.
  - constructor. eauto. rewrite <- REL. auto.
  - inj_existT. subst. constructor. right. eapply CIH; eauto.
Qed.

Lemma strong_itree_approx_proper_r : forall E R1 R2 (RR : R1 -> R2 -> Prop) (t1: itree E R1) (t2 t2': itree E R2),
    t2 ≅ t2' -> strong_itree_approx RR t1 t2 -> strong_itree_approx RR t1 t2'.
Proof.
  intros E R1 R2 RR. pcofix CIH. intros. pfold.
  red. punfold H1. red in H1. punfold H0. red in H0.
  inv H0; try rewrite <- H2 in H1; inv H1; try inv CHECK; pclearbot; eauto.
  - constructor. right. eapply CIH; eauto.
  - rewrite H3 in H4. exfalso. eapply H4; eauto.
  - inj_existT. subst. constructor. right. eapply CIH; eauto.
  - rewrite itree_eta'. constructor. repeat intro; discriminate. auto.
Qed.

Instance strong_itree_approx_proper {E R1 R2 RR} : Proper (@eq_itree E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> Basics.flip impl ) (strong_itree_approx RR).
Proof.
  repeat intro. eapply strong_itree_approx_proper_r. symmetry. eauto.
  eapply strong_itree_approx_proper_l. symmetry. eauto. auto.
Qed.

Lemma strong_itree_approx_trans : forall E R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) t1 t2 t3,
    @strong_itree_approx E R1 R2 RR1 t1 t2 -> strong_itree_approx RR2 t2 t3 -> strong_itree_approx (rcompose RR1 RR2) t1 t3.
Proof.
  intros E R1 R2 R3 RR1 RR2. pcofix CIH.
  intros t1 t2 t3 H12 H23. punfold H12. punfold H23.
  pfold. red in H12. red in H23. red. inv H12; try rewrite <- H0 in H23.
  - inv H23. constructor. econstructor; eauto.
  - pclearbot. inv H23. inj_existT. subst.
    constructor. right. pclearbot. eapply CIH; eauto.
  - pclearbot.
    inv H23; pclearbot.
    + constructor. right. eapply CIH; eauto.
    + constructor. eauto. rewrite H5 in H1.
      eapply strong_itree_approx_spin_unique. eauto.
  - destruct (observe t3).
    + rewrite (itree_eta'). constructor. repeat intro. discriminate. auto.
    + constructor. left. eapply paco2_mon with (r := bot2). 2 : intros; contradiction.
      rewrite H2. apply strong_itree_approx_spin_bottom.
    + rewrite itree_eta'. constructor. repeat intro. discriminate. auto.
Qed.

