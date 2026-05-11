(** * Properties about rutt *)

(** [rutt] retains most of the structure of [eutt], including being an
  equivalence relation, inversion lemmas, and compatibility with [eq_itree] and
  [euttge]. *)

(** The main additions in this file are compatibility with [eutt], morphisms
  wrt. [REv] and [RAns], and an up-to principle. *)

(* begin hide *)
From Coinduction Require Import all. 

From Stdlib Require Import
  Program
  Setoid
  Morphisms
  RelationClasses.

From ITree Require Import
  ITree
  ITreeFacts
  Core.Subevent
  Basics.HeterogeneousRelations
  Eq.Rutt
  Props.Leaf.

(* end hide *)

(* Extra construction lemmas *)

Lemma rutt_trigger {E1 E2 R1 R2 REv RAns RR} (e1: E1 R1) (e2: E2 R2):
  (REv _ _ e1 e2: Prop) ->
  (forall t1 t2, (RAns _ _ e1 t1 e2 t2: Prop) -> (RR t1 t2: Prop)) ->
  rutt REv RAns RR (trigger e1) (trigger e2).
Proof.
  intros. apply rutt_Vis; auto.
  intros. apply rutt_Ret; auto.
Qed.

(* Morphisms related to [REv] and [RAns]. Both behave nicely up to quantified
   relation equality. There are also symmetry results when flipped.
*)

(* We can't use eq_rel directly due to dependent quantification *)
Definition eq_REv {E1 E2: Type -> Type} (REv1 REv2: forall A B, E1 A -> E2 B -> Prop) :=
  forall A B, eq_rel (REv1 A B) (REv2 A B).

#[global] Instance eq_REv_Equivalence {E1 E2}: Equivalence (@eq_REv E1 E2).
Proof.
  constructor.
  - red. red. reflexivity.
  - red. intros * H. red in H. red. now symmetry.
  - hnf. intros * H1 H2. red in H1, H2. red. etransitivity; eauto.
Qed.

Definition flip_REv {E1 E2: Type -> Type} (REv1: forall A B, E1 A -> E2 B -> Prop) :=
  fun B A e2 e1 => REv1 A B e1 e2.

Lemma flip_flip_REv {E1 E2} REv1:
  @eq_REv E1 E2 (flip_REv (flip_REv REv1)) REv1.
Proof. reflexivity. Qed.

(* For RAns we want to defer to eq_rel, but for that we need to regroup events
   and their return values into pairs.
*)
Definition RAns_pair E1 E2 (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) {A B}:
    relationH (E1 A * A) (E2 B * B) :=
  fun '(e1, a) '(e2, b) => RAns A B e1 a e2 b.

Lemma RAns_pair_iff {E1 E2 A B} RAns1:
  forall e1 (a:A) e2 (b:B), RAns_pair E1 E2 RAns1 (e1,a) (e2,b) <-> RAns1 A B e1 a e2 b.
Proof. reflexivity. Qed.

Definition eq_RAns {E1 E2} (RAns1 RAns2: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  forall A B, eq_rel (@RAns_pair E1 E2 RAns1 A B) (@RAns_pair E1 E2 RAns2 A B).

Lemma eq_RAns_iff {E1 E2} {RAns1 RAns2} (H: @eq_RAns E1 E2 RAns1 RAns2):
  forall A B e1 a e2 b, RAns2 A B e1 a e2 b <-> RAns1 A B e1 a e2 b.
Proof. intros *. rewrite <- ! RAns_pair_iff. split; apply H. Qed.

#[global] Instance eq_RAns_Equivalence {E1 E2}: Equivalence (@eq_RAns E1 E2).
Proof.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

Definition flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  fun B A e2 (b:B) e1 (a:A) => flip (@RAns_pair E1 E2 RAns A B) (e2, b) (e1, a).

Lemma flip_RAns_iff {E1 E2 A B} RAns:
  forall e1 (a:A) e2 (b:B), @flip_RAns E1 E2 RAns B A e2 b e1 a <-> RAns _ _ e1 a e2 b.
Proof. reflexivity. Qed.

Lemma flip_flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop):
  eq_RAns (flip_RAns (flip_RAns RAns)) RAns.
Proof. reflexivity. Qed.

Lemma rutt_flip {E1 E2 R1 R2 REv RAns RR} (t1: itree E1 R1) (t2: itree E2 R2):
  rutt REv RAns RR t1 t2 <-> rutt (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; coinduction c CIH; icbn; intros t1 t2 Hrutt; 
  step in Hrutt.
  - induction Hrutt; try now constructor.
    * apply EqTau. now apply CIH.
    * apply EqVis. auto. intros b a HAns. cbn in HAns.
      specialize (H0 a b HAns). now apply CIH.
  - induction Hrutt; try now constructor.
    * apply EqTau. now apply CIH.
    * apply EqVis. auto. intros b a HAns. cbn in HAns.
      specialize (H0 a b HAns). now apply CIH.
Qed.

(* Progressive [Proper] instances for [rutt] and congruence with eutt. *)

#[global] Instance rutt_Proper_R {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv1 REv2 HREv  RAns1 RAns2 HRAns RR1 RR2 HRR t1 _ <- t2 _ <-.
  split; intros Hrutt; 
    revert t1 t2 Hrutt; coinduction c CIH; intros t1 t2 Hrutt; 
    step in Hrutt; rcbn; 
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    1,4: apply EqRet; now apply HRR. 
    1,3: apply EqTau; now apply CIH.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns1 A B e1 a e2 b).
      { erewrite <- eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). now apply CIH.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns2 A B e1 a e2 b).
      { erewrite eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). now apply CIH.
Qed.

#[global] Instance eq_proper_ruttC {E1 E2 R1 R2 REv RAns}
  (RR : R1 -> R2 -> Prop) (c : Chain (@rutt_mon E1 E2 R1 R2 REv RAns)):
  Proper (eq_itree eq ==> eq_itree eq ==> iff) (elem c RR).
Proof.
  split; revert_until c; tower induction;
  intros x IH t1 t1' Ht1 t2 t2' Ht2;
  step in Ht1; step in Ht2; rcbn; intros Hrutt;
  genobs t1' ot1'; genobs t2' ot2';
  move Hrutt before IH; revert_until Hrutt;
  induction Hrutt; intros; subst.
  1-3,6-8: inv Ht1; inv Ht2; simpobs; try now constructor.
  + simpobs. constructor. eapply IH; eauto.
  + simpobs.
    dependent destruction H3; dependent destruction H4;
    dependent destruction H6; dependent destruction H7.
    constructor; auto. intros. eapply IH. apply REL. apply REL0. now apply H0.
  + simpobs. constructor. eapply IH; eauto.
  + simpobs.
    dependent destruction H4; dependent destruction H5;
    dependent destruction H7; dependent destruction H8.
    constructor; auto. intros. eapply IH. apply REL. apply REL0. now apply H0.
  + inv Ht1. constructor. eapply IHHrutt; eauto. now unstep.
  + inv Ht2. constructor. eapply IHHrutt; eauto. now unstep.
  + inv Ht1. constructor. eapply IHHrutt; eauto. now unstep.
  + inv Ht2. constructor. eapply IHHrutt; eauto. now unstep.
Qed.

#[global] Instance eq_proper_rutt {E1 E2 R1 R2 REv RAns}
  (RR : R1 -> R2 -> Prop):
  Proper (eq_itree eq ==> eq_itree eq ==> iff) (@rutt E1 E2 R1 R2 REv RAns RR).
Proof.
  unfold rutt. intros t1 t1' Ht1 t2 t2' Ht2.
  apply eq_proper_ruttC; auto.
Qed.

#[global] Instance rutt_Proper_R2 {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  rewrite Ht1, Ht2. apply rutt_Proper_R; auto.
Qed.

#[global] Instance euttge_proper_ruttC {E1 E2 R1 R2 REv RAns}
  (RR : R1 -> R2 -> Prop) (c : Chain (@rutt_mon E1 E2 R1 R2 REv RAns)):
  Proper (euttge eq ==> euttge eq ==> flip impl) (elem c RR).
Proof.
  unfold Proper, respectful, flip, impl.
  tower induction.
  clear c; intros c IH x x' EQx y y' EQy; step in EQx; step in EQy.
  rcbn; intros EQ.
  genobs x' ox'; genobs y' oy'.
  revert x x' y y' Heqox' Heqoy' EQx EQy.
  induction EQ; intros.

  (* EqRet *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. genret r1 or1. revert x Heqox.
    hinduction EQx before ox; try easy.
    + intros; subst; inv Heqor1. clear x Heqox.
      genobs y oy. genret r2 or2. revert y Heqoy.
      hinduction EQy before oy; try easy.
      * subst; intros [=<-] ? ?. constructor. auto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqTau *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. gentau m1 om1. revert x Heqox.
    hinduction EQx before ox; try easy.
    + intros [=<-] ? ?.
      genobs y oy. gentau m2 om2. revert y Heqoy.
      hinduction EQy before oy; try easy.
      * intros [=<-] ? ?. to_rmon_core. intros ? ?. rcbn. constructor. eapply IH; eauto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqVis *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. genvis e1 k1 ot1. revert x Heqox.
    hinduction EQx before ox; try easy.
    + intros. apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
      clear x Heqox.
      genobs y oy. genvis e2 k2 ot2. revert y Heqoy.
      hinduction EQy before oy; try easy.
      * intros. apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst.
        constructor; auto. intros. eapply IH. apply (REL a). apply (REL0 b). apply H0; auto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqTauL *)
  - edestruct euttge_tau_r_inv; [step; eauto |].
    simpobs.
    apply EqTauL; auto.
    eapply IHEQ; eauto.
    assert (euttge eq (Tau x0) (Tau t1)) by (now step).
    unstep; eapply euttge_tau_inv; eauto.

  (* EqTauR *)
  - edestruct euttge_tau_r_inv; [step; eauto |].
    simpobs.
    apply EqTauR; auto.
    eapply IHEQ; eauto.
    assert (euttge eq (Tau x0) (Tau t2)) by (now step).
    unstep; eapply euttge_tau_inv; eauto.
Qed.

#[global] Instance euttge_proper_rutt {E1 E2 R1 R2 REv RAns}
  (RR : R1 -> R2 -> Prop):
  Proper (euttge eq ==> euttge eq ==> flip impl) (@rutt E1 E2 R1 R2 REv RAns RR).
Proof.
  unfold rutt. intros t1 t1' Ht1 t2 t2' Ht2.
  apply euttge_proper_ruttC; auto.
Qed.

Lemma rutt_cong_eutt {E1 E2 R1 R2}:
  forall REv RAns RR (t1: itree E1 R1) t1' (t2: itree E2 R2),
  rutt REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  rutt REv RAns RR t1' t2.
Proof.
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  coinduction c CIH; icbn; intros t1 t1' Heutt t2 Hrutt.
  step in Hrutt.
  rewrite (itree_eta t1') in Heutt.
  remember (observe t1) as ot1 eqn:Hot1.
  remember (observe t2) as ot2 eqn:Hot2.
  move Hrutt before CIH; revert_until Hrutt.
  induction Hrutt as [r1 r2|m1 m2| |m1 ot2'|]; intros tt1 tt1' Heutt' tt2 Hot1' Hot2'.
  - (* EqRet *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear Hot1' Hot2' tt1 tt2.
    remember (RetF r1) as oRetL eqn:HoRetL.
    induction Heutt'; try discriminate.
    + inv HoRetL. now constructor.
    + apply EqTauL. now apply IHHeutt'.
  - (* EqTau *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear tt1 Hot1'.
    clear tt2 Hot2'.
    step in H. rcbn in H.
    remember (TauF m1) as oTauL eqn:HoTauL.
    revert m1 m2 H HoTauL.
    induction Heutt' as [r1 r2 _|m1' m1''|U' e1 k1 k1' _|t1' ot1' _ IHHeutt'|t1'' m1''];
      intros m1 m2 H HoTauL; try discriminate.
    + (* EqTau of Heutt' *)
      inv HoTauL. apply EqTau. apply CIH with m1.
      * apply REL.
      * unfold rutt. step. exact H.
    + (* EqTauL of Heutt': need to case on the head of m1 *)
      inv HoTauL.
      destruct (observe m1) as [r1|m1_body|U1 e1 k1] eqn:Hobs_m1.
      * (* m1 = Ret r1 *)
        remember (RetF r1) as oRetL eqn:HoRetL.
        clear Hobs_m1 m1 IHIHHeutt'.
        revert H.
        induction IHHeutt'; try discriminate; intros.
        ** inv HoRetL.
           apply EqTauR.
           remember (RetF r1) as oRetL2 eqn:HoRetL2.
           induction H; try discriminate.
           *** inv HoRetL2. constructor. now subst.
           *** apply EqTauR. now apply IHruttF.
        ** apply EqTauL. apply IHIHHeutt'; auto.
      * (* m1 = Tau m1_body *)
        apply (IHIHHeutt' m1_body m2); auto.
        apply ruttF_inv_tau_l in H. exact H.
      * (* m1 = Vis e1 k1 *)
        remember (VisF e1 k1) as oVisL eqn:HoVisL.
        clear Hobs_m1 m1 IHIHHeutt'.
        revert H.
        induction IHHeutt'; try discriminate; intros.
        ** symmetry in HoVisL; dependent destruction HoVisL.
           apply EqTauR.
           remember (VisF e k0) as oVisL2 eqn:HoVisL2.
           induction H; try discriminate.
           *** dependent destruction HoVisL2.
               apply EqVis; auto. intros a b HAns.
               apply CIH with (k0 a).
               **** apply REL.
               **** apply H0; auto.
           *** apply EqTauR. apply IHruttF; auto.
        ** apply EqTauL. apply IHIHHeutt'; auto.
    + (* EqTauR of Heutt' *)
      apply EqTau. apply CIH with m1.
      * rewrite <- tau_eutt with (t:=m1). step. subst t1''. exact Heutt'.
      * unfold rutt. step. exact H.
  - (* EqVis *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear tt1 Hot1' tt2 Hot2'.
    remember (VisF e1 k1) as oVisL eqn:HoVisL.
    induction Heutt'; try discriminate; intros.
    + dependent destruction HoVisL.
      apply EqVis; auto. intros a b HAns.
      apply CIH with (k1 a).
      * apply REL.
      * apply H0; auto.
    + apply EqTauL. apply IHHeutt'; auto.
  - (* EqTauL *)
    eapply IHHrutt with (t1 := m1) (t1' := tt1') (t2 := tt2); auto.
    rewrite <- tau_eutt with (t:=m1). rewrite <- Heutt'.
    rewrite (itree_eta tt1). rewrite <- Hot1'. reflexivity.
  - (* EqTauR *)
    apply EqTauR. eapply IHHrutt; eauto.
Qed.

#[global] Instance rutt_Proper_R3 {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  - eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
  - symmetry in Ht1, Ht2.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
Qed.

(* Bind closure and bind lemmas. *)

Section RuttBind.
Context {E1 E2 : Type -> Type}.
Context {R1 R2 : Type}.
Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
Context (RR : R1 -> R2 -> Prop).

End RuttBind.

Lemma rutt_bind {E1 E2 R1 R2 T1 T2}
      (REv: forall A B, E1 A -> E2 B -> Prop)
      (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
      (RR: R1 -> R2 -> Prop) (RT: T1 -> T2 -> Prop) t1 t2 k1 k2:
    rutt REv RAns RR t1 t2 ->
    (forall r1 r2,
      RR r1 r2 ->
      rutt REv RAns RT (k1 r1) (k2 r2)) ->
    rutt REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  revert t1 t2. coinduction c CIH. icbn. intros t1 t2 Hrutt EQK.
  step in Hrutt.
  genobs t1 ot1. genobs t2 ot2.
  hinduction Hrutt before CIH; intros.
  - (* Ret *)
    rewrite !observe_bind; simpobs.
    specialize (EQK _ _ H).
     step in EQK. now do 2 step.
  - (* Tau *)
    rewrite !observe_bind; simpobs.
    apply EqTau. apply CIH; auto.
  - (* Vis *)
    rewrite !observe_bind; simpobs.
    apply EqVis; auto. intros a b HAns.
    apply CIH; auto. now apply H0. 
  - (* TauL *)
    rewrite observe_bind; simpobs.
    apply EqTauL. apply IHHrutt; auto.
  - (* TauR *)
    setoid_rewrite observe_bind at 2; simpobs.
    apply EqTauR. apply IHHrutt; auto.
Qed.


Section RuttMrec.
  Context (D1 D2 E1 E2 : Type -> Type) (bodies1 : D1 ~> itree (D1 +' E1)) (bodies2 : D2 ~> itree (D2 +' E2)).
  Context (RPre : prerel E1 E2) (RPreInv : prerel D1 D2) (RPost : postrel E1 E2) (RPostInv : postrel D1 D2).

  Context (Hbodies : forall A B (d1 : D1 A) (d2 : D2 B), 
              RPreInv A B d1 d2 -> 
              rutt (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
            (fun (a : A) (b : B) => RPostInv A B d1 a d2 b) (bodies1 A d1) (bodies2 B d2) ).

  Lemma interp_mrec_rutt (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : forall  (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
      rutt (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost) RR t1 t2 ->
      rutt RPre RPost RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
  Proof.
    coinduction c CIH. icbn. 
    intros t1 t2 Ht12. step in Ht12. 
    remember (observe t1) as ot1. remember (observe t2) as ot2.
    hinduction Ht12 before R1; intros; to_rmon. 
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn. now constructor.  
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn. constructor; now apply CIH. 
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn.
      inv H.
      + apply inj_pair2 in H1, H4. subst. constructor.
        eapply CIH.  
        eapply rutt_bind; eauto.
        intros. cbn in H. clear - H H0. apply H0. now constructor.
      + apply inj_pair2 in H1, H4. subst. constructor.
        auto. intros. repeat rewrite tau_euttge. eapply CIH. 
        clear - H0 H. apply H0. now constructor. 
    - apply simpobs in Heqot1. rewrite Heqot1. rewrite unfold_interp_mrec at 1. 
      cbn. constructor. now apply IHHt12. 
    - apply simpobs in Heqot2. rewrite Heqot2. setoid_rewrite unfold_interp_mrec at 2.
      cbn. constructor. now apply IHHt12. 
  Qed.

  Lemma mrec_rutt (A B : Type) (d1 : D1 A) (d2 : D2 B) : 
    RPreInv A B d1 d2 ->
    rutt RPre RPost (fun (a : A) (b : B) => RPostInv A B d1 a d2 b) 
         (mrec bodies1 d1) (mrec bodies2 d2).
  Proof.
    intros. apply interp_mrec_rutt. auto.
  Qed.

End RuttMrec.
