From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.EqdepFacts
     Program.Equality
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(* will need more propositional constraints on Preorders *)

Section SecureProgInsens.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).
  Context (RE : forall A, E A -> E A -> Prop).


  Variant pi_secure_eqitF (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=

    (* eqitF constructors *)
    | pisecEqRet r1 r2 : RR r1 r2 -> pi_secure_eqitF b1 b2 l vclo sim (RetF r1) (RetF r2)
    | pisecEqTau t1 t2 : sim t1 t2 -> pi_secure_eqitF b1 b2 l vclo sim (TauF t1) (TauF t2)
    | pisecEqTauL t1 t2 (CHECK : b1) : sim t1 t2 -> pi_secure_eqitF b1 b2 l vclo sim (TauF t1) (observe t2)
    | pisecEqTauR t1 t2 (CHECK : b2) : sim t1 t2 -> pi_secure_eqitF b1 b2 l vclo sim (observe t1) (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | piEqVisPriv {A} (e1 e2 : E A) k1 k2 (SECCHECK1 : leq (priv A e1) l) (SECCHECK2 : leq (priv A e2) l ) :
        RE A e1 e2 -> ((forall a, vclo sim (k1 a) (k2 a) : Prop)) -> 
        pi_secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    | piEqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim (k1 a) t2) -> pi_secure_eqitF b1 b2 l vclo sim (VisF e k1) (TauF t2)
    | piEqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim t1 (k2 a)) -> pi_secure_eqitF b1 b2 l vclo sim (TauF t1) (VisF e k2)
    | piEqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
        :
        (forall a b, vclo sim (k1 a) (k2 b)) -> pi_secure_eqitF b1 b2 l vclo sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | piEqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim (k1 a) t2 ) ->
        pi_secure_eqitF b1 b2 l vclo sim (VisF e k1) (observe t2)
    | piEqVisUnPrivRInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, vclo sim t1 (k2 a) ) ->
        pi_secure_eqitF b1 b2 l vclo sim (observe t1) (VisF e k2)
  .

  Hint Constructors pi_secure_eqitF : core.

  Definition pi_secure_eqit_ (b1 b2 : bool) (l : L) vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => pi_secure_eqitF b1 b2 l vclo sim (observe t1) (observe t2).

  Hint Unfold pi_secure_eqit_ : core.

  Lemma pi_secure_eqitF_mono b1 b2 l x0 x1 vclo vclo' sim sim'
        (IN: pi_secure_eqitF b1 b2 l vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    pi_secure_eqitF b1 b2 l vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma pi_secure_eqit_mono b1 b2 l vclo (MON: monotone2 vclo) : monotone2 (pi_secure_eqit_ b1 b2 l vclo).
  Proof.
    do 2 red. intros; eapply pi_secure_eqitF_mono; eauto.
  Qed.

  Hint Resolve pi_secure_eqit_mono : paco.

  Definition pi_eqit_secure b1 b2 l := paco2 (pi_secure_eqit_ b1 b2 l id) bot2.

  (* want and eqitC_secure which could help prove some interesting stuff

   *)


End SecureProgInsens.

Hint Resolve pi_secure_eqit_mono : paco.

Hint Constructors pi_secure_eqitF : core.



Ltac unpriv_pi := try apply piEqVisUnPrivVisCo;
                  try apply piEqVisUnPrivTauLCo;
                  try apply piEqVisUnPrivTauRCo;
                  try apply piEqVisUnPrivLInd;
                  try apply piEqVisUnPrivRInd;
                  auto; intros.

Ltac contra_size :=
  match goal with
  | [ Hemp : empty ?A, Hne : nonempty ?A |- _ ] => inv Hemp; inv Hne; contradiction end.


Lemma eqit_secure_imp_pi_eqit_scure b1 b2 E RE  R1 R2 RR Label priv l : forall (t1 : itree E R1) (t2 : itree E R2),
    (forall A, Equivalence (RE A) ) ->
    eqit_secure Label priv RR b1 b2 l t1 t2 -> pi_eqit_secure Label priv RR RE b1 b2 l t1 t2.
Proof.
  pcofix CIH. intros t1 t2 HRE Hps. pfold. red. punfold Hps. red in Hps.
  hinduction Hps before r; intros.
  - constructor; auto.
  - constructor. right. pclearbot. eauto.
  - rewrite itree_eta'. constructor; auto. right. eapply CIH; auto. pfold. apply Hps.
  - rewrite itree_eta' at 1. constructor; auto. right. eapply CIH; auto. pfold. apply Hps.
  - pclearbot. constructor; auto. reflexivity. right. eapply CIH; eauto. apply H.
  - pclearbot. unpriv_pi. right. eapply CIH; auto; apply H.
  - pclearbot. unpriv_pi. right. eapply CIH; auto; apply H.
  - pclearbot. unpriv_pi. right. eapply CIH; auto; apply H.
  - pclearbot. unpriv_pi. right. eapply CIH; auto. pfold. apply H.
  - pclearbot. unpriv_pi. right. eapply CIH; auto. pfold. apply H.
  - unpriv_pi. inv SIZECHECK. contradiction.
  - unpriv_pi. inv SIZECHECK. contradiction.
  - unpriv_pi. inv SIZECHECK. contradiction.
  - unpriv_pi. inv SIZECHECK. contradiction.
Qed.


Lemma pi_eqit_secure_sym b1 b2 E RE R1 R2 RR Label priv l : 
  (forall A, Equivalence (RE A) ) ->
  forall (t1 : itree E R1) (t2 : itree E R2),
    pi_eqit_secure Label priv RR RE b1 b2 l t1 t2 -> pi_eqit_secure Label priv (flip RR) RE b2 b1 l t2 t1.
Proof.
  intro HRE.
  pcofix CIH. intros t1 t2 Hsec.
  punfold Hsec. pfold. red in Hsec. red. inversion Hsec; pclearbot; eauto;
  try (unpriv_pi; right; eapply CIH; apply H1; fail).
  constructor; auto. symmetry. auto. right. eapply CIH; apply H2.
Qed.


Lemma pi_secure_eqit_mon : forall E RE (b1 b2 b3 b4 : bool) R1 R2 RR1 RR2 Label priv l
      (t1 : itree E R1) (t2 : itree E R2),
    (forall A, Equivalence (RE A)) ->
    (b1 -> b3) -> (b2 -> b4) -> (RR1 <2= RR2) ->
    pi_eqit_secure Label priv RR1 RE b1 b2 l t1 t2 -> pi_eqit_secure Label priv RR2 RE b3 b4 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1. pcofix CIH.
  intros t1 t2 Ht12. pstep. red.
  punfold Ht12. red in Ht12.
  hinduction Ht12 before r; intros; eauto; pclearbot;
  try (unpriv_pi; right; apply CIH; try red; eauto; fail);
  constructor; auto. right.  apply CIH; apply H4.
Qed.


Lemma pi_eqit_secure_spin b E RE R1 R2 (RR : R1 -> R2 -> Prop) Label priv l : forall (t1 : itree E R1),
    pi_eqit_secure Label priv RR RE b true l t1 (ITree.spin).
Proof.
  pcofix CIH. intros. pfold. red. cbn. constructor; auto.
Qed.

Lemma pi_eqit_secure_private_halt b E RE R1 R2 (RR : R1 -> R2 -> Prop) Label priv l A (e : E A) k:
  empty A -> ~ leq (priv A e) l -> forall (t1 : itree E R1),
    pi_eqit_secure Label priv RR RE b true l t1 (Vis e k).
Proof.
  intros HA t1. pfold. red. cbn. intros. unpriv_pi. inv HA; contradiction.
Qed.

Lemma pi_eqit_secure_mixed_trans_aux1:
  forall (E : Type -> Type) RE (R1 : Type) (b2 : bool) (R2 : Type) (RR1 : R1 -> R2 -> Prop)
    (Label : Preorder) (priv : forall A : Type, E A -> L) (l : L) t1 t2,
    paco2 (pi_secure_eqit_ Label priv RR1 RE true b2 l id) bot2 t1 (Tau t2)  ->
    pi_eqit_secure Label priv RR1 RE true b2 l t1 t2.
Proof.
  intros E RE R1 b2 R2 RR1 Label priv l. pcofix CIH.
  intros t1 t2 Htau. punfold Htau. red in Htau.
  pfold. red. cbn in *. inv Htau; pclearbot; eauto.
  - constructor; auto. left. eapply paco2_mon; eauto. intros; contradiction.
  - constructor; auto. right. eapply CIH; eauto. pfold. red. rewrite <- H0.
    cbn. pstep_reverse.
  - pstep_reverse. eapply paco2_mon; eauto. intros; contradiction.
  - unpriv_pi. left.  eapply paco2_mon; eauto. intros; contradiction.
  - unpriv_pi. right. eapply CIH. pfold. red. rewrite <- H0.
    cbn. pstep_reverse.
Qed.

Lemma pi_eqit_secure_mixed_trans_aux2:
  forall (E : Type -> Type) RE (R1 : Type) (b2 : bool) (R2 : Type) (RR1 : R1 -> R2 -> Prop)
    (Label : Preorder) (priv : forall A : Type, E A -> L) (l : L) t1 t2,
    paco2 (pi_secure_eqit_ Label priv RR1 RE b2 true l id) bot2 (Tau t1) t2  ->
    pi_eqit_secure Label priv RR1 RE b2 true l t1 t2.
Proof.
  intros E RE R1 b2 R2 RR1 Label priv l. pcofix CIH.
  intros t1 t2 Htau. punfold Htau. red in Htau.
  pfold. red. cbn in *. inv Htau; pclearbot; eauto.
  - constructor; auto. left. eapply paco2_mon; eauto. intros; contradiction.
  - pstep_reverse. eapply paco2_mon; eauto. intros; contradiction.
  - constructor; auto. right. eapply CIH; eauto. pfold. red. rewrite <- H.
    cbn. pstep_reverse.
  - unpriv_pi. left.  eapply paco2_mon; eauto. intros; contradiction.
  - unpriv_pi. right. eapply CIH. pfold. red. rewrite <- H.
    cbn. pstep_reverse.
Qed.

Lemma pi_eqit_secure_mixed_trans b1 b2 E RE R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      Label priv l : 
  forall (t1 : itree E R1) t2 t3, 
    pi_eqit_secure Label priv RR1 RE b1 b2 l t1 t2 -> eqit RR2 b1 b2 t2 t3 ->
    pi_eqit_secure Label priv (rcompose RR1 RR2) RE b1 b2 l t1 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 Hsec Heq. punfold Heq.
  red in Heq. punfold Hsec. red in Hsec. pfold. red.
  hinduction Heq before r; intros; try inv CHECK; pclearbot.
  - inv Hsec; eauto; unpriv_pi; pclearbot.
    + rewrite itree_eta'. constructor; auto. right. eapply CIH; eauto.
      pfold. red. rewrite H0. constructor. auto.
    + rewrite itree_eta'. unpriv_pi. right. eapply CIH; eauto.
      apply H1. pfold. red. rewrite H0. constructor; auto.
  - inv Hsec; pclearbot; eauto.
    + constructor. right. eapply CIH; eauto.
      pfold. red. rewrite H0. constructor; auto. pstep_reverse.
    + unpriv_pi. right. eapply CIH; eauto. apply H1.
    + rewrite itree_eta'. unpriv_pi. right. eapply CIH; eauto.
      inv CHECK. apply pi_eqit_secure_mixed_trans_aux1.
      pfold. red. rewrite <- H0. cbn. pstep_reverse.
  - inv Hsec.
    + pclearbot. rewrite itree_eta'. constructor; auto. right. eapply CIH; eauto.
      pfold. red. rewrite H0. constructor. left. auto.
    + ITrace.inj_existT. subst. constructor; auto. right. 
      pclearbot. eapply CIH; eauto. apply H4.
    + ITrace.inj_existT. subst. unpriv_pi. right. pclearbot.
      eapply CIH; eauto. apply H1.
    + ITrace.inj_existT. subst. unpriv_pi. right. pclearbot.
      eapply CIH; eauto. apply H1.
    + pclearbot. remember (VisF e k2) as ovis. rewrite itree_eta'.
      unpriv_pi. rewrite Heqovis. right. eapply CIH; eauto. apply H1.
      pfold. red. rewrite H0. constructor. left. auto.
    + ITrace.inj_existT. subst. unpriv_pi. right. eapply CIH; eauto. pclearbot. apply H1.
  - eapply IHHeq; eauto. clear IHHeq. inv Hsec; pclearbot.
    + constructor; auto.
    + constructor; auto. left. apply pi_eqit_secure_mixed_trans_aux1. pfold. red.
      rewrite <- H0. cbn. pstep_reverse.
    + pstep_reverse.
    + unpriv_pi.
    + unpriv_pi. left. apply pi_eqit_secure_mixed_trans_aux1. pfold. red.
      rewrite <- H0. cbn. pstep_reverse.
  - constructor; auto. left. pfold. eapply IHHeq; eauto.
Qed.

Lemma pi_eqit_secure_mixed_trans_l b1 b2 E RE R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      Label priv l : 
  forall (t1 : itree E R1) t2 t3, 
    pi_eqit_secure Label priv RR2 RE b1 b2 l t2 t3 -> eqit RR1 b1 b2 t1 t2 ->
    pi_eqit_secure Label priv (rcompose RR1 RR2) RE b1 b2 l t1 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 Hsec Heq. punfold Heq.
  red in Heq. punfold Hsec. red in Hsec. pfold. red.
  hinduction Heq before r; intros; try inv CHECK; pclearbot.
  - inv Hsec; eauto; unpriv_pi; pclearbot.
    + rewrite itree_eta' at 1. constructor; auto. right. eapply CIH; eauto.
      pfold. red. rewrite H. constructor. auto.
    + rewrite itree_eta' at 1. unpriv_pi. right. eapply CIH; eauto.
      apply H1. pfold. red. rewrite H. constructor; auto.
  - inv Hsec; pclearbot; eauto.
    + constructor. right. eapply CIH; eauto.
      pfold. red. rewrite H. constructor; auto. pstep_reverse.
    + unpriv_pi. right. eapply CIH; eauto. apply H1.
    + rewrite itree_eta' at 1. unpriv_pi. right. eapply CIH; eauto.
      inv CHECK. apply pi_eqit_secure_mixed_trans_aux2.
      pfold. red. rewrite <- H. cbn. pstep_reverse.
  - inv Hsec.
    + pclearbot. rewrite itree_eta' at 1. constructor; auto. right. eapply CIH; eauto.
      pfold. red. rewrite H. constructor. left. auto.
    + ITrace.inj_existT. subst. constructor; auto. right. 
      pclearbot. eapply CIH; eauto. apply H4.
    + ITrace.inj_existT. subst. unpriv_pi. right. pclearbot.
      eapply CIH; eauto. apply H0.
    + ITrace.inj_existT. subst. unpriv_pi. right. pclearbot.
      eapply CIH; eauto. apply H0.
    + ITrace.inj_existT. subst. unpriv_pi. right. eapply CIH; eauto. pclearbot. apply H0.
    + pclearbot. remember (VisF e k1) as ovis. rewrite itree_eta' at 1.
      unpriv_pi. rewrite Heqovis. right. eapply CIH; eauto. apply H1.
      pfold. red. rewrite H. constructor. left. auto.
  - constructor; auto. left. pfold. eapply IHHeq; eauto.
  - eapply IHHeq; eauto. clear IHHeq. inv Hsec; pclearbot.
    + constructor; auto.
    + pstep_reverse.
    + constructor; auto. left. apply pi_eqit_secure_mixed_trans_aux2. pfold. red.
      rewrite <- H. cbn. pstep_reverse.
    + unpriv_pi.
    + unpriv_pi. left. apply pi_eqit_secure_mixed_trans_aux2. pfold. red.
      rewrite <- H. cbn. pstep_reverse.
Qed.

Lemma pi_eqit_secure_RR_imp b1 b2 E RE R1 R2 (RR1 : R1 -> R2 -> Prop ) (RR2 : R1 -> R2 -> Prop)
      Label priv l : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) ->
                     forall (t1 : itree E R1) (t2 : itree E R2), 
      pi_eqit_secure Label priv RR1 RE b1 b2 l t1 t2 -> 
      pi_eqit_secure Label priv RR2 RE b1 b2 l t1 t2.
Proof.
  intro Himp. pcofix CIH.
  intros. pfold. red. punfold H0. red in H0.
  inv H0; eauto;
  try (constructor; auto; pclearbot; eauto; fail);
  try (pclearbot; constructor; auto; right; eapply CIH; eauto; try apply H2; fail).
  constructor; auto. pclearbot. right. eapply CIH; eauto. apply H3.
Qed.


Lemma pi_eqit_secureC_wcompat_id E RE :  
  forall b1 b2 R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l,
  wcompatible2 (@pi_secure_eqit_ E R1 R2 Label priv RR RE b1 b2 l id) 
                                         (eqitC RR b1 b2) .
Proof.
  econstructor. pmonauto.
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. unfold_eqit. red in REL. red.
  hinduction REL before r; intros; clear t1' t2'; try inv CHECK.
  - genobs_clear t1 ot1. genobs_clear t2 ot2.
    remember (RetF r1) as x.
    hinduction EQVl before r; intros; inv Heqx; eauto.
    + remember (RetF r3) as y.
      hinduction EQVr before r; intros; inv Heqy; eauto.
      rewrite itree_eta' at 1. constructor; eauto. gstep. red.
      eapply IHEQVr; eauto.
    + rewrite itree_eta'. constructor; auto. cbn. gstep. red. cbn.
      eauto.
  - remember (TauF t1) as y.
    hinduction EQVl before r; intros; inv Heqy; try inv CHECK; subst; eauto.
    + remember (TauF t2) as x.
      hinduction EQVr before r; intros; inv Heqx; try inv CHECK; subst; eauto.
      pclearbot. constructor. gclo. econstructor; cycle -1; eauto with paco.
      pclearbot.
      remember (TauF m1) as ot1. rewrite itree_eta' at 1.
      constructor; auto. rewrite Heqot1. gstep. red. cbn. eauto.
    + constructor; auto. gstep. red. eapply IHEQVl; eauto.
  - inv EQVl; pclearbot; try inv CHECK.
    + constructor; auto. gclo. econstructor; cycle -1; eauto with paco.
    + constructor; auto. gclo. econstructor; cycle -1; eauto with paco.
      apply eqit_inv_tauR. pfold. auto.
  - inv EQVr; pclearbot; try inv CHECK.
    + constructor; auto. gclo. econstructor; cycle -1; eauto with paco.
    + constructor; auto. gclo. econstructor; cycle -1; eauto with paco.
      apply eqit_inv_tauR. pfold. auto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    + ITrace.inj_existT. subst. remember (VisF e2 k3) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
      * ITrace.inj_existT. subst. constructor; auto.
        intros. apply gpaco2_clo. pclearbot. econstructor; eauto. apply H0.
      * pclearbot. remember (VisF e1 k1) as ovis. rewrite itree_eta' at 1.
        constructor; auto. rewrite Heqovis. gstep. red. eapply IHEQVr; eauto.
    + remember (VisF e2 k2) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto; ITrace.inj_existT; subst .
      * setoid_rewrite itree_eta' at 2. constructor; auto.
        gstep. red.
        pclearbot. clear IHEQVl. remember (VisF e1 k0) as y.
        hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto; 
          ITrace.inj_existT; subst.
        ++ constructor; auto. pclearbot. 
           intros. gclo. econstructor; eauto. gfinal. left. apply H0. 
        ++ constructor; auto. gstep. red. eapply IHEQVl; eauto.
      * rewrite itree_eta' at 1. constructor 4; auto.
        gstep. red. eapply IHEQVr; eauto.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    + ITrace.inj_existT. subst. pclearbot. remember (TauF t2) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; pclearbot; eauto.
      * unpriv_pi. gclo. econstructor; cycle -1; eauto with paco. gfinal. left. apply H.
      * remember (VisF e0 k1) as ovis. rewrite itree_eta' at 1. constructor; auto.
        rewrite Heqovis. gstep. red. eapply IHEQVr; eauto.
    + constructor; auto. gstep. red. eapply IHEQVl; eauto.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    + remember (VisF e k2) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
      * ITrace.inj_existT. subst.
        pclearbot. unpriv_pi. gclo. econstructor; cycle -1; eauto with paco.
        gfinal. left. apply H.
      * remember (TauF m1) as otm1. rewrite itree_eta' at 1. constructor; auto.
        gstep. rewrite Heqotm1. red. eapply IHEQVr; eauto.
   + constructor; auto. gstep. red. eapply IHEQVl; eauto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    + ITrace.inj_existT. subst. remember (VisF e2 k3) as y.
      hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
      * ITrace.inj_existT. subst. unpriv_pi. gclo. pclearbot.
        econstructor; cycle -1; eauto with paco. gfinal. left. apply H.
      * remember (VisF e1 k1) as ovis. rewrite itree_eta' at 1.
        constructor; auto. rewrite Heqovis. gstep. eapply IHEQVr; eauto.
    + remember (VisF e2 k2) as x.
      hinduction EQVr before r; intros; inv Heqx; try inv CHECK; subst; eauto.
      * ITrace.inj_existT. subst. pclearbot. unpriv_pi.
         gclo. econstructor; cycle -1; eauto with paco.
         Unshelve. 3 : apply (Vis e1 k0). pfold. apply EQVl.
         gstep. red. cbn. unpriv_pi. gfinal. left. apply H.
       * remember (TauF t3) as ott3. rewrite itree_eta' at 1. constructor; auto.
         rewrite Heqott3. gstep. red. eapply IHEQVr; eauto.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    + ITrace.inj_existT. subst. pclearbot. unpriv_pi.
      gclo. econstructor; cycle -1; eauto with paco. gfinal. left. apply H.
    + constructor; auto. gstep. eapply IHEQVl; eauto.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto.
    + ITrace.inj_existT. subst. pclearbot. unpriv_pi.
      gclo. econstructor; cycle -1; eauto with paco. gfinal. left. apply H.
    + constructor; auto. gstep. eapply IHEQVr; eauto.
Qed.

Hint Resolve pi_eqit_secureC_wcompat_id.

Global Instance geuttgen_cong_secure_eqit {E RE} {Label priv l} {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop} 
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} : 
    (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
    (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
    Proper (@eq_itree E R1 R1 RR1 ==> eq_itree RR2 ==> flip impl)
           (gpaco2 (pi_secure_eqit_ Label priv RS RE b1 b2 l id) (eqitC RS b1 b2) r rg ).
Proof.
  repeat intro. gclo. econstructor; eauto.
  - eapply eqit_mon, H1; eauto; discriminate.
  - eapply eqit_mon, H2; eauto; discriminate.
Qed.

Global Instance geuttgen_cong_eq_secure_eqit {E RE} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} : 
    Proper (@eq_itree E R1 R1 eq ==> eq_itree eq ==> flip impl)
           (gpaco2 (pi_secure_eqit_ Label priv RS RE b1 b2 l id) (eqitC RS b1 b2) r rg ).
Proof.
  intro. eapply geuttgen_cong_secure_eqit; eauto; intros; subst; auto.
Qed.

Global Instance pi_eqit_secure_eq_itree_proper {E RE} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) :
   Proper (@eutt E R1 R1 eq ==> eutt eq ==> flip impl)
          (pi_eqit_secure Label priv RS RE true true l).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34. intros Hsec.
  apply pi_eqit_secure_RR_imp with (RR1 := rcompose RS eq).
  { intros. inv H. auto. }
  eapply pi_eqit_secure_mixed_trans; auto. 2: { symmetry in Ht34. apply Ht34. }
  apply pi_eqit_secure_RR_imp with (RR1 := rcompose eq RS).
  { intros. inv H. auto. }
  eapply pi_eqit_secure_mixed_trans_l; eauto.
Qed.

Global Instance pi_eqit_secure_eutt_proper {E RE} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) :
   Proper (@eq_itree E R1 R1 eq ==> eq_itree eq ==> flip impl)
          (pi_eqit_secure Label priv RS RE b1 b2 l).
Proof.
  repeat intro. ginit. rewrite H, H0; auto. gfinal. eauto.
Qed.

Lemma pi_eqit_secure_ret E RE Label priv l b1 b2 R1 R2 (RR : R1 -> R2 -> Prop) r1 r2 : 
  RR r1 r2 -> @pi_eqit_secure E R1 R2 Label priv RR RE b1 b2 l (Ret r1) (Ret r2).
Proof.
  intros; pfold; constructor; auto.
Qed.

Lemma pi_eqit_secure_bind E RE Label priv l b1 b2 R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) k1 k2 : 
  forall (t1 : itree E R1) (t2 : itree E R2), 
    (forall (r1 : R1) (r2 : R2), RR r1 r2 -> pi_eqit_secure Label priv RS RE b1 b2 l (k1 r1) (k2 r2) ) ->
    pi_eqit_secure Label priv RR RE b1 b2 l t1 t2 ->
    pi_eqit_secure Label priv RS RE b1 b2 l (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  ginit. gcofix CIH. intros. pinversion H1.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    repeat rewrite bind_ret_l. gfinal. right. eapply paco2_mon; try apply H0; auto.
    intros; contradiction.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    repeat rewrite bind_tau. gstep. constructor. gfinal. left. eapply CIH; eauto.
  - apply simpobs in H. apply simpobs in H2.  rewrite H2. rewrite H. rewrite bind_tau.
    gstep. constructor; auto. gfinal. left. eapply CIH; eauto.
    pfold. red. cbn. pstep_reverse.
  - apply simpobs in H. apply simpobs in H2.  rewrite H2. rewrite H. rewrite bind_tau.
    gstep. constructor; auto. gfinal. left. eapply CIH; eauto.
    pfold. red. cbn. pstep_reverse.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    repeat rewrite bind_vis. gstep. constructor; auto.
    gfinal. left. eapply CIH; eauto. apply H4.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    rewrite bind_vis. rewrite bind_tau. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH; eauto. apply H3.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    rewrite bind_vis. rewrite bind_tau. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH; eauto. apply H3.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    repeat rewrite bind_vis. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH; eauto. apply H3.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    rewrite bind_vis. gstep. red. unpriv_pi.
    gfinal. left. eapply CIH; eauto. pfold. red. cbn. pstep_reverse.
  - apply simpobs in H. apply simpobs in H2. rewrite H. rewrite H2.
    rewrite bind_vis. gstep. red. unpriv_pi.
    gfinal. left. eapply CIH; eauto. pfold. red. cbn. pstep_reverse.
Qed.

Lemma pi_eqit_secure_iter_bind_aux:
  forall (E : Type -> Type) RE (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2)) (r : itree E B1 -> itree E B2 -> Prop),
    (forall (a1 : A1) (a2 : A2), RA a1 a2 -> r (ITree.iter body1 a1) (ITree.iter body2 a2)) ->
    forall (t1 : itree E (A1 + B1)) (t2 : itree E (A2 + B2)),
      paco2 (pi_secure_eqit_ Label priv (HeterogeneousRelations.sum_rel RA RB) RE b1 b2 l id) bot2 t1
            t2 ->
      gpaco2 (pi_secure_eqit_ Label priv RB RE b1 b2 l id) (eqitC RB b1 b2) r r
             (ITree.bind t1
                         (fun lr : A1 + B1 =>
                            match lr with
                            | inl l0 => Tau (ITree.iter body1 l0)
                            | inr r0 => Ret r0
                            end))
             (ITree.bind t2
                         (fun lr : A2 + B2 =>
                            match lr with
                            | inl l0 => Tau (ITree.iter body2 l0)
                            | inr r0 => Ret r0
                            end)).
Proof.
  intros E RE B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 r CIH t1 t2 H2.
  generalize dependent t2. revert t1. gcofix CIH'. intros t1 t2 Ht12.
  pinversion Ht12; apply simpobs in H; apply simpobs in H0.
  - rewrite H, H0. repeat rewrite bind_ret_l. inv H1.
    + gstep. constructor. gfinal. left. apply CIH'0. eapply CIH; eauto.
    + gstep. constructor; auto.
  - rewrite H, H0. repeat rewrite bind_tau. gstep. constructor.
    gfinal. left. eapply CIH'; eauto.
  - rewrite H. rewrite <- itree_eta in H0. rewrite H0. rewrite bind_tau. gstep.
    constructor; auto. gfinal.
    left. eapply CIH'; eauto.
  - rewrite H0. rewrite <- itree_eta in H. rewrite H. rewrite bind_tau. gstep.
    constructor; auto. gfinal.
    left. eapply CIH'; eauto.
  - rewrite H, H0. repeat rewrite bind_vis. gstep. constructor; auto.
    intros. gfinal. left. eauto.
  - rewrite H, H0. rewrite bind_vis, bind_tau.  gstep. unpriv_pi; auto.
    intros. gfinal. left. eauto.
  - rewrite H, H0. rewrite bind_vis, bind_tau.  gstep. unpriv_pi; auto.
    intros. gfinal. left. eauto.
  - rewrite H, H0. repeat rewrite bind_vis. gstep. unpriv_pi.
    gfinal. left. eauto.
  - rewrite H. rewrite <- itree_eta in H0. rewrite H0. rewrite bind_vis.
    gstep. unpriv_pi. gfinal. left. eauto.
  - rewrite H0. rewrite <- itree_eta in H. rewrite H. rewrite bind_vis.
    gstep. unpriv_pi. gfinal. left. eauto.
Qed.

Lemma secure_eqit_iter E RE A1 A2 B1 B2 (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
                           b1 b2 Label priv l 
                           (body1 : A1 -> itree E (A1 + B1) ) (body2 : A2 -> itree E (A2 + B2) ): 
  (forall a1 a2, RA a1 a2 -> pi_eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) RE b1 b2 l (body1 a1) (body2 a2) ) ->
                           forall (a1 : A1) (a2 : A2), RA a1 a2 ->
    pi_eqit_secure Label priv RB RE b1 b2 l (ITree.iter body1 a1) (ITree.iter body2 a2).
Proof.
  intro Hbody. ginit. gcofix CIH. intros. rewrite unfold_iter. rewrite unfold_iter. 
  apply Hbody in H0. pinversion H0; apply simpobs in H; apply simpobs in H1.
  - rewrite H. rewrite H1. repeat rewrite bind_ret_l. inv H2.
    + gstep. constructor. gfinal. left. eapply CIH; eauto.
    + gstep. constructor; auto.
  - rewrite H. rewrite H1. repeat rewrite bind_tau. gstep.
    constructor. eapply pi_eqit_secure_iter_bind_aux; eauto.
  - rewrite H. rewrite bind_tau. gstep. constructor; auto.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
    assert (t1 ≈ body1 a1).
    { rewrite H. rewrite tau_eutt. reflexivity. } 
    inv CHECK. rewrite <- itree_eta in H1. rewrite H1. auto.
  - rewrite H1. rewrite bind_tau. gstep. constructor; auto.
    eapply pi_eqit_secure_iter_bind_aux; eauto. rewrite H.
    rewrite <- itree_eta. apply H2.
  - rewrite H, H1. repeat rewrite bind_vis. gstep. constructor; auto.
    intros. red.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
  - rewrite H, H1. rewrite bind_vis, bind_tau. gstep. unpriv_pi.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
  - rewrite H, H1. rewrite bind_vis, bind_tau. gstep. unpriv_pi.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
  - rewrite H, H1. repeat rewrite bind_vis. gstep. unpriv_pi.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
  - rewrite H. rewrite bind_vis. gstep. unpriv_pi.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
    rewrite H1. rewrite <- itree_eta. apply H2.
  - rewrite H1. rewrite bind_vis. gstep. unpriv_pi. red.
    rewrite H. rewrite <- itree_eta.
    eapply pi_eqit_secure_iter_bind_aux; eauto.
Qed.
