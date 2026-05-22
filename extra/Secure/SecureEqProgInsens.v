From Coinduction Require Import all.
From Stdlib Require Import Morphisms Program.Basics.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(* will need more propositional constraints on Preorders *)

Section SecureProgInsens.
  Context {E : Type -> Type} {R1 R2 : Type}.
  Context (Label : Preorder).
  Context (priv : forall A, E A -> L).
  Context (RR : R1 -> R2 -> Prop).

  (*
  Context (RE : forall A, E A -> E A -> A -> A -> Prop).
  want it to be an equivalence
  *)

  Variant pi_secure_eqitF (b1 b2 : bool) (l : L) (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=

    (* eqitF constructors *)
    | pisecEqRet r1 r2 : RR r1 r2 -> pi_secure_eqitF b1 b2 l sim (RetF r1) (RetF r2)
    | pisecEqTau t1 t2 : sim t1 t2 -> pi_secure_eqitF b1 b2 l sim (TauF t1) (TauF t2)
    | pisecEqTauL t1 t2 (CHECK : b1) : sim t1 t2 -> pi_secure_eqitF b1 b2 l sim (TauF t1) (observe t2)
    | pisecEqTauR t1 t2 (CHECK : b2) : sim t1 t2 -> pi_secure_eqitF b1 b2 l sim (observe t1) (TauF t2)
    (* info_flow protecting coinductive constructors *)
    | piEqVisPriv {A} (e : E A) k1 k2 (SECCHECK : leq (priv A e) l) :
        ((forall a, sim (k1 a) (k2 a) : Prop)) -> pi_secure_eqitF b1 b2 l sim (VisF e k1) (VisF e k2)
    | piEqVisUnPrivTauLCo {A} (e : E A) k1 t2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, sim (k1 a) t2) -> pi_secure_eqitF b1 b2 l sim (VisF e k1) (TauF t2)
    | piEqVisUnPrivTauRCo {A} (e : E A) t1 k2 (SECCHECK : ~ leq (priv A e) l) :
        (forall a, sim t1 (k2 a)) -> pi_secure_eqitF b1 b2 l sim (TauF t1) (VisF e k2)
    | piEqVisUnPrivVisCo {A B} (e1 : E A) (e2 : E B) k1 k2 (SECCHECK1 : ~ leq (priv A e1) l) (SECCHECK2 : ~ leq (priv B e2) l)
        :
        (forall a b, sim (k1 a) (k2 b)) -> pi_secure_eqitF b1 b2 l sim (VisF e1 k1) (VisF e2 k2)
    (* info_flow protecting inductive constructors *)
    | piEqVisUnPrivLInd {A} (e : E A) k1 t2 (CHECK : b1) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, sim (k1 a) t2 ) ->
        pi_secure_eqitF b1 b2 l sim (VisF e k1) (observe t2)
    | piEqVisUnPrivRInd {A} (e : E A) t1 k2 (CHECK : b2) (SECCHECK : ~ leq (priv A e) l) :
        (forall a, sim t1 (k2 a) ) ->
        pi_secure_eqitF b1 b2 l sim (observe t1) (VisF e k2)
  .

  Hint Constructors pi_secure_eqitF : itree.

  Definition pi_secure_eqit_ (b1 b2 : bool) (l : L) (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => pi_secure_eqitF b1 b2 l sim (observe t1) (observe t2).

  Hint Unfold pi_secure_eqit_ : itree.

  Lemma pi_secure_eqitF_mono b1 b2 l :
    Proper (respectful Coinduction.lattice.leq Coinduction.lattice.leq)
      (pi_secure_eqit_ b1 b2 l).
  Proof.
    intros!. red; red in H0.
    induction H0; try solve [constructor; intros; eauto with itree; now apply H].
  Qed.

  Definition pi_secure_eqit_mon b1 b2 l := Build_mon (pi_secure_eqitF_mono b1 b2 l).

  Definition pi_eqit_secure b1 b2 l := gfp (pi_secure_eqit_mon b1 b2 l).

End SecureProgInsens.

#[export] Hint Constructors pi_secure_eqitF : itree.
#[global] Hint Constructors pi_secure_eqitF : itree.

Ltac unpriv_pi := try apply piEqVisUnPrivVisCo;
                  try apply piEqVisUnPrivTauLCo;
                  try apply piEqVisUnPrivTauRCo;
                  try apply piEqVisUnPrivLInd;
                  try apply piEqVisUnPrivRInd;
                  auto with itree; intros.

Ltac contra_size :=
  match goal with
  | [ Hemp : empty ?A, Hne : nonempty ?A |- _ ] => inv Hemp; inv Hne; contradiction end.

#[local] Ltac taul := apply pisecEqTauL; [auto|].
#[local] Ltac taur := apply pisecEqTauR; [auto|].

Lemma eqit_secure_imp_pi_eqit_scure b1 b2 E R1 R2 RR Label priv l : forall (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR b1 b2 l t1 t2 -> pi_eqit_secure Label priv RR b1 b2 l t1 t2.
Proof.
  icoinduction c CIH. intros t1 t2 Hps. step in Hps.
  hinduction Hps before c; intros.
  - constructor; auto with itree.
  - constructor. apply CIH. apply H.
  - rewrite itree_eta'. constructor; auto with itree. eapply CIH. step. apply Hps.
  - rewrite itree_eta' at 1. constructor; auto with itree. eapply CIH. step. apply Hps.
  - constructor; auto with itree. intros. apply CIH. apply H.
  - unpriv_pi. eapply CIH; apply H.
  - unpriv_pi. eapply CIH; apply H.
  - unpriv_pi. eapply CIH; apply H.
  - unpriv_pi. eapply CIH. step. apply H.
  - unpriv_pi. eapply CIH. step. apply H.
  - unpriv_pi; inv SIZECHECK; contradiction.
  - unpriv_pi; inv SIZECHECK; contradiction.
  - unpriv_pi; inv SIZECHECK; contradiction.
  - unpriv_pi; inv SIZECHECK; contradiction.
Qed.


Lemma pi_eqit_secure_sym b1 b2 E R1 R2 RR Label priv l : forall (t1 : itree E R1) (t2 : itree E R2),
    pi_eqit_secure Label priv RR b1 b2 l t1 t2 -> pi_eqit_secure Label priv (flip RR) b2 b1 l t2 t1.
Proof.
  icoinduction c CIH. intros t1 t2 Hsec. step in Hsec.
  hinduction Hsec before c; intros; eauto with itree;
  try (unpriv_pi; apply CIH; apply H; fail).
  constructor; auto. intros. apply CIH. apply H.
Qed.


Lemma pi_secure_eqit_mono : forall E (b1 b2 b3 b4 : bool) R1 R2 RR1 RR2 Label priv l
      (t1 : itree E R1) (t2 : itree E R2),
    (b1 -> b3) -> (b2 -> b4) -> (RR1 <= RR2) ->
    pi_eqit_secure Label priv RR1 b1 b2 l t1 t2 -> pi_eqit_secure Label priv RR2 b3 b4 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1. coinduction c CIH.
  intros t1 t2 Ht12. icbn.
  step in Ht12.
  hinduction Ht12 before l; intros;
  try (unpriv_pi; apply CIH; try red; eauto; fail);
  eauto with itree.
  - constructor; auto. now apply H2.
  - constructor; intros; eauto. eapply CIH. apply H.
Qed.


Lemma pi_eqit_secure_spin b E R1 R2 (RR : R1 -> R2 -> Prop) Label priv l : forall (t1 : itree E R1),
    pi_eqit_secure Label priv RR b true l t1 (ITree.spin).
Proof.
  icoinduction c CIH. intros. cbn. constructor; auto.
Qed.

Lemma pi_eqit_secure_private_halt b E R1 R2 (RR : R1 -> R2 -> Prop) Label priv l A (e : E A) k:
  empty A -> ~ leq (priv A e) l -> forall (t1 : itree E R1),
    pi_eqit_secure Label priv RR b true l t1 (Vis e k).
Proof.
  intros HA Hleq t1. step. cbn. unpriv_pi. inv HA; contradiction.
Qed.

Lemma pi_eqit_secure_mixed_trans_aux1:
  forall (E : Type -> Type) (R1 : Type) (b2 : bool) (R2 : Type) (RR1 : R1 -> R2 -> Prop)
    (Label : Preorder) (priv : forall A : Type, E A -> L) (l : L) t1 t2,
    pi_eqit_secure Label priv RR1 true b2 l t1 (Tau t2)  ->
    pi_eqit_secure Label priv RR1 true b2 l t1 t2.
Proof.
  intros E R1 b2 R2 RR1 Label priv l. coinduction c CIH.
  intros t1 t2 Htau. step in Htau.
  icbn. cbn in *.
  inv Htau; eauto with itree.
  - constructor; auto. apply (gfp_chain c). apply H1.
  - constructor; auto. apply CIH. step. rewrite <- H0. step in H1. apply H1.
  - apply (gfp_bchain c). apply H1.
  - unpriv_pi. apply (gfp_chain c). apply H1.
  - unpriv_pi. apply CIH. step. rewrite <- H0. specialize (H1 a). step in H1. apply H1.
Qed.

Lemma pi_eqit_secure_mixed_trans b1 b2 E R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      Label priv l : forall (t1 : itree E R1) t2 t3,
    pi_eqit_secure Label priv RR1 b1 b2 l t1 t2 -> eqit b1 b2 RR2 t2 t3 ->
    pi_eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  coinduction c CIH. intros t1 t2 t3 Hsec Heq.
  step in Heq. step in Hsec. icbn. cbn in *.
  hinduction Heq before c; intros.
  - inv Hsec; eauto with itree; unpriv_pi.
    + rewrite itree_eta'. constructor; auto with itree. eapply CIH; eauto. step. rewrite H0. constructor. auto.
    + rewrite itree_eta'. unpriv_pi. eapply CIH; eauto. apply H1. step. rewrite H0. constructor; auto.
  - inv Hsec; eauto with itree.
    + constructor. eapply CIH; eauto with itree. step. rewrite H0. constructor; auto. now step in REL.
    + unpriv_pi. eapply CIH; eauto. apply H1.
    + unpriv_pi. eapply CIH. apply H1. step. rewrite H0. apply EqTauL; auto. now step in REL.
  - inv Hsec.
    + rewrite itree_eta'. constructor; auto. eapply CIH; eauto. step. rewrite H0. apply EqVis. apply REL.
    + ddestruction. subst. constructor; auto with itree. intros a. eapply CIH. apply H1. apply REL.
    + ddestruction. subst. unpriv_pi. eapply CIH. apply H1. apply REL.
    + ddestruction. subst. unpriv_pi. eapply CIH. apply H1. apply REL.
    + remember (VisF e k2) as ovis. rewrite itree_eta'. unpriv_pi. rewrite Heqovis. eapply CIH. apply H1. step. rewrite H0. apply EqVis. apply REL.
    + ddestruction. subst. unpriv_pi. eapply CIH. apply H1. apply REL.
  - eapply IHHeq; eauto. clear IHHeq. inv Hsec.
    + constructor; auto.
    + inv CHECK. constructor; auto. apply pi_eqit_secure_mixed_trans_aux1. step. rewrite <- H0. now step in H1.
    + now step in H1.
    + unpriv_pi.
    + inv CHECK0. unpriv_pi. apply pi_eqit_secure_mixed_trans_aux1. step. rewrite <- H0. specialize (H1 a). step in H1. apply H1.
  - constructor; auto. step. eapply IHHeq; eauto.
Qed.

Lemma pi_eqit_secure_RR_imp b1 b2 E R1 R2 (RR1 : R1 -> R2 -> Prop ) (RR2 : R1 -> R2 -> Prop)
      Label priv l : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) ->
                     forall (t1 : itree E R1) (t2 : itree E R2),
      pi_eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
      pi_eqit_secure Label priv RR2 b1 b2 l t1 t2.
Proof.
  intros Himp.
  icoinduction c CIH. intros t1 t2 Ht12. step in Ht12.
  hinduction Ht12 before c; intros; eauto with itree;
  try ( constructor; auto; intros; eapply CIH; eauto; fail);
  try ( unpriv_pi; intros; eapply CIH; eauto; apply H; fail).
  constructor; auto. intros. eapply CIH. apply H.
Qed.

Ltac inv_eq_itree := 
  repeat match goal with 
  | [ H : eqitF _ false false _ (RetF _) _ |- _ ] => inv H
  | [ H : eqitF _ false false _ _ (RetF _) |- _ ] => inv H
  | [ H : eqitF _ false false _ (TauF _) _ |- _ ] => inv H
  | [ H : eqitF _ false false _ _ (TauF _) |- _ ] => inv H
  | [ H : eqitF _ false false _ (VisF _ _) _ |- _ ] => inv H
  | [ H : eqitF _ false false _ _ (VisF _ _) |- _ ] => inv H
  end. 

#[local] Ltac taul ::= eapply pisecEqTauL; [auto|].
#[local] Ltac taur ::= eapply pisecEqTauR; [auto|].

(* #[global] Instance pi_eqit_secure_proper_secureC {E R1 R2}  Label priv (RR : R1 -> R2 -> Prop) l
  (c : Chain (pi_secure_eqit_mon Label priv RR true true l)) :
  Proper (euttge (E := E) eq ==> euttge eq ==> flip impl) (elem c).
Proof with eauto with itree. 
   unfold Proper, respectful, flip, impl.
  tower induction.
  clear c; intros c IH x x' EQx y y' EQy; step in EQx; step in EQy.
    intros EQ. icbn; icbn in EQ. 
    genobs x' ox'; genobs y' oy'.
    (* [hinduction] is not sufficient here, because [move] is unable to pass
         through [ox] to reach [x] *)
    revert x x' y y' Heqox' Heqoy' EQx EQy.
    induction EQ; intros.
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genret r1 or1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros; subst; inv Heqor1. clear x Heqox.
        genobs y oy; genret r2 or2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        subst; intros [=<-] ??...
        intros. rewrite itree_eta' at 1; taur. step. eapply IHEQy; eauto. 
      * intros; subst. taul. step. eapply IHEQx... 
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      gentau t1 om1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros [=<-] ? ??.
        clear x Heqox.
        genobs y oy; gentau t2 om2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros [=<-] ??...
        intros. rewrite itree_eta' at 1.  
        taur.
        now step; eapply IHEQy.
      * intros; subst; taul; step; eapply IHEQx...
     + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taul.
      eapply IH.
      assert (euttge eq (Tau x0) (Tau t1)) by (now step).
      eapply euttge_tau_inv; eauto. unstep in EQy. apply EQy. assumption. 

    + edestruct euttge_tau_r_inv; [step; eauto |].
      simpobs.
      taur.
      eapply IH. 
      unstep in EQx. apply EQx. 
      assert (euttge eq (Tau x0) (Tau t2)) by (now step).
      eapply euttge_tau_inv; eauto.
      assumption. 
    + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genvis e k1 ot1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros.
        apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
        clear x Heqox.
        genobs y oy; genvis e k2 ot2.
        revert y Heqoy.
        hinduction EQy before oy; try easy.
        intros; apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst; eauto with itree.
        intros.
        rewrite itree_eta' at 1. taur.
        now step; eapply IHEQy.
      * intros; subst; taul; step; eapply IHEQx...
     + clear x' y' Heqox' Heqoy'.
      genobs x ox.
      genvis e k1 ot1.
      revert x Heqox.
      hinduction EQx before ox; try easy.
      * intros.
        apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
        clear x Heqox.
        genobs y oy; genvis e k0 ot2.
        revert y Heqoy.  
        remember (TauF t2).
        hinduction EQy before oy; intros; subst; try easy.
        -- inv Heqi. constructor 6; intros; auto.  eapply IH. apply REL. apply REL0. apply H.  
        -- rewrite itree_eta' at 1. taur. 
        step. eapply IHEQy; eauto. 
      * intros; subst; taul; step; eapply IHEQx...
    + clear x' y' Heqox' Heqoy'.
      genobs y oy.
      genvis e k2 ot2.
      revert y Heqoy.
      hinduction EQy before oy; try easy.
      * intros.
        apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst.
        clear y Heqoy.
        genobs x ox; genvis e k1 ot2.
        revert x Heqox.  
        remember (TauF t1).
        hinduction EQx before ox; intros; subst; try easy.
        -- inv Heqi. constructor 7; intros; auto.  eapply IH. apply REL. apply REL0. apply H.  
        -- rewrite itree_eta'. taul. 
        step. eapply IHEQx; eauto. 
      * intros; subst; taur; step; eapply IHEQy...
    + 
Qed.  *)


(* Chain-level congruence: rewriting under [eq_itree eq] on either side of a
   chain element.  This replaces the paco-style [pi_eqit_secureC_wcompat_id]
   (weak compatibility of the [eqitC] up-to-eq_itree closure).  *)
#[global] Instance pi_eqit_secure_proper_secureC {E R1 R2} b1 b2 Label priv (RR : R1 -> R2 -> Prop) l
  (c : Chain (pi_secure_eqit_mon Label priv RR b1 b2 l)) :
  Proper (eq_itree (E := E) eq ==> eq_itree eq ==> flip impl) (elem c).
Proof.
  do 5 red. tower induction. clear c. intros c CIH t1 t2 H12 t3 t4 H34 Hpi.
  icbn; icbn in Hpi. step in H12; step in H34. 
  induction Hpi; inv_eq_itree.
  (* ret and coinductive cases are simple *)
  1,2: eauto with itree. 
  - taul. eapply CIH. apply REL. step; apply H34. assumption. 
  - taur. eapply CIH. step; apply H12. apply REL. assumption. 
  - ddestruction. evis.  
  - ddestruction. unpriv_pi. eapply CIH. apply REL0. apply REL. apply H. 
  - ddestruction. unpriv_pi. eapply CIH. apply REL. apply REL0. apply H.
  - ddestruction. unpriv_pi. eapply CIH. apply REL0. apply REL. apply H.
  - ddestruction. unpriv_pi. eapply CIH. apply REL. step; apply H34. apply H. 
  - ddestruction. unpriv_pi. eapply CIH. step; apply H12. apply REL. apply H.
Qed. 


#[global] Instance pi_eqit_secure_eq_itree_proper {E} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) :
   Proper (@eq_itree E R1 R1 eq ==> eq_itree eq ==> flip impl)
          (pi_eqit_secure Label priv RS b1 b2 l).
Proof.
  eapply pi_eqit_secure_proper_secureC with
    (c := chain_gfp (pi_secure_eqit_mon Label priv RS b1 b2 l)).
Qed.

Global Instance pi_eqit_secure_eutt_proper {E} {Label priv l} {R1 R2 : Type} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) :
   Proper (@eutt E R1 R1 eq ==> eutt eq ==> flip impl)
          (pi_eqit_secure Label priv RS true true l).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34. intros Hsec.
  apply pi_eqit_secure_RR_imp with (RR1 := rcompose RS eq).
  intros r0 r3 Hr; inv Hr; auto.
  eapply pi_eqit_secure_mixed_trans; cycle 1.
  symmetry in Ht34. apply Ht34.
  apply pi_eqit_secure_sym in Hsec. apply pi_eqit_secure_sym.
  symmetry in Ht12.
  apply pi_eqit_secure_RR_imp with (RR1 := rcompose (flip RS) eq).
  intros r0 r3 Hr; inv Hr; auto.
  eapply pi_eqit_secure_mixed_trans; eauto.
Qed.


Lemma pi_eqit_secure_ret E Label priv l b1 b2 R1 R2 (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 -> @pi_eqit_secure E R1 R2 Label priv RR b1 b2 l (Ret r1) (Ret r2).
Proof.
  intros; step; constructor; auto.
Qed.

Lemma pi_eqit_secure_bind E Label priv l b1 b2 R1 R2 S1 S2 (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) k1 k2 :
  forall (t1 : itree E R1) (t2 : itree E R2)
  (c : Chain (pi_secure_eqit_mon Label priv RS b1 b2 l)),
    (forall (r1 : R1) (r2 : R2), RR r1 r2 -> elem c (k1 r1) (k2 r2) ) ->
    pi_eqit_secure Label priv RR b1 b2 l t1 t2 ->
    elem c (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  #[local] Ltac by_coinduction CIH := eapply CIH; intros; 
                                      try solve [now simpobs_subst]; 
                                      solve [now step; apply_foralls].
  intros t1 t2 c. revert t1 t2. tower induction.
  clear c; intros c CIH t1 t2 Hk1k2 Ht1t2.
  step in Ht1t2. genobs t1 ot1. genobs t2 ot2; icbn. 
  hinduction Ht1t2 before c; intros. 
  - rewrite 2 observe_bind. simpobs. now apply Hk1k2.
  - rewrite 2 observe_bind. simpobs. etau. 
    by_coinduction CIH. 
  - rewrite observe_bind. simpobs. apply pisecEqTauL; auto.
    by_coinduction CIH.
  - rewrite (observe_bind t3). simpobs. etau. 
    by_coinduction CIH. 
  - rewrite 2 observe_bind. simpobs. apply piEqVisPriv; auto. intros a.
    by_coinduction CIH. 
  - rewrite 2 observe_bind. simpobs. apply piEqVisUnPrivTauLCo; auto. intros a.
    by_coinduction CIH. 
  - rewrite 2 observe_bind. simpobs. apply piEqVisUnPrivTauRCo; auto. intros a.
    by_coinduction CIH. 
  - rewrite 2 observe_bind. simpobs. apply piEqVisUnPrivVisCo; auto. intros a b.
    by_coinduction CIH. 
  - rewrite observe_bind. simpobs. apply piEqVisUnPrivLInd; auto. intros a.
    by_coinduction CIH. 
  - rewrite (observe_bind t2). simpobs. apply piEqVisUnPrivRInd; auto. intros a.
    by_coinduction CIH. 
Qed.

Lemma pi_eqit_secure_iter_bind_aux:
  forall (E : Type -> Type) (B2 B1 A1 A2 : Type) (RA : A1 -> A2 -> Prop)
    (RB : B1 -> B2 -> Prop) (b1 b2 : bool) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (body1 : A1 -> itree E (A1 + B1))
    (body2 : A2 -> itree E (A2 + B2))
    (c : Chain (pi_secure_eqit_mon Label priv RB b1 b2 l)),
    (forall (a1 : A1) (a2 : A2), RA a1 a2 -> elem c (ITree.iter body1 a1) (ITree.iter body2 a2)) ->
    forall (t1 : itree E (A1 + B1)) (t2 : itree E (A2 + B2)),
      pi_eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l t1 t2 ->
      elem c
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
  intros E B2 B1 A1 A2 RA RB b1 b2 Label priv l body1 body2 c. 
  tower induction. clear c; intros c CIH Hbody t1 t2 Ht12. step in Ht12. 
  icbn. genobs t1 ot1. genobs t2 ot2.
  hinduction Ht12 before E; intros. 
  #[local] Ltac break_observe := unfold observe; cbn; simpobs; cbn. 
  (* QUESTION: why does 'now step; apply Hbody' instead of auto fail? *)
  #[local] Ltac pi_solve CIH := constructor; auto; intros; by_coinduction CIH.
  - break_observe. inv H; cbn; eauto with itree.
    constructor. now step; apply Hbody. 
  - break_observe. pi_solve CIH.
  - unfold observe at 1; cbn; simpobs. pi_solve CIH.
  - unfold observe at 2; cbn; simpobs. pi_solve CIH.
  - break_observe. pi_solve CIH.
  - break_observe. pi_solve CIH.
  - break_observe. pi_solve CIH.
  - break_observe. pi_solve CIH.
  - unfold observe at 1; cbn; simpobs. pi_solve CIH.
  - unfold observe at 2; cbn; simpobs. pi_solve CIH.
Qed. 


Lemma secure_eqit_iter E A1 A2 B1 B2 (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
                           b1 b2 Label priv l
                           (body1 : A1 -> itree E (A1 + B1) ) (body2 : A2 -> itree E (A2 + B2) ):
                           forall (a1 : A1) (a2 : A2), RA a1 a2 ->
  (forall a1 a2, RA a1 a2 -> pi_eqit_secure Label priv (HeterogeneousRelations.sum_rel RA RB) b1 b2 l (body1 a1) (body2 a2) ) ->
    pi_eqit_secure Label priv RB b1 b2 l (ITree.iter body1 a1) (ITree.iter body2 a2).
Proof.
  intros. rename H0 into Hbody. generalize dependent a2. revert a1.
  icoinduction c CIH.
  intros a1 a2 Ha. specialize (Hbody a1 a2 Ha) as Hbodya.
  step in Hbodya.
  remember (observe (body1 a1)).
  remember (observe (body2 a2)).
  hinduction Hbodya before E; intros; cbn; auto with itree.
  - break_observe. inv H; cbn; eauto with itree. 
  - break_observe. constructor. 
    eapply pi_eqit_secure_iter_bind_aux; eauto.
    (* taul, taur hard *)
  - unfold observe at 1; cbn; simpobs. constructor; auto. ITree.fold_subst.
    rewrite unfold_iter. eapply pi_eqit_secure_iter_bind_aux; eauto. 
    now simpobs_subst.   
  - unfold observe at 2; cbn; simpobs. constructor; auto. ITree.fold_subst.
    rewrite unfold_iter. eapply pi_eqit_secure_iter_bind_aux; eauto. 
    now simpobs_subst.   
  - break_observe. constructor; auto. intro. eapply pi_eqit_secure_iter_bind_aux; eauto. apply H. 
  - break_observe. constructor; intros; auto. eapply pi_eqit_secure_iter_bind_aux; intros. 
    apply CIH; eauto. apply H. 
  - break_observe. constructor; intros; auto. eapply pi_eqit_secure_iter_bind_aux; eauto. 
    apply H. 
  - break_observe. constructor; intros; auto. eapply pi_eqit_secure_iter_bind_aux; eauto. 
    apply H. 
  - unfold observe at 1; cbn; simpobs; cbn. constructor; intros; auto. 
    rewrite unfold_iter. 
    eapply pi_eqit_secure_iter_bind_aux; eauto. now simpobs_subst. 
  - unfold observe at 2; cbn; simpobs; cbn. constructor; intros; auto. 
    rewrite unfold_iter. 
    eapply pi_eqit_secure_iter_bind_aux; eauto. now simpobs_subst. 
Qed. 

Lemma secure_eqit_ret : forall (E : Type -> Type) Label priv l b1 b2 (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (r1 : R1) (r2 : R2),
    RR r1 r2 -> @eqit_secure E R1 R2 Label priv RR b1 b2 l (Ret r1) (Ret r2).
Proof.
  intros. step. constructor. auto.
Qed.
