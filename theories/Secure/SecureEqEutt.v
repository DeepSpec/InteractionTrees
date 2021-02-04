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
     Secure.SecureEq
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac unpriv_co := try apply EqVisUnPrivVisCo; 
                  try apply EqVisUnPrivTauLCo; 
                  try apply EqVisUnPrivTauRCo; 
                  auto; intros.

Ltac unpriv_ind := try apply EqVisUnPrivLInd;
                   try apply EqVisUnPrivRInd;
                   auto; intros.

Lemma tau_eqit_secure : forall E R1 R2 Label priv l RR (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR true true l (Tau t1) t2 -> eqit_secure Label priv RR true true l t1 t2.
Proof.
  intros E R1 R2 Label priv l RR.  intros t1 t2 Hsec. pstep. red.
  punfold Hsec. red in Hsec. cbn in *. remember (TauF t1) as x.
  hinduction Hsec before priv; intros;  inv Heqx; pclearbot; try inv CHECK; auto.
  - constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse.
Qed.

Lemma unpriv_e_eqit_secure : forall E A R1 R2 Label priv l RR (e : E A) (k : A -> itree E R1) 
      (t : itree E R2),
    (~leq (priv A e) l ) ->
    eqit_secure Label priv RR true true l (Vis e k) t ->
    forall a, eqit_secure Label priv RR true true l (k a) t.
Proof.
  intros. generalize dependent t. rename H into Hunpriv. generalize dependent a.
  intros. punfold H0. red in H0. cbn in *. pfold. red.
  remember (VisF e k) as x. genobs_clear t ot.
  hinduction H0 before l; intros; try inv Heqx; 
  ITrace.inj_existT; subst; try contradiction;  auto.
  - constructor; auto. eapply IHsecure_eqitF; eauto.
  - pclearbot. constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse. pclearbot. apply H.
  - unpriv_ind. eapply H0; eauto.
Qed.


(* reformat this lemma? useful but unclear *)
Lemma eses_aux1: forall (E : Type -> Type) (R2 R1 : Type) (Label : Preorder)
                    (priv : forall A : Type, E A -> L) (l : L) (RR : R1 -> R2 -> Prop)
                    (r : itree E R1 -> itree E R2 -> Prop) (m1 m2 : itree E R1),
              m1 ≈ m2 ->
               (forall (t1 t1' : itree E R1) (t2 : itree E R2),
                   t1 ≈ t1' -> eqit_secure Label priv RR true true l t1 t2 -> r t1' t2) ->
               forall (X : Type) (e : E X) (k : X -> itree E R2),
                 secure_eqitF Label priv RR true true l id
                              (upaco2 (secure_eqit_ Label priv RR true true l id) bot2) (observe m1) 
                              (VisF e k) ->
                 leq (priv X e) l ->
                 secure_eqitF Label priv RR true true l id
                              (upaco2 (secure_eqit_ Label priv RR true true l id) r) (observe m2) 
                              (VisF e k).
Proof.
  intros E R2 R1 Label priv l RR r m1 m2 REL CIH X e k Hsec SECCHECK.
  remember (VisF e k) as x. punfold REL. red in REL. rewrite Heqx.
  hinduction Hsec before r; intros; try inv Heqx; ITrace.inj_existT; subst; try contradiction; auto. 
  - eapply IHHsec; eauto.
    pstep_reverse. setoid_rewrite <- tau_eutt at 1. pfold. auto.
  - pclearbot. remember (VisF e0 k1) as y.
    hinduction REL before r; intros; try inv Heqy; ITrace.inj_existT; subst; auto.
    + constructor; auto. right. eapply CIH; eauto; try apply H.
      pclearbot. apply REL.
    + constructor; eauto.
  - rewrite H2. remember (VisF e k1) as y.
    hinduction REL before r; intros; try inv Heqy; ITrace.inj_existT; subst; auto.
    + pclearbot. rewrite <- H2. unpriv_ind. rewrite H2. eapply H0; eauto.
      Unshelve. all: auto. pstep_reverse.
    + constructor; auto. eapply IHREL; eauto.
Qed.

Lemma eses_aux2:
forall (E : Type -> Type) (R2 R1 : Type) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (RR : R1 -> R2 -> Prop)
    (r : itree E R1 -> itree E R2 -> Prop) (m1 m2 : itree E R1) (r0 : R2),
  m1 ≈ m2 ->
  secure_eqitF Label priv RR true true l id
    (upaco2 (secure_eqit_ Label priv RR true true l id) bot2) (observe m1) 
    (RetF r0) ->
  secure_eqitF Label priv RR true true l id
    (upaco2 (secure_eqit_ Label priv RR true true l id) r) (observe m2) 
    (RetF r0).
Proof.
  intros E R2 R1 Label priv l RR r m1 m2 r0 Heutt Hsec.
  punfold Heutt. red in Heutt. remember (RetF r0) as x.
  rewrite Heqx. hinduction Hsec before r; intros; inv Heqx; auto.
  - remember (RetF r1) as y.
    hinduction Heutt before r; intros; inv Heqy; auto.
    constructor; auto. eapply IHHeutt; eauto.
  - eapply IHHsec; eauto. pstep_reverse. rewrite <- tau_eutt at 1. pfold. auto.
  - remember (VisF e k1) as y. 
    hinduction Heutt before r; intros; inv Heqy; ITrace.inj_existT; subst; auto.
    +  unpriv_ind. rewrite H2. eapply H0; eauto. 
       pclearbot. pstep_reverse.
    + constructor; auto. eapply IHHeutt; eauto.
Qed.

Lemma eutt_secure_eqit_secure : forall E Label priv l R1 R2 RR (t1 t1': itree E R1) (t2 : itree E R2),
    t1 ≈ t1' -> eqit_secure Label priv RR true true l t1 t2 ->
    eqit_secure Label priv RR true true l t1' t2.
Proof.
  intros E Label priv l R1 R2 RR. pcofix CIH. intros t1 t1' t2 Heutt Hsec.
  punfold Heutt. red in Heutt. punfold Hsec. red in Hsec.
  pfold. red. hinduction Heutt before r; intros; subst; auto.
  - remember (RetF r2) as x. hinduction Hsec before r; intros; try inv Heqx; auto.
    + constructor; auto. eapply IHHsec; eauto.
    + unpriv_ind. eapply H0; eauto.
  - genobs_clear t2 ot2. 
    assert (Ht2 : (exists m3, ot2 = TauF m3) \/ (forall m3, ot2 <> TauF m3) ).
    { destruct ot2; eauto; right; repeat intro; discriminate. }
    (* because of the extra inductive cases this is not enough *)
    destruct Ht2 as [ [m3 Hm3] | Ht2 ].
    + subst. pclearbot. constructor. right. eapply CIH; eauto.
      apply tau_eqit_secure. apply eqit_secure_sym. apply tau_eqit_secure.
      apply eqit_secure_sym. pfold. auto.
    + destruct ot2; try (exfalso; eapply Ht2; eauto; fail).
      * pclearbot. rewrite itree_eta' at 1. eapply eses_aux2 with (m1 := Tau m1); eauto. 
        do 2 rewrite tau_eutt. auto.
      * assert (leq (priv _ e) l \/ ~ leq (priv _ e) l).
        { apply classic. }
        destruct H as [SECCHECK | SECCHECK].
        ++ pclearbot. rewrite itree_eta' at 1. apply eses_aux1 with (m1 := Tau m1); auto.
           do 2 rewrite tau_eutt. auto.
        ++ pclearbot.
           unpriv_co. pclearbot. right. eapply CIH. apply REL. 
           apply tau_eqit_secure. 
           apply eqit_secure_sym.
           eapply unpriv_e_eqit_secure; eauto.
           apply eqit_secure_sym. pfold. auto.
  - pclearbot. rewrite itree_eta' at 1. pstep_reverse.
    assert (eqit_secure Label priv RR true true l (Vis e k1) t2 ).
    { pfold; auto. }
    clear Hsec. rename H into Hsec.
    destruct (classic (leq (priv _ e) l ) ).
    + pstep. red. punfold Hsec. red in Hsec.
      cbn in *. remember (VisF e k1) as x. 
      hinduction Hsec before r; intros; inv Heqx; ITrace.inj_existT; subst; try contradiction; auto.
      * constructor; auto. eapply IHHsec; eauto.
      * constructor; auto; intros. right. eapply CIH; try apply REL. pclearbot. apply H.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + punfold Hsec. red in Hsec. pfold. red.
      cbn in *. (* if its a Tau or a invisible event we are fine*)
      destruct (observe t2).
      * inv Hsec. ITrace.inj_existT. subst. unpriv_ind. rewrite H4. rewrite H4 in H1.
        eapply eses_aux2; eauto. apply REL.
      * unpriv_co. right. eapply CIH; try apply REL.
        eapply unpriv_e_eqit_secure; eauto. apply eqit_secure_sym.
        apply tau_eqit_secure. apply eqit_secure_sym. pfold. auto.
      * destruct (classic (leq (priv _ e0) l ) ).
        -- rewrite itree_eta'. unpriv_ind; auto. 
           inv Hsec; intros; ITrace.inj_existT; subst; try contradiction. cbn.
           rewrite H5. rewrite H5 in H2. eapply eses_aux1; eauto. apply REL.
        -- unpriv_co; auto. right. eapply CIH; try apply REL.
           do 2 (eapply unpriv_e_eqit_secure; eauto; apply eqit_secure_sym).
           pfold. auto.
  - eapply IHHeutt; eauto. (* hoist to lemma? *) remember (TauF t0) as x.
    hinduction Hsec before r;  intros; try inv Heqx; auto.
    + constructor; auto. pclearbot. pstep_reverse.
    + constructor; auto. eapply IHHsec; eauto.
    + pclearbot. unpriv_ind; auto. pstep_reverse.
    + pclearbot. unpriv_ind. eapply H0; eauto.
Qed.
