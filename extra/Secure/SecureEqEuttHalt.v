From Stdlib Require Import Morphisms.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.Labels
     Secure.SecureEqHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma tau_eqit_secure : forall E R1 R2 Label priv l RR (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR true true l (Tau t1) t2 -> eqit_secure Label priv RR true true l t1 t2.
Proof.
  intros E R1 R2 Label priv l RR.  intros t1 t2 Hsec. pstep. red.
  step in Hsec. red in Hsec. cbn in *. remember (TauF t1) as x.
  hinduction Hsec before priv; intros;  inv Heqx;  try inv CHECK; auto with itree.
  - constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse.
  - step in H.
Qed.

Lemma unpriv_e_eqit_secure : forall E A R1 R2 Label priv l RR (e : E A) (k : A -> itree E R1)
      (t : itree E R2),
    (~leq (priv A e) l ) ->
    eqit_secure Label priv RR true true l (Vis e k) t ->
    forall a, eqit_secure Label priv RR true true l (k a) t.
Proof.
  intros. generalize dependent t. rename H into Hunpriv. generalize dependent a.
  intros. step in H0. red in H0. cbn in *. step. red.
  remember (VisF e k) as x. genobs_clear t ot.
  hinduction H0 before l; intros; try inv Heqx;
    ddestruction; subst; try contradiction; try contra_size; auto.
  - constructor; auto. eapply IHsecure_eqitF; eauto.
  -  constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse.  apply H.
  - unpriv_ind. eapply H0; eauto.
  -  rewrite itree_eta'. pstep_reverse.
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
  remember (VisF e k) as x. step in REL. red in REL. rewrite Heqx.
  hinduction Hsec before r; intros; try inv Heqx; ddestruction; subst; try contradiction; auto.
  - eapply IHHsec; eauto.
    pstep_reverse. setoid_rewrite <- tau_eutt at 1. step. auto.
  -  remember (VisF e0 k1) as y.
    hinduction REL before r; intros; try inv Heqy; ddestruction; subst; auto.
    + constructor; auto. right. eapply CIH; eauto; try apply H.
       apply REL.
    + constructor; eauto.
  - rewrite H2. remember (VisF e k1) as y.
    hinduction REL before r; intros; try inv Heqy; ddestruction; subst; auto.
    +  rewrite <- H2. unpriv_ind. rewrite H2. eapply H0; eauto.
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
  step in Heutt. red in Heutt. remember (RetF r0) as x.
  rewrite Heqx. hinduction Hsec before r; intros; inv Heqx; auto with itree.
  - remember (RetF r1) as y.
    hinduction Heutt before r; intros; inv Heqy; auto with itree.
    constructor; auto. eapply IHHeutt; eauto.
  - eapply IHHsec; eauto. pstep_reverse. rewrite <- tau_eutt at 1. step. auto.
  - remember (VisF e k1) as y.
    hinduction Heutt before r; intros; inv Heqy; ddestruction; subst; auto.
    +  unpriv_ind. rewrite H2. eapply H0; eauto.
        pstep_reverse.
    + constructor; auto. eapply IHHeutt; eauto.
Qed.

Definition classic_empty := Secure.Labels.classic_empty.

(*tomorrow start on the transitivity proof *)
Lemma eutt_secure_eqit_secure : forall E Label priv l R1 R2 RR (t1 t1': itree E R1) (t2 : itree E R2),
    t1 ≈ t1' -> eqit_secure Label priv RR true true l t1 t2 ->
    eqit_secure Label priv RR true true l t1' t2.
Proof.
  intros E Label priv l R1 R2 RR. coinduction c CIH. intros t1 t1' t2 Heutt Hsec.
  step in Heutt. red in Heutt. step in Hsec. red in Hsec.
  step. hinduction Heutt before r; intros; subst; auto with itree.
  - remember (RetF r2) as x. hinduction Hsec before r; intros; try inv Heqx; auto with itree.
    + constructor; auto. eapply IHHsec; eauto.
    + unpriv_ind. eapply H0; eauto.
  - genobs_clear t2 ot2.
    assert (Ht2 : (exists m3, ot2 = TauF m3) \/ (forall m3, ot2 <> TauF m3) ).
    { destruct ot2; eauto; right; repeat intro; discriminate. }
    (* because of the extra inductive cases this is not enough *)
    destruct Ht2 as [ [m3 Hm3] | Ht2 ].
    + subst.  constructor. right. eapply CIH; eauto.
      apply tau_eqit_secure. apply eqit_secure_sym. apply tau_eqit_secure.
      apply eqit_secure_sym. step. auto.
    + destruct ot2; try (exfalso; eapply Ht2; eauto; fail).
      *  rewrite itree_eta' at 1. eapply eses_aux2 with (m1 := Tau m1); eauto.
        do 2 rewrite tau_eutt. auto.
      * assert (leq (priv _ e) l \/ ~ leq (priv _ e) l).
        { apply classic. }
        destruct H as [SECCHECK | SECCHECK]; destruct ( classic_empty X  ).
        ++  rewrite itree_eta' at 1. apply eses_aux1 with (m1 := Tau m1); auto.
           do 2 rewrite tau_eutt. auto.
        ++  rewrite itree_eta' at 1. apply eses_aux1 with (m1 := Tau m1); auto.
           do 2 rewrite tau_eutt. auto.
        ++ unpriv_halt.  right. eapply CIH; eauto.
           apply tau_eqit_secure. step. auto.
        ++ 
           unpriv_co.  eapply CIH.  apply REL.
           apply tau_eqit_secure.
           apply eqit_secure_sym.
           eapply unpriv_e_eqit_secure; eauto.
           apply eqit_secure_sym. step. auto.
  -  rewrite itree_eta' at 1. pstep_reverse.
    assert (eqit_secure Label priv RR true true l (Vis e k1) t2 ).
    { step; auto. }
    clear Hsec. rename H into Hsec.
    destruct (classic (leq (priv _ e) l ) ).
    + pstep. step in Hsec. red in Hsec.
      cbn in *. remember (VisF e k1) as x.
      hinduction Hsec before r; intros; inv Heqx; ddestruction; subst; try contradiction; auto.
      * constructor; auto. eapply IHHsec; eauto.
      * constructor; auto; intros. right. eapply CIH; try apply REL.  apply H.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + destruct (classic_empty u).
      * step. cbn.  step in Hsec. red in Hsec. cbn in *.
        destruct (observe t2).
        -- inv Hsec; contra_size.
        -- unpriv_halt. right. apply CIH with (t1 := Vis e k1).
           ++ step. constructor. left. auto.
           ++ inv Hsec; ddestruction; subst; try contradiction;  try contra_size. step. auto.
               auto.
        -- inv Hsec; ddestruction; subst; try contradiction; try contra_size.
           ++ unpriv_halt. right. apply CIH with (t1 := Vis e k1).
              { step. constructor. red. auto. }
              { rewrite H1 in H3. step. apply H3. }
           ++  unpriv_halt. right. apply CIH with (t1 := Vis e k1).
              { step. constructor. red. auto. }
              { apply H2. }
           ++  unpriv_halt. contra_size.
      * step. cbn.  step in Hsec. red in Hsec. cbn in *.
        destruct (observe t2).
        ++ rewrite itree_eta' at 1. rewrite itree_eta' in Hsec at 1.
           eapply eses_aux2; eauto. step. constructor. red. auto.
        ++ unpriv_co. right. apply CIH with (t1 := k1 a); try apply REL.
           eapply unpriv_e_eqit_secure; eauto. apply eqit_secure_sym.
           apply tau_eqit_secure. apply eqit_secure_sym. step. auto.
        ++ destruct (classic (leq (priv _ e0) l )).
           ** rewrite itree_eta' at 1.
              eapply eses_aux1 with (m1 := Vis e k1); eauto.
              step. constructor. red. auto.
           ** destruct (classic_empty X).
              --- unpriv_halt. right. eapply CIH; try apply REL.
                  eapply unpriv_e_eqit_secure; eauto. step. auto.
              --- unpriv_co. right. eapply CIH; try apply REL.
                  (* eapply unpriv_e_eqit_secure; eauto. *)
                  do 2 (eapply unpriv_e_eqit_secure; eauto; apply eqit_secure_sym).
                  step. auto.
  - eapply IHHeutt; eauto. pstep_reverse.
    apply tau_eqit_secure. step. auto.
Qed.


Lemma eqit_secure_TauLR :
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (t0 : itree E R2)
    (t4 : itree E R3),
    eqit_secure Label priv RR2 b1 b2 l (Tau t0) (Tau t4) ->
    eqit_secure Label priv RR2 b1 b2 l t0 t4.
Proof.
  intros E R3 Label priv l b1 b2 R2 RR2.
  intros. step in H. red in H. cbn in *. pstep. red.
  remember (TauF t0) as x. remember (TauF t4) as y.
  hinduction H before b2; intros;  try discriminate.
  - inv Heqx; inv Heqy.  pstep_reverse.
  - inv Heqx. inv H; eauto with itree.
    +  unpriv_ind. pstep_reverse.
    + unpriv_ind. rewrite H1 in H2.
      specialize (H2 a). genobs (k1 a) ok1. clear Heqok1.
      remember (TauF t4) as y.
      hinduction H2 before b2; intros; inv Heqy; try inv CHECK; eauto with itree.
      *  constructor; auto; pstep_reverse.
      *  unpriv_ind. pstep_reverse.
      *  step in H.
    +  step in H2.
  - inv Heqy. inv H; eauto with itree.
    +  unpriv_ind. pstep_reverse.
    + rewrite H0 in H2. unpriv_ind. specialize (H2 a).
      genobs (k2 a) ok2. clear Heqok2.
      remember (TauF t0) as y.
      hinduction H2 before b2; intros; inv Heqy; try inv CHECK; eauto with itree.
      *  constructor; auto. pstep_reverse.
      * unpriv_ind.  pstep_reverse.
      *  step in H.
    +  step in H2.
Qed.

Lemma eqit_secure_TauLVisR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop),
    forall (t3 : itree E R2) (X : Type) (e : E X) (k : X -> itree E R3) (a : X),
      (~ leq (priv _ e) l) ->
      eqit_secure Label priv RR2 b1 b2 l (Tau t3) (Vis e k) ->
      eqit_secure Label priv RR2 b1 b2 l t3 (k a).
Proof.
  intros E R3 Label priv l b1 b2 R2 RR t3 A e k a He Hsec.
  step in Hsec. red in Hsec. cbn in *.
  remember (TauF t3) as x. remember (VisF e k) as y.
  hinduction Hsec before b2; intros; try discriminate.
  - inv Heqx. inv CHECK.
    remember (VisF e k) as y. step. clear IHHsec.
    hinduction Hsec before b2; intros; inv Heqy; ddestruction;  subst;
    try contradiction; try contra_size; eauto with itree.
    + constructor; auto.  pstep_reverse.
    + unpriv_ind.  pstep_reverse.
    +  specialize (H a). step in H.
  - inv Heqx. inv Heqy. ddestruction; subst.  apply H.
  - inv Heqx. inv Heqy. ddestruction; subst. rewrite H2 in H.
    clear H0. clear H2 t1. remember (TauF t3) as x.
    step. specialize (H a).
    hinduction H before b2; intros; inv Heqx; try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  step in H.
  -   inv Heqx. inv Heqy. ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_TauRVisL:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) RR2,
    forall (t3 : itree E R2) (X : Type) (e : E X) (k : X -> itree E R3) (a : X),
      (~ leq (priv _ e) l) ->
      eqit_secure Label priv RR2 b1 b2 l (Vis e k) (Tau t3)->
      eqit_secure Label priv RR2 b1 b2 l (k a) t3.
Proof.
  intros E R3 Label priv l b1 b2 R2 RR t3 A e k a He Hsec.
  step in Hsec. red in Hsec. cbn in *.
  remember (TauF t3) as x. remember (VisF e k) as y.
  hinduction Hsec before b2; intros; try discriminate.
  - inv Heqx. inv CHECK. remember (VisF e k) as y. step. clear IHHsec.
    hinduction Hsec before b1; intros; inv Heqy; ddestruction; subst;
    try contradiction; eauto with itree.
    + constructor; auto with itree.  pstep_reverse.
    + unpriv_ind.  pstep_reverse.
    + contra_size.
    + contra_size.
    +  specialize (H a). step in H.
  - inv Heqx. inv Heqy. ddestruction; subst.  apply H.
  - inv Heqx. inv Heqy. ddestruction; subst.  rewrite H2 in H. inv CHECK.
    specialize (H a). step. remember (TauF t3) as y.
    hinduction H before b2; intros; inv Heqy; try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  step in H.
  - inv Heqx. inv Heqy. ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_VisLR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2),
    ~ leq (priv A e) l ->
    forall (X : Type) (e0 : E X) (k : X -> itree E R3) (a : A),
      ~ leq (priv X e0) l ->
      forall a0 : X,
        eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) ->
        eqit_secure Label priv RR2 b1 b2 l (k2 a) (k a0).
Proof.
  intros E R3 Label priv l b1 b2 R2 RR2 A e k2 SECCHECK X e0 k a H0 a0 H1.
  step. red.
  step in H1. red in H1. cbn in *. remember (VisF e k2) as x.
  remember (VisF e0 k) as y.
  hinduction H1 before l; intros; try discriminate.
  - inv Heqx. inv Heqy. ddestruction; subst. contradiction.
  -  inv Heqx. inv Heqy. ddestruction; subst. pstep_reverse.
  - inv Heqx. ddestruction; subst. inv CHECK. clear H0.
    specialize (H a).
    rewrite Heqy in H. clear Heqy. remember (VisF e1 k) as y.
    hinduction H before l; intros; inv Heqy; ddestruction; subst; try contradiction;
    try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    + unpriv_ind.  pstep_reverse.
    +  specialize (H a0). step in H.

  - inv Heqy.  ddestruction; subst. inv CHECK. clear H0.
    rewrite Heqx in H. specialize (H a0).
    remember (VisF e0 k0) as y.
    hinduction H before b1; intros; inv Heqy; ddestruction; subst; try contradiction;
    try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  specialize (H a). step in H.
  - inv Heqx; inv Heqy; ddestruction; subst. contra_size.
  - inv Heqx; inv Heqy; ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_private_VisLR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2),
    nonempty A ->
    ~ leq (priv A e) l ->
    forall (X : Type) (e0 : E X) (k : X -> itree E R3),
      ~ leq (priv X e0) l ->
      nonempty X ->
      (forall a a0,
        eqit_secure Label priv RR2 b1 b2 l (k2 a) (k a0)) ->
        eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) .
Proof.
  intros. step. cbn. unpriv_co. left. apply H3.
Qed.

Lemma eqit_secure_private_VisL:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2) (t : itree E R3),
    nonempty A ->
    ~ leq (priv A e) l ->
    (forall a,
        eqit_secure Label priv RR2 true b2 l (k2 a) t) ->
        eqit_secure Label priv RR2 true b2 l (Vis e k2) t .
Proof.
  intros. step. cbn. unpriv_ind. pstep_reverse. apply H1.
Qed.

Lemma eqit_secure_private_VisR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R3) (t : itree E R2),
    nonempty A ->
    ~ leq (priv A e) l ->
    (forall a,
        eqit_secure Label priv RR2 b1 true l t (k2 a)) ->
        eqit_secure Label priv RR2 b1 true l t (Vis e k2).
Proof.
  intros. step. cbn. unpriv_ind. pstep_reverse. apply H1.
Qed.

Lemma eqit_secure_public_Vis :  forall (E : Type -> Type) (R1 R2 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (RR : R1 -> R2 -> Prop) (A : Type)
    (e : E A) (k1: A -> itree E R1) (k2 : A -> itree E R2),
    leq (priv A e) l ->
    (eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2) <->
    forall a, eqit_secure Label priv RR b1 b2 l (k1 a) (k2 a)).
Proof.
  split; intros.
  - sinv H0; ddestruction; subst; try contradiction; apply H2.
  - step. constructor; auto. left. apply H0.
Qed.

Lemma eqit_secure_trans_aux1:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall x : Type, E x -> L) (l : L) (b2 : bool) (R2 : Type)
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (r0 : R3) (t4 : itree E R2),
    secure_eqitF Label priv RR2 true b2 l id
                 (upaco2 (secure_eqit_ Label priv RR2 true b2 l id) bot2) (observe t4)
                 (RetF r0) ->
    forall t : itree E R1,
      paco2 (secure_eqit_ Label priv RR1 true b2 l id) bot2 t t4 ->
      secure_eqitF Label priv (rcompose RR1 RR2) true b2 l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true b2 l id) r)
                   (observe t) (RetF r0).
Proof.
  intros E R3 R1 Label priv l b2 R2 RR1 RR2 r r0 t4 Ht23 t H.
  step in H. red in H.
  remember (RetF r0) as x.
  hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; auto.
  - remember (RetF r1) as y.
    hinduction H0 before r; intros; inv Heqy; eauto with itree.
    rewrite itree_eta'. unpriv_ind. cbn. eapply H0; eauto.
  - eapply IHHt23; eauto.
    remember (TauF t1) as y.
    hinduction H before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  step in H.
  - assert (Hne : nonempty A). { eauto. } (* add the condition that lets us assume this*)
    inv Hne. eapply (H0 a); eauto.
    remember (VisF e k1) as y.
    hinduction H1 before r; intros; inv Heqy; try inv CHECK; ddestruction; subst;
    try contradiction; try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  rewrite itree_eta' at 1. pstep_reverse.
Qed.

Lemma eqit_secure_trans_aux2:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall x : Type, E x -> L) (l : L) (b2 : bool) (R2 : Type)
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (X : Type) (e0 : E X) (k : X -> itree E R3) (t4 : itree E R2),
    leq (priv X e0) l ->
    secure_eqitF Label priv RR2 true b2 l id
                 (upaco2 (secure_eqit_ Label priv RR2 true b2 l id) bot2) (observe t4)
                 (VisF e0 k) ->
    (forall (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
        eqit_secure Label priv RR1 true b2 l t1 t2 ->
        eqit_secure Label priv RR2 true b2 l t2 t3 -> r t1 t3) ->
    forall t : itree E R1,
      paco2 (secure_eqit_ Label priv RR1 true b2 l id) bot2 t t4 ->
      secure_eqitF Label priv (rcompose RR1 RR2) true b2 l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true b2 l id) r)
                   (observe t) (VisF e0 k).
Proof.
  intros E R3 R1 Label priv l b2 R2 RR1 RR2 r X e0 k t4 He0 Ht23 CIH0 t Ht.
  step in Ht. red in Ht. remember (VisF e0 k) as x.
  hinduction Ht23 before r; intros; inv Heqx; try inv CHECK;
  ddestruction; subst; try contradiction; eauto.
  - eapply IHHt23; eauto. clear IHHt23. remember (TauF t1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  step in H.
  -  remember (VisF e0 k1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK;
    ddestruction; subst; try contradiction; eauto with itree.
    +  constructor; auto. right. eapply CIH0. apply H.
      apply H0.
    + rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
  - assert (nonempty A); eauto. inv H1. eapply H0; eauto.
    Unshelve. all : auto. clear H0. rewrite H2 in H.
    remember (VisF e k1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK; ddestruction; subst;
    try contradiction; try contra_size; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  rewrite itree_eta' at 1. pstep_reverse.

Qed.


Lemma secret_halt_trans_1 : forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) t1 (e : E A) k t3,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l t1 (Vis e k) ->
    eqit_secure Label priv RR2 b1 b2 l (Vis e k) t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 A RR1 RR2 t1 e k t3 He HA.
  generalize dependent t3. generalize dependent t1.
  coinduction c CIH. intros t1 t3 Ht1 Ht3.
  step. step in Ht1. red in Ht1. step in Ht3. red in Ht3.
  cbn in *.
  remember (VisF e k) as x.
  hinduction Ht1 before r; intros; inv Heqx; ddestruction; subst;
  try contradiction; try contra_size; eauto with itree.
  -  inv Ht3; ddestruction; subst; try contradiction; try contra_size.
    + constructor. right. apply CIH; auto. step. auto.
    + unpriv_co; auto. right. apply CIH; auto. step. rewrite H0 in H2. apply H2.
    +  constructor. right. apply CIH; auto.
    +  destruct (classic_empty B).
      * unpriv_halt. right. apply CIH; auto with itree. step.
        red. cbn. unpriv_halt.
      * unpriv_co. right. apply CIH; auto. apply H1.
    +  unpriv_halt. right. apply CIH; auto. step.
      red. cbn. unpriv_halt. contra_size.
  -   inv Ht3; ddestruction; subst; try contradiction; try contra_size.
    + unpriv_halt. right. apply CIH; auto.
      * step. cbn. unpriv_halt.
      * step. auto.
    + unpriv_halt. right. apply CIH; auto.
      * step. cbn. unpriv_halt.
      * step. auto. rewrite H0 in H2. apply H2.
    +  unpriv_halt. right. apply CIH; auto.
      step. cbn. unpriv_halt.
    +  unpriv_halt. right. apply CIH.
      * step. cbn. unpriv_halt.
      * apply H1.
    + unpriv_halt. contra_size.
  -  inv Ht3; ddestruction; subst; try contradiction; try contra_size;
    destruct (classic_empty A0).
    + unpriv_halt. right. apply CIH; auto.
      * step. cbn. unpriv_halt. contra_size.
      * step. auto.
    + unpriv_co. right. apply CIH; auto; try apply H.
      step. auto.
    + unpriv_halt. right. apply CIH; auto.
      * step. cbn. unpriv_halt. contra_size.
      * step. rewrite H0 in H2. apply H2.
    + unpriv_co. right. apply CIH. apply H. rewrite H0 in H2.
      step. apply H2.
    +  unpriv_halt. right. apply CIH; auto. step.
      red. cbn. unpriv_halt. contra_size.
    +  unpriv_co. right. apply CIH; auto. apply H.
    + unpriv_halt.  right. apply CIH; try apply H1.
      step. cbn. unpriv_halt. contra_size.
    +  destruct (classic_empty B).
      * unpriv_halt. right. apply CIH; auto. apply H.
        step. cbn. unpriv_halt.
      * unpriv_co. right. apply CIH; eauto. apply H. apply H1.
    +  unpriv_halt. contra_size.
    +  unpriv_halt. right. apply CIH; auto. apply H.
      step. cbn. unpriv_halt. contra_size.
Qed.

Lemma secret_halt_trans_2 :  forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) (e : E A) k t2 t3,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l (Vis e k) t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l (Vis e k) t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 A RR1 RR2 e k t2 t3 He HA.
  generalize dependent t3. generalize dependent t2.
  coinduction c CIH. intros t2 t3 Ht2 Ht23. step.
  red. cbn. step in Ht2. step in Ht23. red in Ht2. red in Ht23.
  cbn in *.
  hinduction Ht23 before r; intros; eauto with itree.
  - inv Ht2. ddestruction; subst. contra_size.
  - unpriv_halt. right.  eapply CIH; eauto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;   eauto.
    step. auto.
  - eapply IHHt23; eauto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
    step in H0.
  - 
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
  - unpriv_halt.   inv SIZECHECK. right. eapply CIH; try apply H.
    Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
    + step. apply H2.
    + apply H1.
  -  unpriv_halt. right. eapply CIH; try apply H.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
    step. auto.
  -  unpriv_halt. inv SIZECHECK1. inv SIZECHECK2. right. eapply CIH; try apply H.
    Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
    + step. apply H2.
    + apply H1.
  - inv SIZECHECK.  eapply H0; eauto. Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction;  eauto.
    rewrite itree_eta' at 1. pstep_reverse.
  - unpriv_halt. right. eapply CIH; eauto. step. apply Ht2.
    step. apply H.
  -  unpriv_halt. right. eapply CIH; eauto. step. auto.
  - unpriv_halt. contra_size.
  - unpriv_halt. right.  eapply CIH with (t2 := Vis e1 k1); eauto.
    + step. auto.
    + apply H.
  - unpriv_halt. contra_size.
Qed.

Lemma eqit_secure_RR_imp : forall E b1 b2 R1 R2 (RR1 RR2 : R1 -> R2 -> Prop) Label priv l
                (t1 : itree E R1) (t2 : itree E R2),
    RR1 <2= RR2 ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1.
  coinduction c CIH. intros t1 t2 Ht12. step. red.
  step in Ht12. red in Ht12.
  hinduction Ht12 before r; intros; eauto;
  try ( constructor; auto; right; eapply CIH; eauto; fail);
  try ( unpriv_co; right; eapply CIH; eauto; apply H0; fail).
   constructor; auto. right. eapply CIH; eauto. apply H0.
  -  unpriv_halt. right. eapply CIH; eauto. apply H0.
  -  unpriv_halt. right. eapply CIH; eauto. apply H0.
Qed.

Lemma secret_halt_trans_3 :  forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop)  t1 t2 (e : E A) k,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 (Vis e k) ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 (Vis e k).
Proof.
  intros. apply eqit_secure_sym in H1. apply eqit_secure_sym in H2.
  apply eqit_secure_sym. eapply secret_halt_trans_2 in H1; eauto.
  eapply eqit_secure_RR_imp; eauto.
  intros. inv PR. econstructor; eauto.
Qed.

Lemma eqit_secure_trans : forall E Label priv l b1 b2 (R1 R2 R3 : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 RR1 RR2.
  coinduction c CIH0. intros t1 t2 t3 Ht12 Ht23.
  step in Ht12. red in Ht12. step in Ht23. red in Ht23. step. red.
  hinduction Ht12 before r; intros; try inv CHECK; auto with itree.
  - remember (RetF r2) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  -  genobs t4 ot4.
    assert ( (exists t5, ot4 = TauF t5) \/ (forall t5, ot4 <> TauF t5) ).
    { destruct ot4; eauto; right; intros; discriminate. }
    destruct H0 as [ [t5 Ht4] | Ht4].
    + subst. rewrite Ht4. rewrite Ht4 in Ht23. constructor.
      right. eapply CIH0; eauto. eapply eqit_secure_TauLR. step.
      auto.
    + destruct ot4; try (exfalso; eapply Ht4;  eauto; fail  ).
      * inv Ht23. inv CHECK. rewrite itree_eta' at 1.
        assert (eqit_secure Label priv (rcompose RR1 RR2) true b2 l (Tau t0) (Ret r0)  ).
        { step. cbn. rewrite itree_eta' at 1. eapply eqit_secure_trans_aux1; eauto.
          step. constructor; auto. pstep_reverse. }
        rewrite itree_eta'. pstep_reverse. eapply paco2_mon; eauto.
        intros; contradiction.
      * destruct (classic (leq (priv _ e) l ) ).
        -- inv Ht23; ddestruction; subst; try contradiction; try inv CHECK.
           constructor; auto. eapply eqit_secure_trans_aux2; eauto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. rewrite itree_eta' at 1.
              pstep_reverse.
              eapply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3 with (t2 := Tau t3); eauto.
              ** step. constructor. left. auto.
              ** step. auto.
           ++ unpriv_co. right. eapply CIH0; eauto.
              assert (eqit_secure Label priv RR2 b1 b2 l (Tau t3) (Vis e k)).
              step. auto. eapply eqit_secure_TauLVisR; eauto.
  - apply IHHt12; auto.
    remember (TauF t0) as y.
    hinduction Ht23 before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    +  constructor; auto. pstep_reverse.
    +  unpriv_ind. pstep_reverse.
    +  step in H.
  -  remember (VisF e k2) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; ddestruction; subst;
    try contradiction; eauto with itree.
    +  constructor; auto. intros. right. eapply CIH0; eauto; try apply H0.
      apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  -  remember (TauF t0) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; auto.
    +  unpriv_co. right. eapply CIH0; try apply H0.
      auto.
    + destruct ot2.
      * clear IHHt23. rewrite itree_eta'. unpriv_ind.
        remember (k1 a) as t. specialize (H a). setoid_rewrite <- Heqt in H.
        clear Heqt a k1. cbn. eapply eqit_secure_trans_aux1; eauto.
      * unpriv_co. right. eapply CIH0; try apply H.
        clear IHHt23. remember (TauF t) as y.
        step. red.
        hinduction Ht23 before r; intros; inv Heqy; try inv CHECK; eauto with itree.
        --  constructor; auto. pstep_reverse.
        --  unpriv_ind. pstep_reverse.
        --  step in H.
      * destruct (classic (leq (priv _ e0) l ) ).
        -- rewrite itree_eta'. unpriv_ind. cbn.
           clear IHHt23. remember (k1 a) as t. specialize (H a). setoid_rewrite <- Heqt in H.
           clear Heqt a k1. eapply eqit_secure_trans_aux2; eauto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. unpriv_ind.
              pstep_reverse. apply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3; eauto. apply H.
              step. auto.
           ++ unpriv_co. right. eapply CIH0. apply H.
              clear IHHt23. pstep. remember (VisF e0 k) as y.
              hinduction Ht23 before r; intros; inv Heqy; try inv CHECK;
                ddestruction; subst; try contradiction; try contra_size; eauto with itree.
              **  constructor; auto. pstep_reverse.
              ** unpriv_ind.  pstep_reverse.
              **  rewrite itree_eta' at 1. pstep_reverse.
    + constructor; auto. eapply IHHt23; eauto.
    +  unpriv_co. right. eapply CIH0; try apply H0. apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + unpriv_halt. right.  eapply CIH0; eauto. apply H0.
  - 
    genobs_clear t3 ot3.
    assert (Hne : nonempty A); eauto. inv Hne.
    assert ( (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4) ).
    { destruct ot3; eauto; right; intros; discriminate. }
    destruct H0 as [ [t4 Ht3] | Ht3].
    + subst. constructor. right. eapply CIH0; try apply H.
      Unshelve. all: auto.
      eapply eqit_secure_TauRVisL; eauto. step. auto.
       (* should be fine but new lemma, also shelved goal *)
    +
      destruct ot3; try (exfalso; eapply Ht4;  eauto; fail  ).
      * inv Ht23; inv CHECK. ddestruction. subst. clear CIH0.
        constructor; auto. rewrite H4. eapply eqit_secure_trans_aux1; eauto.
        rewrite <- H4. apply H1. Unshelve. auto. (* shelved goal*)
      * constructor. right. eapply CIH0; try apply H.
        eapply eqit_secure_TauRVisL; eauto. step. auto.
        (* same goal as last admit *)
      * destruct (classic (leq (priv _ e0) l ) ).
        -- inv Ht23; try inv CHECK; ddestruction; subst; try contradiction.
           constructor; auto. rewrite H5. eapply eqit_secure_trans_aux2; eauto.
           rewrite <- H5. apply H2. Unshelve. all : auto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. rewrite itree_eta' at 1. pstep_reverse.
              eapply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3 with (t2 := Vis e k2); eauto.
              ** step. cbn. unpriv_co.
              ** step. auto.
           ++ unpriv_co. right. eapply CIH0; try apply H.
              Unshelve. all : auto.
              assert (eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) ).
              step. auto. eapply eqit_secure_VisLR; eauto.
  -  remember (VisF e2 k2) as x.
    (* maybe need to separate the inductive and coinductive progress cases? *)
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; try contradiction;
    try contra_size;
    ddestruction; subst; auto.
    + constructor; auto. eapply IHHt23; eauto.
    +  unpriv_co. right. eapply CIH0; try apply H0. apply H.
    +  assert (Hne : nonempty B); eauto. inv Hne.
      unpriv_co. right. eapply CIH0; eauto; try eapply H0. apply H.
      Unshelve. auto.
    +  assert (Hne : nonempty B0); eauto. inv Hne.
      unpriv_co. right. eapply CIH0; try apply H0. apply H.
      Unshelve. auto.
    + genobs t2 ot2. destruct ot2.
      * assert (Hne : nonempty B); eauto. inv Hne.
        rewrite itree_eta'. unpriv_ind. eapply eqit_secure_trans_aux1; eauto.
        Unshelve. auto.
      * assert (Hne : nonempty B); eauto. inv Hne.
        unpriv_co. right. eapply CIH0; try apply H1. Unshelve. all : auto.
        clear H0. specialize (H a). step. genobs (k2 a) ok2.
        clear Heqok2 H1 k2.
        remember (TauF t) as y.
        hinduction H before r; intros; inv Heqy; try inv CHECK; auto.
        -- constructor; auto.  pstep_reverse.
        -- constructor; eauto.
        --  unpriv_ind. pstep_reverse.
        -- unpriv_ind. eapply H0; eauto.
        --  rewrite itree_eta' at 1. pstep_reverse.
      * inv SIZECHECK2.
        destruct (classic (leq (priv _ e) l ) ).
        -- rewrite itree_eta'. unpriv_ind.
           eapply eqit_secure_trans_aux2; eauto. Unshelve. all : auto.
        -- destruct (classic_empty X).
           ++ unpriv_halt. right. eapply CIH0; eauto. apply H1.
              step. apply H. Unshelve. auto.
           ++ unpriv_co. right. eapply CIH0; try apply H1.
              Unshelve. all : auto.
              clear H0. pstep. remember (VisF e k) as y.
              specialize (H a). clear Heqot2. genobs (k2 a) ok2.
              clear Heqok2.
              hinduction H before r; intros; inv Heqy; try inv CHECK;
                ddestruction; subst; try contradiction; try contra_size; eauto with itree.
              **  constructor; auto. pstep_reverse.
              ** unpriv_ind.  pstep_reverse.
              **  rewrite itree_eta' at 1. pstep_reverse.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    +  inv SIZECHECK2. unpriv_halt. right. eapply CIH0; eauto. apply H0.
      apply H. Unshelve. auto.
  - remember (VisF e k2) as x. hinduction Ht23 before r; intros; inv Heqx; try inv CHECK;
    ddestruction; subst; try contradiction; try contra_size;  auto.
    + constructor; auto. eapply IHHt23; eauto.
    + constructor; auto.  assert (Hne : nonempty A0); eauto. inv Hne. eapply H0; eauto.
      pstep_reverse. Unshelve. auto.
    + unpriv_ind. assert (Hne : nonempty A0); eauto. inv Hne. eapply H0; eauto.
       pstep_reverse. Unshelve. auto.
    + assert (Hne : nonempty A0). { eauto. } inv Hne. eauto. Unshelve.  auto.
    + unpriv_ind. eauto.
    +  rewrite itree_eta'. pstep_reverse.
      apply paco2_mon with (r := bot2); intros; try contradiction.
      inv SIZECHECK0.
      eapply secret_halt_trans_3 with (t2 := k0 a); eauto.
      * step. apply H1.
      * apply H.
  - 
    remember (TauF t0) as y.
    hinduction Ht23 before r; intros; inv Heqy; subst; eauto with itree; 
    + unpriv_halt. right. eapply CIH0; eauto.
    + clear IHHt23. rewrite itree_eta'. rewrite itree_eta' at 1.
      pstep_reverse. apply paco2_mon with (r := bot2); intros; try contradiction.
      eapply secret_halt_trans_2; eauto. step. auto.
    + unpriv_halt. right. eapply CIH0; eauto. apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + unpriv_halt. contra_size.
  - 
    inv Ht23; ddestruction; subst; try contra_size; try contradiction;
    try inv CHECK.
    + constructor. right. eapply CIH0; eauto. step. auto.
    + unpriv_co. right. eapply CIH0; eauto. rewrite H0 in H2.
      step. apply H2.
    +  constructor. right. eapply CIH0; eauto.
    +  destruct (classic_empty B).
      * unpriv_halt. right. eapply CIH0; eauto. step. cbn. unpriv_halt.
      * unpriv_co. right. eapply CIH0; eauto. apply H1.
    +  unpriv_halt. right. eapply CIH0; eauto.
      step. cbn. unpriv_halt. contra_size.
 -  rewrite itree_eta' at 1. pstep_reverse.
   apply paco2_mon with (r := bot2); intros; try contradiction.
   eapply secret_halt_trans_2 with (t2 := Vis e2 k2); eauto.
   + step. cbn. unpriv_halt.
   + step. auto.
 -  destruct (classic_empty A).
   + inv Ht23; ddestruction; subst; try contradiction; try contra_size; try inv CHECK.
     * unpriv_halt. right. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- step. cbn. unpriv_halt. contra_size.
       -- step. auto.
     * unpriv_halt. right. rewrite H1 in H3. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- step. cbn. unpriv_halt. contra_size.
       -- step. apply H3.
     * unpriv_halt.  right. eapply CIH0; eauto.
       step. cbn. unpriv_halt. contra_size.
     * unpriv_halt.  right. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- step. cbn. unpriv_halt. contra_size.
       -- apply H2.
     * unpriv_halt. contra_size.
   + destruct (observe t3).
     * inv Ht23; ddestruction; subst; try contra_size; try contradiction.
     * unpriv_co. right. eapply CIH0; eauto. apply H.
       inv Ht23; ddestruction; subst; try contra_size; try contradiction.
       step. auto.  auto.
     * destruct (classic (leq (priv _ e) l ) ).
       { inv Ht23; ddestruction; subst; try contra_size; try contradiction. }
       destruct (classic_empty X).
       -- unpriv_halt. right. eapply CIH0; eauto. apply H. step. auto.
       -- unpriv_co. right. eapply CIH0; eauto. apply H.
          inv Ht23; ddestruction; subst; try contra_size; try contradiction.
          ++ step. apply H5.
          ++  apply H4.
Qed.


Lemma eqit_itree_eqit_secure : forall E Label priv l R1 R2 RR (t1 t1': itree E R1) (t2 : itree E R2),
    t1 ≅ t1' -> eqit_secure Label priv RR false false l t1 t2 ->
    eqit_secure Label priv RR false false l t1' t2.
Proof.
  intros E Label priv l R1 R2 RR. coinduction c CIH.
  intros t1 t1' t2 Heq Hsec. pstep. red.
  step in Heq. red in Heq. step in Hsec. red in Hsec.
  inv Heq; try inv CHECK.
  - rewrite <- H0 in Hsec. rewrite itree_eta' at 1. pstep_reverse.
    eapply paco2_mon with (r := bot2); intros; try contradiction. step.
    red. cbn. remember (RetF r2) as x. clear H H0.
    hinduction Hsec before r; intros; inv Heqx; eauto with itree.
  -  genobs t2 ot2.
    assert ( (exists t3, ot2 = TauF t3) \/ (forall t3, ot2 <> TauF t3) ).
    { destruct ot2; eauto; right; intros; discriminate. }
    destruct H1 as [ [t3 Ht2] | Ht2].
    + subst. rewrite Ht2. rewrite Ht2 in Hsec. constructor.
      right. eapply CIH; eauto. rewrite <- H0 in Hsec. inv Hsec; try inv CHECK.  auto.
    + destruct ot2; try (exfalso; eapply Ht2;  eauto; fail  ).
      * rewrite <- H0 in Hsec. inv Hsec; try inv CHECK.
      * rewrite <- H0 in Hsec. inv Hsec; ddestruction; subst; try inv CHECK.
        --  unpriv_co. right. eapply CIH; eauto. apply H3.
        --  unpriv_halt. right. eapply CIH; eauto.
  - rewrite <- H0 in Hsec. inv Hsec; ddestruction; subst; try inv CHECK; try contradiction; try contra_size.
    +  constructor; auto. right. eapply CIH; eauto with itree. apply H2.
    +  unpriv_co. right. eapply CIH; eauto with itree. apply H2.
    +  unpriv_co. right. eapply CIH; eauto with itree. apply H2.
    +  unpriv_halt. right. eapply CIH; eauto. step. constructor. left. auto.
    +  unpriv_halt. right. eapply CIH with (t1 := Vis e k1); try apply H2.
      step. constructor. left. auto.
    +  unpriv_halt. right. eapply CIH; eauto with itree. apply H2.
Qed.

Lemma eqit_secure_eq_trans : forall E R b1 b2 Label priv l (t1 t2 t3 : itree E R),
    eqit_secure Label priv eq b1 b2 l t1 t2 ->
    eqit_secure Label priv eq b1 b2 l t2 t3 ->
    eqit_secure Label priv eq b1 b2 l t1 t3.
Proof.
  intros. apply eqit_secure_RR_imp with (RR1 := rcompose eq eq).
  { intros. inv PR. auto. }
  eapply eqit_secure_trans; eauto.
Qed.

Lemma eqit_secure_anything : forall E R1 b Label priv l
                      (t1 : itree E R1) t2,
    eqit_secure Label priv eq b b l t1 t2 ->
    eqit_secure Label priv eq b b l t1 t1.
Proof.
  intros.
  eapply eqit_secure_eq_trans; eauto.
  apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto.
Qed.


Global Instance proper_eqit_secure_eqit {E} {R1 R2 : Type} {b} {RR : R1 -> R2 -> Prop} {Label priv l} :
       Proper (eqit eq b b ==> eqit eq b b ==> iff) (@eqit_secure E R1 R2 Label priv RR b b l).
Proof.
  repeat intro. destruct b; split; intros.
  - eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - assert (x ≈ y); auto. assert (x0 ≈ y0); auto.
    symmetry in H2.
    eapply eutt_secure_eqit_secure; eauto.
    symmetry in H3. apply eqit_secure_sym.
    eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - assert (x ≅ y); auto. assert (x0 ≅ y0); auto.
    symmetry in H2. symmetry in H3.
    eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
Qed.

Global Instance proper_eqit_secure_eqit_secure
       {E} {b} {R1 R2 : Type} {RR : R1 -> R2 -> Prop} {Label priv l} :
  Proper (eqit_secure Label priv eq b b l ==> eqit_secure Label priv eq b b l ==> iff)
         (@eqit_secure E R1 R2 Label priv RR b b l).
Proof.
  repeat intro; split; intros.
  - eapply eqit_secure_RR_imp with (RR1 := rcompose RR eq); eauto.
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
    apply eqit_secure_sym.
    eapply eqit_secure_RR_imp with (RR1 := rcompose (flip RR) eq); eauto.
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto. apply eqit_secure_sym. auto.
  - assert (eqit_secure Label priv eq b b l y0 x0).
    { apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto. }
    eapply eqit_secure_RR_imp with (RR1 := rcompose RR eq).
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
    assert (eqit_secure Label priv eq b b l y x).
    { apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto. }
    eapply eqit_secure_RR_imp with (RR1 := rcompose eq RR).
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
Qed.
