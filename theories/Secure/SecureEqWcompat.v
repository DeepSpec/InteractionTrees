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
     Secure.SecureEqEuttHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma eqit_secureC_wcompat_id :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l
, wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l id) 
                                         (eqitC RR b1 b2) .
Proof.
  econstructor. pmonauto.
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. unfold_eqit. red in REL. red.
  hinduction REL before r; intros; clear t1' t2'; try inv CHECK.
  - genobs_clear t1 ot1. genobs_clear t2 ot2.
    remember (RetF r1) as x.
    hinduction EQVl before r; intros; inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; inv Heqy; eauto.
  - remember (TauF t1) as y.
    hinduction EQVl before r; intros; inv Heqy; try inv CHECK; subst; eauto.
    remember (TauF t2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    pclearbot. constructor. gclo. econstructor; cycle -1; eauto with paco.
  - eapply IHREL; eauto.
    remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    constructor; auto. pclearbot. pstep_reverse.
  - eapply IHREL; eauto.
    remember (TauF t2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto.
    constructor; auto. pclearbot. pstep_reverse.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. constructor; auto.
    intros. apply gpaco2_clo. pclearbot. econstructor; eauto. apply H.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    ITraceFacts.inj_existT. subst. pclearbot. remember (TauF t2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
    pclearbot.
    unpriv_co. gclo. econstructor; cycle -1; eauto with paco. gfinal.
    left. apply H.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    remember (VisF e k2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
    ITraceFacts.inj_existT. subst.
    pclearbot. unpriv_co. gclo. econstructor; cycle -1; eauto with paco.
    gfinal. left. apply H.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto.
    ITraceFacts.inj_existT. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto.
    ITraceFacts.inj_existT. subst. unpriv_co. gclo. pclearbot.
    econstructor; cycle -1; eauto with paco. gfinal. left. apply H.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. pclearbot. unpriv_ind.
    eapply H0; eauto. pstep_reverse.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. pclearbot. unpriv_ind.
    eapply H0; eauto. pstep_reverse.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. remember (TauF t2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
    pclearbot. unpriv_halt. gclo. econstructor; cycle -1; eauto with paco.
    pfold. constructor. left. auto.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. remember (TauF t1) as y.
    hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto.
    pclearbot. unpriv_halt. gclo. econstructor; cycle -1; eauto with paco.
    pfold. constructor. left. auto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; try contra_size; eauto.
    ITraceFacts.inj_existT. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. unpriv_halt. pclearbot.
    gclo. econstructor; cycle -1; eauto with paco.
    Unshelve. all : try apply (Vis e1 k3).
    + pfold. constructor. left. auto.
    + gfinal. left. apply H.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; try contra_size; eauto.
    ITraceFacts.inj_existT. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
    ITraceFacts.inj_existT. subst. unpriv_halt. pclearbot.
    gclo. econstructor; cycle -1; eauto with paco.
    Unshelve. all : try apply (Vis e2 k4).
    + pfold. constructor. left. auto.
    + gfinal. left. apply H.
Qed.

Hint Resolve eqit_secureC_mon : paco.

Lemma eqit_secure_shalt_refl : forall E R1 R2 b1 b2 (RR : R1 -> R2 -> Prop) Label priv l A (e : E A) k1 k2,
    (~ leq (priv _ e) l) -> empty A ->
    eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2).
Proof.
  intros. pfold. red. cbn. unpriv_halt. contra_size.
Qed.

Ltac inv_vis_secure := ITraceFacts.inj_existT; subst;
   try contradiction; try contra_size. 
Ltac clear_trivial :=
  repeat match goal with 
  | H : empty ?A, H' : forall a : ?A, ?P |- _ => clear H' end.
Ltac eqit_secureC_halt_cases E := repeat (pclearbot; clear_trivial; match goal with
     | |- _ (TauF _ ) (TauF _) => constructor; gclo; pclearbot 
     | |- eqit_secureC ?RR ?Label ?priv ?l ?b1 ?b2 _ ?t1 ?t2 => econstructor; clear_trivial; eauto with paco 
     | H : secure_eqitF ?Label ?priv ?RR ?b1 ?b2 ?l _ _ (observe ?t1) _ |- eqit_secure ?Label ?priv ?RR ?b1 ?b2 ?l ?t1 ?t2 => pfold; eauto
     |  H : nonempty ?A |- _ _ (@VisF _ _ _ ?A ?e _ ) => unpriv_co; gclo ; pclearbot
     |  H : nonempty ?A |- _  (@VisF _ _ _ ?A ?e _ ) _ => unpriv_co; gclo ; pclearbot
     |  H : empty ?A |- _ _ (@VisF _ _ _ ?A ?e _ ) => unpriv_halt; gclo ; pclearbot
     |  H : empty ?A |- _ (@VisF _ _ _ ?A ?e _ ) _ => unpriv_halt; gclo ; pclearbot
     | |- eqit_secureC ?RR ?Label ?priv ?l ?b1 ?b2 _ ?t1 ?t2 => econstructor; eauto with paco 

     | H : forall a, secure_eqitF ?Label ?priv ?RR ?b1 ?b2 ?l _ _ _ (observe ?t2), 
       H1 : observe ?t2 = VisF ?e ?k |- eqit_secure _ _ _ _ _ _ _ (Vis ?e ?k) =>
       rewrite H1 in H; pfold; apply H 
     |  HA : empty ?A, HB : empty ?B, ev1 : E ?A |- 
                       eqit_secure _ _ _ _ _ _ (go (@VisF _ _ _ ?A _ _ )) (go (@VisF _ _ _ ?B _ _ ))
                       => pfold; red; cbn; unpriv_halt; try contra_size
     |  H : forall a : ?A, paco2 _ bot2 (?k a) ?t |- eqit_secure _ _ _ _ _ _ (?k ?a) (?t)  => red; eauto
     |  H : forall a : ?A, paco2 _ bot2 ?t (?k a) |- eqit_secure _ _ _ _ _ _ ?t (?k ?a)   => red; eauto
     |  H : forall (a : ?A) (b : ?B), paco2 _ bot2 (?k1 a) (?k2 b) |- 
                                                                        eqit_secure _ _ _ _ _ _ (?k1 ?a) (?k2 ?b)   => red; eauto                 | H : _ (observe ?t) (VisF ?e1 ?k1) |- _ ?t ?t1 => rewrite itree_eta' in H; apply H
     | a : ?A, H : empty ?A |- _ => contra_size 
     | a : ?A |- nonempty ?A => constructor; auto
     | HA : empty ?A, HB : empty ?B, Heq : observe ?t = (@VisF _ _ _ ?A _ _)   |- 
         gpaco2 _ _ _ _ (?t ) (go (@VisF _ _ _ ?B _ _))  => gfinal; right; pstep; red; cbn; rewrite Heq; unpriv_halt 
     | HA : empty ?A, HB : empty ?B |- 
         gpaco2 _ _ _ _ (go (@VisF _ _ _ ?A _ _) ) (go (@VisF _ _ _ ?B _ _))  => gfinal; right; pstep; red; cbn; unpriv_halt
     | H : forall (a : ?A), _ (observe (?k a) ) observe (?t), Heq : observe ?t = VisF ?e ?k1 |-
        eqit_secure _ _ _ _ _ _ (?k ?a) _ => rewrite itree_eta' in Heq; rewrite Heq in H; pfold; apply H
     | H : forall a : ?A, ?P (observe (?k a) ) (observe ?t), Heq : observe ?t = VisF ?e ?k2 |- 
                                                        eqit_secure _ _ _ _ _ _ (?k ?a) _ => 
                                          rewrite itree_eta' in Heq; rewrite Heq in H; pfold; apply H
  end; 
  clear_trivial)
. 

Ltac find_size A := 
  match goal with 
  | H : nonempty A |- _ => idtac 
  | H : empty A |- _ => idtac 
  | |- _ => destruct (classic_empty A); try contra_size end.
             

Ltac produce_elem H A := inv H; assert (nonempty A); try (constructor; auto; fail).



Lemma eqit_secureC_wcompat_id' :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l, 
    wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l id) 
                                         (eqit_secureC RR Label priv l b1 b2) .
Proof.
  econstructor. 
  { red. intros. eauto with paco. }
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. red in EQVl. red in EQVr. red in REL. red.
  hinduction REL before r; intros; clear t1' t2'; try inv CHECK.
  - remember (RetF r1) as x. hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y. hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
    rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  - remember (TauF t1) as x. hinduction EQVl before r; intros; subst; try inv Heqx;
    try inv CHECK; eauto.
    + remember (TauF t4) as y. pclearbot. 
      (* think I might have a lead on the problem, should H0 have vclo not id here?*)
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; eauto.
      * constructor. gclo. econstructor; eauto. gfinal; eauto.
      * unpriv_co. gclo. econstructor; eauto. apply H. gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
    + remember (TauF t3) as y. pclearbot.
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; eauto.
      * unpriv_co. gclo. econstructor; eauto. apply H0. gfinal; eauto.
      * unpriv_co. gclo. econstructor; eauto. apply H0. apply H.
        gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
      * unpriv_halt. gclo. econstructor; eauto. apply H0. gfinal; eauto.
   + remember (TauF t3) as y. pclearbot.
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; eauto.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
      * unpriv_halt. gclo. econstructor; eauto. apply H.
        gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
      * unpriv_halt. contra_size.
 - eapply IHREL; eauto.
   remember (TauF t1) as y. hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto.
   + constructor; auto. pclearbot. pstep_reverse.
   + unpriv_ind. pclearbot. pstep_reverse.
   + pclearbot. punfold H.
 - eapply IHREL; eauto. 
   remember (TauF t2) as y. hinduction EQVr before r; intros; inv Heqy; try inv CHECL; eauto.
   + constructor; auto. pclearbot. pstep_reverse.
   + unpriv_ind. pclearbot. pstep_reverse.
   + pclearbot. punfold H.
 - remember (VisF e k1) as x. 
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto.
   remember (VisF e0 k3) as y.
   hinduction EQVr before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; eauto.
   + pclearbot. constructor; auto. intros. gclo. econstructor; eauto.
     apply H0. apply H. gfinal; left; apply H1.
   + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
 - unfold id in H. remember (VisF e k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto.
   + pclearbot. remember (TauF t2) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
     * constructor. gclo. pclearbot. inv SIZECHECK.  econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_co. gclo. pclearbot. inv SIZECHECK0. econstructor; eauto. apply H0.
       apply H. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
     * unpriv_halt. pclearbot. inv SIZECHECK0.
       gclo. econstructor; eauto. apply H0. gfinal; eauto.
       Unshelve. auto.
   + pclearbot. pclearbot. inv SIZECHECK. remember (TauF t2) as y.     
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
     * unpriv_co. gclo. pclearbot. econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_co. gclo. pclearbot. econstructor; eauto.
       apply H0. apply H. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
     * pclearbot. unpriv_halt. gclo. econstructor; eauto.
       apply H0. gfinal; eauto. Unshelve. auto.
  + pclearbot. inv SIZECHECK0. remember (TauF t2) as y.     
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto.
     * unpriv_halt. gclo. pclearbot. econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_halt. gclo. pclearbot. econstructor; eauto.
       apply H0. apply H. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
     * pclearbot. unpriv_halt. contra_size. 
 - unfold id in H. remember (VisF e k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto.
   + pclearbot. remember (TauF t0) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto.
     * constructor. gclo. pclearbot. inv SIZECHECK.  econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_co. gclo. pclearbot. inv SIZECHECK0. econstructor; eauto. apply H.
       apply H0. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
     * unpriv_halt. pclearbot. inv SIZECHECK0.
       gclo. econstructor; eauto. apply H0. gfinal; eauto.
       Unshelve. auto.
   + pclearbot. pclearbot. inv SIZECHECK. remember (TauF t1) as y.     
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto.
     * unpriv_co. gclo. pclearbot. econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_co. gclo. pclearbot. econstructor; eauto.
       apply H. apply H0. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
     * pclearbot. unpriv_halt. gclo. econstructor; eauto.
       apply H0. gfinal; eauto. Unshelve. auto.
  + pclearbot. inv SIZECHECK0. remember (TauF t1) as y.     
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto.
     * unpriv_halt. gclo. pclearbot. econstructor; eauto. apply H0.
       gfinal; eauto. Unshelve. auto.
     * unpriv_halt. gclo. pclearbot. econstructor; eauto.
       apply H. apply H0. gfinal; eauto. Unshelve. auto.
     * rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
     * pclearbot. unpriv_halt. contra_size. 
 - unfold id in H. remember (VisF e2 k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto; pclearbot.
   + inv SIZECHECK1. inv SIZECHECK2. remember (VisF e1 k1) as y. 
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; subst; eauto;
     try (eqit_secureC_halt_cases E; fail).
     rewrite itree_eta'. unpriv_ind. eapply H0; auto. all : eauto.
     Unshelve. all : auto.
   + inv SIZECHECK0. inv SIZECHECK3. remember (VisF e0 k0) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; subst; eauto;
     try (eqit_secureC_halt_cases E; fail).
      rewrite itree_eta'. unpriv_ind. eapply H0; auto. all : eauto.
      Unshelve. all : auto.
   + inv SIZECHECK1. inv SIZECHECK2. remember (VisF e0 k0) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; subst; eauto;
     try (eqit_secureC_halt_cases E; fail).
      rewrite itree_eta'. unpriv_ind. eapply H0; auto. all : eauto.
      Unshelve. all : auto. 
 - inv SIZECHECK. eapply H0; eauto. Unshelve. all : auto.
   remember (VisF e k1) as x. clear H0.
   hinduction EQVl before r; intros; inv Heqx; inv_vis_secure; try inv CHECK; pclearbot; eauto.
   + constructor; auto. pstep_reverse.
   + unpriv_ind. pstep_reverse.
   + rewrite itree_eta' at 1 . pstep_reverse.
 - inv SIZECHECK. eapply H0; eauto. Unshelve. all : auto.
   remember (VisF e k2) as x. clear H0.
   hinduction EQVr before r; intros; inv Heqx; inv_vis_secure; try inv CHECK; pclearbot; eauto.
   + constructor; auto. pstep_reverse.
   + unpriv_ind. pstep_reverse.
   + rewrite itree_eta' at 1 . pstep_reverse.
 - remember (TauF t2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; pclearbot; eauto;
   inv EQVl; inv_vis_secure; eqit_secureC_halt_cases E.
   + pclearbot. find_size A0; eqit_secureC_halt_cases E.
   + pclearbot. find_size A1; eqit_secureC_halt_cases E.
 - remember (TauF t1) as x.
   hinduction  EQVl before r; intros; inv Heqx; try inv CHECK; pclearbot; eauto;
   inv EQVr; inv_vis_secure;
   eqit_secureC_halt_cases E.
   + find_size A0; eqit_secureC_halt_cases E.
   + find_size A1; eqit_secureC_halt_cases E.
 - unfold id in H. remember (VisF e2 k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure;  pclearbot; eauto;
   inv EQVl; inv_vis_secure;
   (* maybe I should just write a new one *)
   do 2 (
   repeat match goal with | H : nonempty ?A |- _ => inv H end;
   match goal with
   | e1 : E ?A, e2 : E ?B, e3 : E ?C, e4 : E ?D |- _ =>
     find_size A ; find_size B; find_size C ; find_size D ; try contra_size
   | e1 : E ?A, e2 : E ?B, e3 : E ?C |- _ => 
     find_size A ; find_size B; find_size C ; try contra_size
   | e1 : E ?A, e2 : E ?B |- _ =>
      find_size A ; find_size B; try contra_size
   | e1 : E ?A |- _ =>
     find_size A ; try contra_size 
   end);
   eqit_secureC_halt_cases E; try (eapply eqit_secure_shalt_refl; eauto); eqit_secureC_halt_cases E;
   try apply H3; try apply H; eqit_secureC_halt_cases E.
   Unshelve. all : auto. 
 - unfold id in H. remember (VisF e1 k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; pclearbot; eauto;
     inv EQVr; inv_vis_secure;
       do 2 (
            repeat match goal with | H : nonempty ?A |- _ => inv H end;
            match goal with
            | e1 : E ?A, e2 : E ?B, e3 : E ?C, e4 : E ?D |- _ =>
              find_size A ; find_size B; find_size C ; find_size D ; try contra_size
            | e1 : E ?A, e2 : E ?B, e3 : E ?C |- _ => 
              find_size A ; find_size B; find_size C ; try contra_size
            | e1 : E ?A, e2 : E ?B |- _ =>
              find_size A ; find_size B; try contra_size
            | e1 : E ?A |- _ =>
              find_size A ; try contra_size 
            end);
       eqit_secureC_halt_cases E; try (eapply eqit_secure_shalt_refl; eauto); eqit_secureC_halt_cases E;
   try apply H3; try apply H; eqit_secureC_halt_cases E.
   Unshelve. all: auto.
Qed.


Hint Resolve eqit_secureC_wcompat_id : paco.

Global Instance geuttgen_cong_secure_eqit {E} {Label priv l} {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop} 
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} : 
    (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
    (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
    Proper (@eq_itree E R1 R1 RR1 ==> eq_itree RR2 ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) r rg ).
Proof.
  repeat intro. gclo. econstructor; eauto.
  - eapply eqit_mon, H1; eauto; discriminate.
  - eapply eqit_mon, H2; eauto; discriminate.
Qed.

Global Instance geuttgen_cong_secure_eqit' {E} {Label priv l} {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop} 
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} : 
    (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
    (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
    Proper (@eqit_secure E R1 R1 Label priv RR1 false false l ==> 
             eqit_secure Label priv RR2 false false l ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqit_secureC RS Label priv l b1 b2) r rg ).
Proof.
  repeat intro. gclo. econstructor; eauto.
  - eapply secure_eqit_mon, H1; eauto. intros; discriminate.
  - eapply secure_eqit_mon, H2; eauto. intros; discriminate.
Qed.

(* eqit_bind_clo eqit_clo_bind *)

Global Instance geutt_cong_euttge:
  forall {E : Type -> Type} Label priv l b1 b2 {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop} 
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop}
    (r rg : forall x : itree E R1, (fun _ : itree E R1 => itree E R2) x -> Prop),
  (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
  (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
    (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

Global Instance geutt_eq_cong_euttge:
  forall {E : Type -> Type} Label priv l b1 b2 {R1 R2 : Type} r rg RS ,
    Proper ( @euttge E R1 R1 eq ==> @euttge E R2 R2 eq ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS true true) r rg ).
Proof.
  repeat intro. eapply geutt_cong_euttge; eauto; intros; subst; auto.
Qed.
(* 
Global Instance geutt_eq_cong_euttgel:
  forall {E : Type -> Type} Label priv l b1 b2 {R1 R2 : Type} r rg RS ,
    Proper ( @euttge E R1 R1 eq ==> @eq_itree E R2 R2 eq ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS true false) r rg ).
Proof.
  repeat intro. assert (x0 ≳ y0). rewrite H0. reflexivity.
  eapply geutt_cong_euttge; eauto; intros; subst; auto.
Qed.
*)
