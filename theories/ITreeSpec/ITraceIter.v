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
     Dijkstra.DijkstraMonad
     Dijkstra.ITrace
     Dijkstra.ITraceBind
     Dijkstra.EuttDiv
     Dijkstra.ITracePreds
     Dijkstra.ITraceBindTrigger
     Dijkstra.TracesIT
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac prove_arg H :=
  let H' := fresh H in
  match type of H with ?P -> _ => assert (H' : P); try (specialize (H H'); clear H') end.


Section eqitC_euttEv.
  Context {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  (* Question, is it a problem that I don't have the booleans, is that necessary? 
     Would be simple to add but would necessitate some busy work *)

  (* A transitivity functor *)
  Variant eqit_trans_clo  (b1 b2 b1' b2' : bool)  (r : itree E1 R1 -> itree E2 R2 -> Prop) : 
    itree E1 R1 -> itree E2 R2 -> Prop := 
    eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' t1 t1')
      (EQVr: eqit RR2 b2 b2' t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      eqit_trans_clo b1 b2 b1' b2' r t1 t2.
  Hint Constructors eqit_trans_clo : core.
  (* sets directionality *)
  Definition eqitC_euttEv b1 b2 := eqit_trans_clo b1 b2 false false.
  Hint Unfold eqitC_euttEv : core.

  Lemma eqitC_euttEv_mon b1 b2 r1 r2 t1 t2 
    (IN : eqitC_euttEv b1 b2 r1 t1 t2)
    (LE : r1 <2= r2) :
    eqitC_euttEv b1 b2 r2 t1 t2.
  Proof.
    destruct IN; econstructor; eauto.
  Qed.

  Hint Resolve eqitC_euttEv_mon : paco.
    

End eqitC_euttEv.

(*replicate this proof for the models functor*)
Lemma eqitC_euttEv_wcompat (b1 b2 : bool) E1 E2 R1 R2 (REv : forall A B, E1 A -> E2 B -> Prop) 
      (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop ) (RR : R1 -> R2 -> Prop) 
     (vclo: (itree E1 R1 -> itree E2 R2 -> Prop) -> (itree E1 R1 -> itree E2 R2 -> Prop) )
     (MON: monotone2 vclo)
      (CMP: compose (eqitC_euttEv RR b1 b2) vclo <3= compose vclo (eqitC_euttEv RR b1 b2)) :
  wcompatible2 (EuttEv.euttEv_ REv RAns RR vclo) (eqitC_euttEv RR b1 b2).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply eqitC_euttEv_mon; eauto. }
  intros.
  dependent destruction PR. punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst; try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; try (constructor; eauto; fail).
    constructor; auto. intros. apply H0 in H1. pclearbot. eapply MON.
    + eapply CMP. red. econstructor; eauto.
    + intros. apply gpaco2_clo; auto.
Qed.

Hint Resolve (eqitC_euttEv_wcompat true true) : paco.

Global Instance geuttEv_cong_eqit {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
      (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
    Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (EuttEv.euttEv_ REv RAns RS id) (eqitC_euttEv RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto; 
  try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

Global Instance geuttEv_cong_euttge {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
      (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
    Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (EuttEv.euttEv_ REv RAns RS id) (eqitC_euttEv RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

Lemma test : forall E A B (a : A) (body1 body2 : A -> itree E (A + B) ),
 (forall a, body1 a ≅ body2 a) -> 
 ITree.iter body1 a ≈ iter body2 a.
Proof. 
  intros E A B a body1 body2 Hbody. revert a.
  ginit.  gcofix CIH. intros.
  setoid_rewrite unfold_iter. setoid_rewrite Hbody.
  remember (body2 a) as t. clear Heqt. revert t. gcofix CIH'. intros.
  gstep. red. cbn. unfold observe. cbn.
  destruct (observe t); cbn.
  - destruct r0; cbn; constructor; auto.
    gfinal. left. apply CIH.
  - constructor. gfinal. left. auto. 
  - constructor. intros. gfinal. eauto.
Qed.

Lemma test2 : forall E A B (a : A) (body1 body2 : A -> itree E (A + B) ),
 (forall a, body1 a ≈ body2 a) -> 
 ITree.iter body1 a ≈ iter body2 a.
Proof.
  intros E A B a body1 body2 Hbody. revert a.
  ginit. gcofix CIH0. intros. setoid_rewrite unfold_iter.
  remember (body1 a) as t1. remember (body2 a) as t2.
  assert (t1 ≈ t2).
  { subst; auto. }
  clear Heqt1 Heqt2. generalize dependent t2. revert t1. gcofix CIH1.
  intros. gstep. red. unfold observe. cbn.
  punfold H0. red in H0. hinduction H0 before r; subst; intros.
  - destruct r2; constructor; auto. gfinal. eauto.
  - pclearbot. constructor. gfinal. left. eauto.
  - constructor. intros. gfinal. left. pclearbot.
    eapply CIH1; apply REL.
  - constructor; auto.
  - constructor; auto.
Qed.
(*this shows that these properness results with gpaco are no joke*)
(* find a better place for this proof *)

Global Instance gtrace_refine_cong_eqit {E R r rg} :
      Proper (@eq_itree (EvAns E) R R eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (EuttEv.euttEv_ (REvRef E) (RAnsRef E) eq id) (eqitC_euttEv eq true true) r rg).
Proof.
  apply geuttEv_cong_eqit; intros; rewrite H; auto.
Qed.

Global Instance gtrace_refine_cong_euttge {E R r rg} :
      Proper (@euttge (EvAns E) R R eq ==> euttge eq ==> flip impl)
         (gpaco2 (EuttEv.euttEv_ (REvRef E) (RAnsRef E) eq id) (eqitC_euttEv eq true true) r rg).
Proof.
  apply geuttEv_cong_euttge; intros; rewrite H; auto.
Qed.


Ltac simpobs H := apply simpobs in H.
(*
Lemma trace_refine_proper_l : forall E R (tr1 tr2 : itree  (EvAns E) R) (t : itree E R),
    tr1 ≈ tr2 -> tr1 ⊑ t -> tr2 ⊑ t.
Proof.
  intros E R. ginit. gcofix CIH. intros tr1 tr2 t Htr Href.
  punfold Href. red in Href. genobs tr1 otr1. genobs t ot.
  hinduction Href before r; intros; subst.
  - simpobs Heqotr1. simpobs Heqot. rewrite Heqot. rewrite Heqotr1 in Htr.
    clear Heqot Heqotr1.
    match type of Htr with ?t1 ≈ ?t2 => genobs t1 or1; genobs t2 otr2 end.
    punfold Htr. red in Htr. rewrite <- Heqor1 in Htr. rewrite <- Heqotr2 in Htr.
    cbn in *. hinduction Htr before r; intros; try inv Heqor1.
    + simpobs Heqotr2. rewrite Heqotr2. gstep. constructor. auto.
    + simpobs Heqotr2. rewrite Heqotr2. rewrite tau_euttge. eauto.
  - simpobs Heqot. simpobs Heqotr1. pclearbot.
    rewrite Heqot. clear Heqot. 
    assert ((exists tr2', observe tr2 = TauF tr2') \/ (forall tr2', observe tr2 <> TauF tr2') ).
    { destruct (observe tr2); eauto; right; repeat intro; discriminate. }
    destruct H0 as [ [tr2' Htr2] |  Htr2  ].
    + symmetry in Htr2. simpobs Htr2. rewrite Htr2. gstep. constructor. gfinal.
      left. eapply CIH; eauto. rewrite Heqotr1 in Htr.
      rewrite tau_eutt in Htr. rewrite Htr. rewrite Htr2. rewrite tau_eutt. reflexivity.
    + destruct (observe tr2) eqn : Htr2'.
      * symmetry in Htr2'. simpobs Htr2'. rewrite Htr2'. rewrite tau_euttge.
        assert (m1 ≈ Ret r0).
        { rewrite Heqotr1 in Htr. rewrite <- Htr2'. rewrite <- Htr. rewrite tau_eutt. reflexivity. }
        clear Htr2 Htr2' Htr Heqotr1.
        punfold H. red in H. genobs m1 om1. genobs m2 om2.
        hinduction H before r; intros; subst.
        ++ simpobs Heqom1. simpobs Heqom2.
           rewrite Heqom2. rewrite Heqom1 in H0. pinversion H0; subst.
           gstep; constructor; eauto.
        ++
        eapply gpaco2_clo. econstructor. 
        rewrite Htr2' in Htr. rewrite Heqotr1 in Htr. rewrite tau_eutt in Htr.
        clear CIH.
    admit.
  - simpobs Heqotr1. rewrite Heqotr1 in Htr. rewrite tau_eutt in Htr.
    eapply IHHref; eauto.
  - simpobs Heqot. rewrite Heqot. rewrite tau_euttge. eapply IHHref; eauto.
  - simpobs Heqot. simpobs Heqotr1. rewrite Heqot. clear Heqot. rewrite Heqotr1 in Htr.
    clear Heqotr1.
    match type of Htr with ?t1 ≈ ?t2 => genobs t1 ovis; genobs t2 otr2 end.
    punfold Htr. red in Htr. rewrite <- Heqovis in Htr. rewrite <- Heqotr2 in Htr.
    hinduction Htr before r; intros; try inv Heqovis.
    + inj_existT. subst. inv H; inj_existT; subst.
      * simpobs Heqotr2. rewrite Heqotr2. gstep.
        constructor; auto. intros. apply H0 in H. pclearbot.
        gfinal. left. destruct a0. eapply CIH; eauto. apply REL.
      * simpobs Heqotr2. rewrite Heqotr2. gstep. constructor; auto.
        intros [].
    + simpobs Heqotr2. rewrite Heqotr2. rewrite tau_euttge. eauto.
Qed. *)
(* might be worth it to prove the directed versions of this as well,
   could help make this proof more readable *)
(*This may be replicable in the ⊧ case also this should be moved to itrace stuff,*)
Lemma trace_iter_refine : forall E A B 
(trbody : A -> itree (EvAns E) (A + B)) (body : A -> itree E (A + B) ),
    (forall a, trbody a ⊑ body a) -> forall a, iter trbody a ⊑ iter body a.
Proof. 
  intros E A B trbody body Href. ginit.
  gcofix CIH0. intros. setoid_rewrite unfold_iter.
  remember (trbody a) as tr. remember (body a) as t.
  assert (tr ⊑ t); try (subst; auto; fail). clear Heqtr Heqt.
  generalize dependent tr. revert t. gcofix CIH1. intros.
  punfold H0. red in H0. remember (observe tr) as otr.
  remember (observe t) as ot.
  hinduction H0 before r; intros.
  - apply simpobs in Heqot. apply simpobs in Heqotr.
    rewrite Heqotr. rewrite Heqot. repeat rewrite bind_ret_l.
    subst. destruct r2; gstep; constructor; auto.
    gfinal. eauto.
  - apply simpobs in Heqot. apply simpobs in Heqotr.
    rewrite Heqotr. rewrite Heqot. repeat rewrite bind_tau.
    gstep. constructor. gfinal. left. eapply CIH1. pclearbot. auto.
  - apply simpobs in Heqotr. rewrite Heqotr. rewrite bind_tau.
    rewrite tau_euttge. pclearbot. eapply IHeuttEvF; eauto.
  - apply simpobs in Heqot. rewrite Heqot. rewrite bind_tau.
    rewrite tau_euttge. pclearbot. eapply IHeuttEvF; eauto.
  - apply simpobs in Heqot. apply simpobs in Heqotr.
    rewrite Heqotr. rewrite Heqot. repeat rewrite bind_vis.
    gstep. constructor; eauto. intros. apply H0 in H1.
    pclearbot. gfinal. left. eauto.
Qed.


Global Instance monad_itrace {E} : Monad (itrace E) := Monad_itree.
Lemma trace_bind_refine : forall E A B (tr : itrace E A) (ktr : A -> itrace E B) (t : itree E A) (kt : A -> itree E B),
    tr ⊑ t -> (forall a, (ktr a) ⊑ (kt a)) -> (tr >>= ktr) ⊑ (t >>= kt).
Proof.
  intros. generalize dependent tr.
  revert t. cbn. ginit. gcofix CIH0. intros.
  punfold H1. red in H1. remember (observe tr) as otr. remember (observe t) as ot.
  hinduction H1 before r; intros; subst.
  - apply simpobs in Heqotr. apply simpobs in Heqot. rewrite Heqotr.
    rewrite Heqot. repeat rewrite bind_ret_l. gfinal.
    right. eapply paco2_mon; try apply H0. intros; contradiction.
  - apply simpobs in Heqotr. apply simpobs in Heqot.
    rewrite Heqot. rewrite Heqotr. repeat rewrite bind_tau.
    gstep. constructor. gfinal. pclearbot. eauto.
  - apply simpobs in Heqotr. rewrite Heqotr. rewrite tau_euttge.
    eapply IHeuttEvF; eauto.
  - apply simpobs in Heqot. rewrite Heqot. rewrite bind_tau.
    rewrite tau_euttge. eapply IHeuttEvF; eauto.
  - apply simpobs in Heqotr. apply simpobs in Heqot.
    rewrite Heqot. rewrite Heqotr. repeat rewrite bind_vis.
    gstep. constructor; auto. intros. apply H1 in H2.
    pclearbot. gfinal. left. eauto.
Qed.
