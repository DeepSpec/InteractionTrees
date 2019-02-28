(* Equivalence up to taus *)
(* We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. The main consequence of this
   choice is that equivalence up to taus is an equivalence relation.
 *)

(* TODO:
   - Generalize Reflexivity, Symmetry, Transitivity to heterogeneous
     eutt.
   - Make eutt a notation instead of a definition?
 *)

Require Import Paco.paco.

From Coq Require Import
     Program
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From ITree Require Import
     Core
     UpToTausExplicit.

From ITree Require Export
     Eq.Eq.

Local Open Scope itree.


Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttF 
              (eutt: itree E R1 -> itree E R2 -> Prop)
              (eutt_taus: itreeF E R1 _ -> itreeF E R2 _ -> Prop)
  : itreeF E R1 _ -> itreeF E R2 _ -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF eutt eutt_taus (RetF r1) (RetF r2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, eutt (k1 x) (k2 x)):
    euttF eutt eutt_taus (VisF e k1) (VisF e k2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt_taus (observe t1) (observe t2)):
    euttF eutt eutt_taus (TauF t1) (TauF t2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF eutt eutt_taus (observe t1) ot2):
    euttF eutt eutt_taus (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF eutt eutt_taus ot1 (observe t2)):
    euttF eutt eutt_taus ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt_ eutt t1 t2 := paco2 (euttF eutt) bot2 (observe t1) (observe t2).
Hint Unfold eutt_.

Lemma euttF_mon r r' s s' x y
    (EUTT: euttF r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF r' s' x y.
Proof.
  induction EUTT; eauto.
Qed.

Lemma monotone_euttF eutt : monotone2 (euttF eutt).
Proof. repeat intro. eauto using euttF_mon. Qed.
Hint Resolve monotone_euttF : paco.

Lemma monotone_eutt_ : monotone2 eutt_.
Proof. red. eauto using euttF_mon, paco2_mon_gen. Qed.
Hint Resolve monotone_eutt_ : paco.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)
Definition eutt : itree E R1 -> itree E R2 -> Prop := paco2 eutt_ bot2.
Hint Unfold eutt.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors euttF.
Hint Unfold eutt_.
Hint Resolve monotone_euttF : paco.
Hint Resolve monotone_eutt_ : paco.
Hint Unfold eutt.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  pcofix CIH. intros. pfold. revert_until CIH. pcofix CIH'. intros.
  punfold H0. pfold. inv H0; pclearbot; eauto 7.
Qed.

Global Instance Reflexive_eutt_gen `{Reflexive _ RR}
       (r : itree E R -> itree E R -> Prop) :
  Reflexive (paco2 (eutt_ RR) r).
Proof.
  pcofix CIH. intros. pfold. revert x. pcofix CIH'. intros.
  genobs x ox. destruct ox; eauto.
Qed.

Global Instance Reflexive_euttF_gen `{Reflexive _ RR}
       (r : relation (itree E R)) (r' : relation (itree' E R)) :
  Reflexive (euttF RR (upaco2 (eutt_ RR) r) (upaco2 (euttF RR (upaco2 (eutt_ RR) r)) r')). 
Proof.
  repeat intro. assert (X := Reflexive_eutt_gen r (go x)). do 2 punfold X.
  eauto using euttF_mon, upaco2_mon_bot.
Qed.

Global Instance Symmetric_eutt_gen `{Symmetric _ RR}
       (r : itree E R -> itree E R -> Prop)
       (Sr : Symmetric r) :
  Symmetric (paco2 (eutt_ RR) r).
Proof.
  pcofix CIH. intros. pfold. revert_until CIH. pcofix CIH'. intros.
  punfold H1. punfold H1. pfold.
  genobs_clear x ox. genobs_clear y oy.
  induction H1; pclearbot; eauto.
  - econstructor. intros. destruct (EUTTK x); eauto.
  - punfold EQTAUS. eauto 8.
Qed.

End EUTT_homo.

Lemma Symmetric_eutt_ {E R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    paco2 (eutt_ RR1) r1 t1 t2 -> paco2 (eutt_ RR2) r2 t2 t1.
Proof.
  pcofix CIH. intros.
  pfold. revert_until CIH. pcofix CIH'. intros.
  pfold. do 2 punfold H0.
  genobs_clear t1 ot1. genobs_clear t2 ot2.
  induction H0; pclearbot; eauto 7.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Section EUTT_eq_EUTTE.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma euttE__impl_eutt_ r t1 t2 :
  @euttE_ E R1 R2 RR r t1 t2 -> eutt_ RR r t1 t2.
Proof.
  revert t1 t2. pcofix CIH'. intros. destruct H0.
  genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
  assert (EM: notauF ot1 \/ notauF ot2 \/ ~(notauF ot1 \/ notauF ot2))
    by (destruct ot1, ot2; simpl; tauto).
  destruct EM as [EM|[EM|EM]].
  - destruct FIN as [FIN _].
    hexploit FIN; eauto 7. clear FIN; intro FIN.
    destruct FIN as [ot' [UNTAUS NOTAU]].
    hexploit EQV; eauto. intros EQNT.
    induction UNTAUS; subst.
    { pfold. inv EQNT; eauto. }
    hexploit IHUNTAUS; eauto.
    { intros. destruct UNTAUS1.
      dependent destruction H; [|subst; contradiction].
      hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
    }
    intros EUTT. punfold EUTT.
  - destruct FIN as [_ FIN].
    hexploit FIN; eauto 7. clear FIN; intro FIN.
    destruct FIN as [ot' [UNTAUS NOTAU]].
    hexploit EQV; eauto. intros EQNT.
    induction UNTAUS; subst.
    { pfold. inv EQNT; eauto. }
    hexploit IHUNTAUS; eauto.
    { intros. destruct UNTAUS2.
      dependent destruction H; [|subst; contradiction].
      hexploit @unalltaus_injective; [|econstructor|]; eauto. intros; subst; eauto.
    }
    intros EUTT. punfold EUTT.
  - destruct ot1, ot2; simpl in *; try tauto.
    pfold. econstructor. right. apply CIH'.
    econstructor.
    + rewrite !finite_taus_tau in FIN. eauto.
    + eauto using unalltaus_tau'.
Qed.

Lemma eutt__impl_euttE_ r t1 t2 :
  @eutt_ E R1 R2 RR r t1 t2 -> euttE_ RR r t1 t2.
Proof.
  intros. punfold H. econstructor; intros.
  - split; intros.
    + genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
      destruct H0 as [ot' [UNTAUS NOTAU]].
      move UNTAUS before r. revert_until UNTAUS.
      induction UNTAUS; intros.
      * induction H; eauto; try contradiction.
        rewrite finite_taus_tau. eauto.
      * induction H; eauto 7; try inv OBS; pclearbot
        ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
        punfold EQTAUS.
   + genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
     destruct H0 as [ot' [UNTAUS NOTAU]].
     move UNTAUS before r. revert_until UNTAUS.
     induction UNTAUS; intros.
     * induction H; eauto; try contradiction.
       rewrite finite_taus_tau. eauto.
     * induction H; eauto 7; try inv OBS; pclearbot
       ; rewrite ?finite_taus_tau; eauto; eapply IHUNTAUS; eauto.
       punfold EQTAUS.
  - genobs t1 ot1. genobs t2 ot2. clear Heqot1 t1 Heqot2 t2.
    destruct UNTAUS1 as [UNTAUS1 NT1]. destruct UNTAUS2 as [UNTAUS2 NT2].
    move UNTAUS2 before r. move UNTAUS1 before r. revert_until UNTAUS1.
    induction UNTAUS1.
    + induction 1; intros.
      * inv H; try contradiction; eauto.
      * subst. inv H; try contradiction. eauto.
    + induction 1; intros; subst.
      * inv H; try contradiction; eauto.
      * inv H; try contradiction; eauto.
        pclearbot. eapply IHUNTAUS1; eauto.
        punfold EQTAUS.
Qed.

Lemma eutt__is_euttE_ r t1 t2 :
  @eutt_ E R1 R2 RR r t1 t2 <-> euttE_ RR r t1 t2.
Proof. split; eauto using euttE__impl_eutt_, eutt__impl_euttE_. Qed.

Lemma euttE_impl_eutt r t1 t2 :
  paco2 (@euttE_ E R1 R2 RR) r t1 t2 -> paco2 (eutt_ RR) r t1 t2.
Proof.
  split; intros; eapply paco2_mon_gen; eauto; intros; apply euttE__impl_eutt_; eauto.
Qed.

Lemma eutt_impl_euttE r t1 t2 :
  paco2 (@eutt_ E R1 R2 RR) r t1 t2 -> paco2 (euttE_ RR) r t1 t2.
Proof.
  split; intros; eapply paco2_mon_gen; eauto; intros; apply eutt__impl_euttE_; eauto.
Qed.

Lemma eutt_is_euttE r t1 t2 :
  paco2 (@eutt_ E R1 R2 RR) r t1 t2 <-> paco2 (euttE_ RR) r t1 t2.
Proof. split; eauto using euttE_impl_eutt, eutt_impl_euttE. Qed.

End EUTT_eq_EUTTE.

Section EUTT_trans.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Ltac convert_eutt_to_euttE :=
  try (apply euttE__impl_eutt_ || apply euttE_impl_eutt);
  repeat match goal with [H: eutt_ _ _ _ _ |- _] => apply eutt__impl_euttE_ in H end;
  repeat match goal with [H: eutt _ _ _ |- _] => apply eutt_impl_euttE in H end.

Inductive eutt_trans_clo (r: itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| eutt_pre_clo_intro t1 t2 t3 t4
      (EQVl: t1 ≈ t2)
      (EQVr: t4 ≈ t3)
      (REL: r t2 t3)
  : eutt_trans_clo r t1 t4
.
Hint Constructors eutt_trans_clo.

Lemma eutt_clo_trans :
  weak_respectful2 (@eutt_ E R1 R2 RR) eutt_trans_clo.
Proof.
  econstructor; [pmonauto|].
  intros. destruct PR.
  convert_eutt_to_euttE.
  destruct (euttE_clo_trans E _ _ RR). clear WEAK_MON.
  hexploit WEAK_RESPECTFUL.
  { apply LE. }
  { intros. apply GF in PR. convert_eutt_to_euttE. auto. }
  { econstructor; [apply EQVl|apply EQVr|apply REL]. }
  intros EUTT.
  eapply monotone_euttE_; eauto; intros.
  eapply rclo2_mon_gen; eauto; intros.
  - convert_eutt_to_euttE. auto.
  - destruct PR0. econstructor; convert_eutt_to_euttE; eauto.
Qed.

Global Instance eutt_cong_eutt r :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (paco2 (@eutt_ E R1 R2 RR ∘ gres2 (eutt_ RR)) r).
Proof.
  repeat intro. pupto2 eutt_clo_trans. eauto.
Qed.

Global Instance eutt_cong_gres_eutt_ r :
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gres2 (@eutt_ E R1 R2 RR) r).
Proof.
  repeat intro. pupto2 eutt_clo_trans. eauto.
Qed.

Global Instance eutt_eq_under_rr_impl :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> flip impl) (eutt RR).
Proof.
  repeat red. intros. pupto2_init. rewrite H, H0. pupto2_final. eauto.
Qed.

End EUTT_trans.

Arguments eutt_clo_trans : clear implicits.
Hint Constructors eutt_trans_clo.

Section EUTT_nested_trans.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive eutt_nested_trans_clo (r: itree' E R1 -> itree' E R2 -> Prop) :
  itree' E R1 -> itree' E R2 -> Prop :=
| eutt_nested_pre_clo_intro ot1 ot2 ot3 ot4
      (EQVl: go ot1 ≅ go ot2)
      (EQVr: go ot4 ≅ go ot3)
      (REL: r ot2 ot3)
  : eutt_nested_trans_clo r ot1 ot4
.
Hint Constructors eutt_nested_trans_clo.

Lemma eutt_nested_clo_trans r :
  weak_respectful2 (euttF RR (gres2 (eutt_ RR) (upaco2 (eutt_ RR ∘ gres2 (eutt_ RR)) r)))
                    eutt_nested_trans_clo.
Proof.
  econstructor; [pmonauto|].
  intros. destruct PR.
  apply GF in REL. clear l LE GF.
  punfold EQVl; red in EQVl. punfold EQVr; red in EQVr. simpl in *.
  move REL before r0. revert_until REL.
  induction REL; intros; subst;
    try (dependent destruction EQVl; dependent destruction EQVr; [ idtac ]; pclearbot).
  - eauto.
  - econstructor. intros. rewrite REL, REL0. eauto.
  - econstructor. eapply rclo2_step. econstructor.
    + rewrite REL. reflexivity.
    + rewrite REL0. reflexivity.
    + eauto using rclo2.
  - dependent destruction EQVl; pclearbot. punfold REL0.
  - dependent destruction EQVr; pclearbot. punfold REL0.
Qed.

Global Instance eq_cong_nested_euttF r r0 :
  Proper (going (eq_itree eq) ==> going (eq_itree eq) ==> flip impl)
         (paco2 (@euttF E R1 R2 RR (gres2 (eutt_ RR) (upaco2 (eutt_ RR ∘ gres2 (eutt_ RR)) r))
                 ∘ gres2 (euttF RR (gres2 (eutt_ RR) (upaco2 (eutt_ RR ∘ gres2 (eutt_ RR)) r)))) r0).
Proof.
  repeat intro. destruct H, H0.
  pupto2 eutt_nested_clo_trans. econstructor; eauto.
Qed.

End EUTT_nested_trans.

Arguments eutt_nested_clo_trans : clear implicits.
Hint Constructors eutt_nested_trans_clo.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Let eutt : itree E R -> itree E R -> Prop := eutt eq.

Global Instance subrelation_observing_eutt:
  @subrelation (itree E R) (observing eq) eutt.
Proof.
  repeat intro. eapply subrelation_eq_eutt, observing_eq_itree_eq. eauto.
Qed.

Global Instance Reflexive_eutt: Reflexive eutt.
Proof. apply Reflexive_eutt_gen; eauto. Qed.

Global Instance Symmetric_eutt: Symmetric eutt.
Proof. apply Symmetric_eutt_gen; eauto. Qed.

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  unfold eutt. repeat intro. pupto2_init.
  rewrite H, H0. pupto2_final. apply Reflexive_eutt.
Qed.

(* We can now rewrite with [eutt] equalities. *)
Global Instance Equivalence_eutt : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

Global Instance eutt_cong_go : Proper (going eutt ==> eutt) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance eutt_cong_observe : Proper (eutt ==> going eutt) observe.
Proof.
  constructor. punfold H. pfold. destruct H. econstructor; eauto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. pfold. pfold. econstructor. punfold H.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof. 
  constructor. pfold. pfold. econstructor.
  intros. specialize (H x0). punfold H.
Qed.

End EUTT_eq.

(**)

Lemma eutt_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros. pfold. pfold. econstructor. punfold H.
Qed.

Lemma eutt_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eutt RR (k1 u) (k2 u)) ->
  eutt RR (Vis e k1) (Vis e k2).
Proof.
  intros. pfold. pfold. econstructor. intros. specialize (H x). punfold H.
Qed.

Lemma eutt_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 -> @eutt E R1 R2 RR (Ret r1) (Ret r2).
Proof.
  intros. pfold. pfold. econstructor. eauto.
Qed.

Global Instance eutt_bind {E S R} :
  Proper (eutt eq ==>
          pointwise_relation _ (eutt eq) ==>
          eutt eq) (@ITree.bind E R S).
Proof.
  repeat intro. do 2 punfold H.
  revert_until S. pcofix CIH. intros.
  pfold. revert_until CIH. pcofix CIH'. intros. pfold.
  rewrite !unfold_bind. genobs_clear x ox. genobs_clear y oy.
  move H0 before CIH'. revert_until H0.
  induction H0; intros; subst; pclearbot.
  - simpl. specialize (H1 r2). do 2 punfold H1.
    eauto 7 using euttF_mon, upaco2_mon_bot.
  - econstructor. intros.
    specialize (EUTTK x). do 2 punfold EUTTK.
  - econstructor. intros. punfold EQTAUS.
  - econstructor. rewrite unfold_bind. eauto.
  - econstructor. rewrite unfold_bind. eauto.
Qed.

Global Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt eq ==> eutt eq) (@ITree.map E R S).
Proof.
  unfold ITree.map. do 3 red. intros.
  rewrite H0. setoid_rewrite H. reflexivity.
Qed.

Global Instance eutt_forever {E R S} :
  Proper (eutt eq ==> eutt eq) (@ITree.forever E R S).
Proof.
  cut (forall X (t1 t2: itree E X) (x y: itree E R), t1 ≈ t2 -> x ≈ y -> (t1 ;; @ITree.forever E R S x) ≈ (t2 ;; ITree.forever y)).
  { repeat intro.
    rewrite <-(ret_bind tt (fun _ => ITree.forever x)).
    rewrite <-(ret_bind tt (fun _ => ITree.forever y)).
    eapply H; eauto; reflexivity.
  }

  pcofix CIH. intros. 
  pfold. revert_until CIH. pcofix CIH'. intros.
  do 2 punfold H0. pfold.
  rewrite !unfold_bind. genobs_clear t1 ot1. genobs_clear t2 ot2.
  induction H0; intros; subst; pclearbot; try (econstructor; eauto 7; fail).
  simpl. rewrite (unfold_forever x), (unfold_forever y). 
  econstructor. eauto 7.
Qed.

Global Instance eutt_when {E} (b : bool) :
  Proper (eutt eq ==> eutt eq) (@ITree.when E b).
Proof.
  repeat intro. destruct b; simpl; eauto. reflexivity.
Qed.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  pfold. pfold. econstructor. reflexivity.
Qed.
