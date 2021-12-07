From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Logic.Classical
.

Require Import Lia.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq
     CPO.CPO
     CPO.ITreeApprox
     CPO.ITreeApproxSup
.

From ExtLib Require Import
     Structures.Monad.

Global Instance itree_weak_cpo {R E} test_and_apply : weak_cpo (itree E R) :=
  {|
    weak_leq := weak_itree_approx eq;
    strong_leq := strong_itree_approx eq;
    sup := itree_approx_sup test_and_apply;
    weak_eq := eutt eq;
    strong_eq := eq_itree eq;
    
  |}.

Global Instance itree_pointed_weak_cpo {R E} test_and_apply : pointed_weak_cpo (@itree_weak_cpo R E test_and_apply) :=
  {| bot := ITree.spin |}.

Class test_and_apply_correct (E : Type -> Type) (taa :  forall {A B C : Type} (e1 : E A) (a : A) (e2 : E B) (k : B -> C) (default : C) , C) := 
  {
  test_and_apply_correct_eq : forall A C (e : E A) (a : A) (k : A -> C) (default : C), taa e a e k default = k a;
  test_and_apply_correct_type_eq : forall A C (e1 e2 : E A) (a : A) (k : A -> C) (default : C), taa e1 a e2 k default = k a;
  test_and_apply_correct_neq : forall A B C (e1 : E A) (e2 : E B) a k (default : C),
      ~ JMeq e1 e2 -> taa e1 a e2 k default = default;
  E_injective : forall A B, E A -> E B -> E A = E B -> A = B;
  }.

Global Instance itree_weak_cpo_laws {E : Type -> Type} {R} taa : test_and_apply_correct E taa -> weak_cpo_laws (@itree_weak_cpo R E taa). 
intros. econstructor. Unshelve.
- cbn. intros. split; intros.
  + rewrite H0. split; apply weak_itree_approx_refl.
  + destruct H0. apply weak_itree_approx_antisym; auto.
- cbn. split; intros.
  + rewrite H0. split; apply strong_itree_approx_refl.
  + destruct H0. apply strong_itree_approx_antisym; auto.
- cbn. intros.  rewrite H0. reflexivity.
- cbn. intros. apply strong_to_weak_itree_approx; auto.
- cbn. intros. red in H0. cbn in H0. constructor; auto.
  + cbn. intros. eapply sup_is_upper_bound; destruct H; eauto.
    constructor; red; intros; subst; auto.
  + intros. cbn in *. eapply sup_is_below_all_upper_bounds; destruct H; eauto.
    constructor; red; intros; subst; auto.
- intros seq1 seq2 Hseq. cbn in *. red in Hseq. cbn in *. 
  assert (fun_eq seq1 seq2). red. intros n1 n2 Hn; subst. auto.  
  eapply proper_fun_seq; destruct H; eauto.
- cbn. intros.  apply sup_advance_eutt; destruct H; eauto.
  constructor; red; intros; subst; auto.
- constructor. red. cbn. apply weak_itree_approx_refl.
  red. cbn. intros. eapply weak_itree_approx_mon with (RR1 := rcompose eq eq).
  intros. inv H2. auto. eapply weak_itree_approx_trans; eauto.
- constructor. red. cbn. apply strong_itree_approx_refl.
  red. cbn. intros. eapply strong_itree_approx_mon with (RR1 := rcompose eq eq).
  intros. inv H2. auto. eapply strong_itree_approx_trans; eauto.
Qed.

Global Instance itree_pointed_weak_cpo_laws {E : Type -> Type} {R} taa : test_and_apply_correct E taa -> pointed_weak_cpo_laws (@itree_weak_cpo R E taa) (@itree_pointed_weak_cpo R E taa).
Proof.
  intros. constructor. cbn. intros. eapply strong_itree_approx_spin_bottom.
Qed.

(*TODO move this to EuttDiv or something *)
Lemma bind_spin : forall E R S (k : R -> itree E S), @ITree.spin E S ≅ ITree.bind ITree.spin k.
Proof.
  ginit. gcofix CIH. intros. setoid_rewrite spin_cong_tau_spin.
  rewrite bind_tau. gstep. constructor. gfinal. left. auto.
Qed.

Section Fixable.
Context (E : Type -> Type).
Context (taa : forall {A B C : Type} (e1 : E A) (a : A) (e2 : E B) (k : B -> C) (default : C) , C).
Context (Htaa : test_and_apply_correct E taa).

Instance E_itree_cpo {R} : weak_cpo (itree E R) := itree_weak_cpo taa.
Instance E_itree_pointed_cpo {R} : pointed_weak_cpo (@E_itree_cpo R) := itree_pointed_weak_cpo taa.
Instance E_itree_cpo_laws {R} : weak_cpo_laws (@E_itree_cpo R) := itree_weak_cpo_laws taa Htaa.
Instance E_itree_pointed_cpo_laws {R} : pointed_weak_cpo_laws (@E_itree_cpo R) E_itree_pointed_cpo :=
  itree_pointed_weak_cpo_laws taa Htaa.

(*only talks about monotyped bind, thats a little weird *)
Lemma subst_mon R S (k : R -> itree E S) : monotone_fun (ITree.subst k).
Proof.
  red. cbn. pcofix CIH. intros t1 t2 Ht. punfold Ht. red in Ht.
  pfold. red. unfold observe. cbn. inv Ht; eauto.
  - assert (strong_itree_approx eq (k r2) (k r2) ). apply strong_itree_approx_refl.
    assert (paco2 (strong_itree_approx_ eq id) r (k r2) (k r2)  ).
    eapply paco2_mon; eauto; intros; contradiction. punfold H2.
  - constructor. right. pclearbot. eapply CIH; eauto.
  - constructor. right. pclearbot. eapply CIH; eauto.
  - match goal with |- (strong_itree_approxF eq (upaco2 (strong_itree_approx_ eq id) r) id) ?ot1 (_observe ?t2) => 
                    remember t2 as t end.
    enough (strong_itree_approx eq (Tau (ITree.subst k t0) ) t ).
    + assert (paco2 (strong_itree_approx_ eq id) r (Tau (ITree.subst k t0) ) t  ). 
      eapply paco2_mon; eauto; intros; contradiction. punfold H4.
    + rewrite H2. setoid_rewrite <- bind_spin. rewrite <- spin_cong_tau_spin.
      apply strong_itree_approx_spin_bottom.
Qed.

(* For some reason it wasn't finding this instance so I redeclared it *)
Instance peel_vis_elem_proper'
     : forall R (A0 : Type) (e0 : E A0) (a0 : A0),
       Proper (@eq_itree E R R eq ==> eq_itree eq) (peel_vis_elem taa e0 a0).
Proof. intros. destruct Htaa. eapply peel_vis_elem_proper; eauto. Qed.

Instance proper_fun_seq' R : Proper (fun_eq ==> @eq_itree E R R eq) (itree_approx_sup taa).
Proof.
  eapply proper_fun_seq; destruct Htaa; eauto.
Qed.

Instance proper_fun_seq_peel_vis' : forall R (A : Type) (e : E A) (a : A),
  Proper (@fun_eq E nat R ==> fun_eq) (peel_vis taa e a).
Proof. intros. eapply proper_fun_seq_peel_vis; destruct Htaa; auto. Qed.

(* TODO move to other file *)
Lemma weak_itree_approx_ret_spin:
     forall (R : Type) (r : R), ~ weak_itree_approx eq (Ret r) (@ITree.spin E R).
Proof.
  intros R r Hcontra. punfold Hcontra. red in Hcontra.
  cbn in *. remember (RetF r) as x. remember (TauF ITree.spin) as y.
  hinduction Hcontra before E; intros; inv Heqx; inv Heqy; eauto.
Qed.

Lemma subst_scott_cont_aux_ret1 : forall (R : Type) (r : R) (seq : sequence (itree E R) ),
    supremum seq (Ret r) -> ~ forall n, ~ seq n ≈ Ret r.
Proof.
  intros R r seq Hseq Hcontra. destruct Hseq.
  specialize (Hlub ITree.spin).
  assert (~ weak_itree_approx eq (Ret r) (@ITree.spin E R) ).
  apply weak_itree_approx_ret_spin. apply H. 
  apply Hlub. red in Hmon. cbn in *. intros n.
  specialize (Hub n). assert (~ seq n ≈ Ret r). auto.
  assert (seq n ≈ ITree.spin).
  {
    remember (seq n) as t. ginit. clear Heqt. generalize dependent t.
    gcofix CIH. intros. punfold Hub. red in Hub.
    cbn in *. remember (observe t) as ot. remember (RetF r) as y.
    hinduction Hub before r; intros; inv Heqy; use_simpobs; eauto.
    - rewrite Heqot in H1. exfalso. apply H1. reflexivity.
    - rewrite Heqot. cbn in *. gstep. red. cbn. constructor.
      gfinal. left. pclearbot. eapply CIH; eauto.
      + rewrite <- itree_eta. auto.
      + rewrite Heqot in H1. rewrite tau_eutt in H1. auto.
  }
  rewrite H1. apply weak_itree_approx_spin_bottom.
Qed.

Lemma subst_scott_cont_aux_ret2 : forall (R : Type) (r : R) (seq : sequence (itree E R) ),
    supremum seq (Ret r) -> exists n, seq n ≈ Ret r.
Proof.
  intros. apply subst_scott_cont_aux_ret1 in H.
  destruct (classic (exists n, seq n ≈ Ret r) ); auto.
  exfalso. apply H. intros. intro Hcontra.
  apply H0. exists n. eauto.
Qed.

Lemma peel_vis_supremum_eq_itree : forall (R X : Type) (seq : sequence (itree E R)) (e : E X) (k : X -> itree E R), itree_approx_sup taa seq ≅ Vis e k -> forall a, itree_approx_sup taa (peel_vis taa e a seq) ≅ (k a).
Proof.
  intros. 
  destruct (observe (seq 0) ) eqn : Hseq0; symmetry in Hseq0; use_simpobs.
  - rewrite sup_head_ret in H; eauto. pinversion H.
  - rewrite sup_head_tau in H; eauto. pinversion H; inv CHECK.
  - rewrite sup_head_vis in H; eauto.
    assert (X = X0). pinversion H; inj_existT; subst; auto.
    subst. assert (e0 = e). pinversion H; inj_existT; subst; auto.
    subst. eapply eqit_inv_Vis in H. Unshelve. 2 : apply a. auto.
Qed.

Lemma peel_vis_supremum_aux : forall (R X : Type) (seq : sequence (itree E R)) (e : E X) (k : X -> itree E R), 
    monotone_approx eq seq ->
    itree_approx_sup taa seq ≈ Vis e k -> forall a, itree_approx_sup taa (peel_vis taa e a seq) ≈ (k a).
Proof.
  intros R X. intros seq e k Hseq H a. 
  punfold H. red in H. cbn in *. remember (observe (itree_approx_sup taa seq) ) as x.
  assert (go x ≅ itree_approx_sup taa seq). subst. rewrite <- itree_eta. reflexivity.
  clear Heqx.
  remember (VisF e k) as y.
  hinduction H before E; intros; inv Heqy; inj_existT; subst; use_simpobs.
  - pclearbot. rename H0 into Heqx. destruct (observe (seq 0) ) eqn : Hseq0; symmetry in Hseq0; use_simpobs.
    + rewrite sup_head_ret in Heqx; eauto. pinversion Heqx.
    + rewrite sup_head_tau in Heqx; eauto. pinversion Heqx; inv CHECK.
    + rewrite sup_head_vis in Heqx; eauto.
      assert (X = X0). pinversion Heqx; inj_existT; subst; auto.
      subst. assert (e0 = e). pinversion Heqx; inj_existT; subst; auto.
      subst. eapply eqit_inv_Vis in Heqx. Unshelve. 2 : apply a.
      rewrite <- Heqx. auto.
  - pclearbot. rename H0 into Heqx. destruct (observe (seq 0) ) eqn : Hseq0; symmetry in Hseq0; use_simpobs.
    + rewrite sup_head_ret in Heqx; eauto. pinversion Heqx; inv CHECK0.
    + rewrite sup_head_tau in Heqx; eauto. pinversion Heqx; try inv CHECK0. subst.
      rewrite sup_advance_eutt. all : try (destruct Htaa; auto; fail).
      2 : constructor; red; intros; subst; auto.
      2 : apply peel_vis_preserves_monotone_approx; destruct Htaa; auto.
      rewrite <- sup_peel_tau_eutt. all : try (destruct Htaa; auto; fail).
      2 : constructor; red; intros; subst; auto.
      2 : apply peel_vis_preserves_monotone_approx; destruct Htaa; auto; apply advance_preserves_monotone_approx; destruct Htaa; auto.
      assert (fun_eq (peel_tau (advance (peel_vis taa e a seq))) (peel_vis taa e a (peel_tau (advance seq) ) ) ).
      { repeat intro; subst. unfold advance, peel_tau, peel_vis.
        specialize (@commute_peel_vis_peel_tau) as Hcom. do 2 red in Hcom.
        unfold peel_vis, peel_tau in Hcom. rewrite Hcom; eauto. reflexivity.
        all : destruct Htaa; auto. }
      rewrite H0. eapply IHeqitF; eauto. apply peel_tau_preserves_monotone_approx. apply advance_preserves_monotone_approx. auto.
      rewrite <- itree_eta. auto.
    + rewrite sup_head_vis in Heqx; eauto. pinversion Heqx; inv CHECK0.
Abort. (* there is some really weird problem with a failure to unify terms here, maybe I need to reduce this to a core
             problem. I honestly have no idea if I did something wrong or if it is a bug in Coq
             I found a way around this but wtf
           *)

Variant sup_spec {R} (sup : sequence (itree E R) -> itree E R ) : Prop :=
  | sup_correct (Hret : forall (seq : sequence (itree E R)) r, seq 0 ≅ Ret r -> sup seq ≅ Ret r)
                (Htau : forall seq t, seq 0 ≅ Tau t -> sup seq ≅ Tau (sup (peel_tau (advance seq))) )
                (Hvis : forall seq  X (e : E X) k, seq 0 ≅ Vis e k -> sup seq ≅ Vis e (fun a => sup (peel_vis taa e a seq) ) )
                (Hadv : forall seq, monotone_approx eq seq -> sup seq ≈ sup (advance seq))
                (Hpeel_tau : forall seq, monotone_approx eq seq -> sup (peel_tau seq) ≈ sup seq  )
                (Hprop : Proper (fun_eq ==> eq_itree eq) sup )
.

Lemma peel_vis_supremum_aux' : forall (R X : Type) (seq : sequence (itree E R)) (e : E X) (k : X -> itree E R)
  (sup : sequence (itree E R) -> itree E R ), 
    monotone_approx eq seq ->
    sup_spec sup ->
    sup seq ≈ Vis e k -> forall a, sup (peel_vis taa e a seq) ≈ (k a).
Proof.
  intros R X. intros seq e k sup Hseq Hsup H a. 
  destruct Hsup. rename Hret into sup_head_ret. rename Htau into sup_head_tau.
  rename Hvis into sup_head_vis. rename Hadv into sup_advance_eutt.
  rename Hpeel_tau into sup_peel_tau_eutt.
  punfold H. red in H. cbn in *. remember (observe (sup seq) ) as x.
  assert (go x ≅ sup seq). subst. rewrite <- itree_eta. reflexivity.
  clear Heqx.
  remember (VisF e k) as y.
  hinduction H before E; intros; inv Heqy; inj_existT; subst; use_simpobs.
  - pclearbot. rename H0 into Heqx. destruct (observe (seq 0) ) eqn : Hseq0; symmetry in Hseq0; use_simpobs.
    + rewrite sup_head_ret in Heqx; eauto. pinversion Heqx.
    + rewrite sup_head_tau in Heqx; eauto. pinversion Heqx; inv CHECK.
    + rewrite sup_head_vis in Heqx; eauto.
      assert (X = X0). pinversion Heqx; inj_existT; subst; auto.
      subst. assert (e0 = e). pinversion Heqx; inj_existT; subst; auto.
      subst. eapply eqit_inv_Vis in Heqx. Unshelve. 2 : apply a.
      rewrite <- Heqx. auto.
  - pclearbot. rename H0 into Heqx. destruct (observe (seq 0) ) eqn : Hseq0; symmetry in Hseq0; use_simpobs.
    + rewrite sup_head_ret in Heqx; eauto. pinversion Heqx; inv CHECK0.
    + rewrite sup_head_tau in Heqx; eauto. pinversion Heqx; try inv CHECK0. subst.
      rewrite sup_advance_eutt. 
      2 : apply peel_vis_preserves_monotone_approx; destruct Htaa; auto.
      rewrite <- sup_peel_tau_eutt. 
      2 : apply peel_vis_preserves_monotone_approx; destruct Htaa; auto; apply advance_preserves_monotone_approx; destruct Htaa; auto.
      assert (fun_eq (peel_tau (advance (peel_vis taa e a seq))) (peel_vis taa e a (peel_tau (advance seq) ) ) ).
      { repeat intro; subst. unfold advance, peel_tau, peel_vis.
        specialize (@commute_peel_vis_peel_tau) as Hcom. do 2 red in Hcom.
        unfold peel_vis, peel_tau in Hcom. rewrite Hcom; eauto. reflexivity.
        all : destruct Htaa; auto. }
      rewrite H0. eapply IHeqitF; eauto. apply peel_tau_preserves_monotone_approx. apply advance_preserves_monotone_approx. auto.
      rewrite <- itree_eta. auto.
    + rewrite sup_head_vis in Heqx; eauto. pinversion Heqx; inv CHECK0. 
Qed.

Lemma peel_vis_supremum_aux : forall (R X : Type) (seq : sequence (itree E R)) (e : E X) (k : X -> itree E R), 
    monotone_approx eq seq ->
    itree_approx_sup taa seq ≈ Vis e k -> forall a, itree_approx_sup taa (peel_vis taa e a seq) ≈ (k a).
Proof.
  intros. apply peel_vis_supremum_aux'; auto. constructor.
  - apply sup_head_ret.
  - apply sup_head_tau.
  - apply sup_head_vis.
  - apply sup_advance_eutt. all : destruct Htaa; auto.
    constructor; repeat red; intros; subst; auto.
  - apply sup_peel_tau_eutt. all : destruct Htaa; auto.
    constructor; repeat red; intros; subst; auto.
  - apply proper_fun_seq'.
Qed. 

(*should be able to rely on peel_vis_supremum_aux for this, or maybe not*)
Lemma peel_vis_supremum:
  forall (R X : Type) (seq : sequence (itree E R)) (e : E X) (k : X -> itree E R) (a : X),
    supremum seq (Vis e k) -> supremum (peel_vis taa e a seq) (k a).
Proof.
  intros R X seq e k a Hseq.
  assert (monotone_seq seq). destruct Hseq; auto.
  eapply CPO.sup_correct in H. 
  assert (weak_eq (sup seq) (Vis e k)). eapply supremum_unique; eauto. apply E_itree_cpo_laws.
  cbn in H0. eapply peel_vis_supremum_aux in H0. Unshelve. 3 : apply a.
  2 : destruct Hseq; auto. symmetry in H0. assert (weak_eq (k a) (sup (peel_vis taa e a seq)) ).  cbn. auto. rewrite H1. apply CPO.sup_correct. red. cbn. intros.
  apply peel_vis_preserves_monotone_approx; destruct Htaa; auto. destruct H; auto.
Qed.

Lemma peel_vis_upper_bound_aux:
  forall (R S : Type) (k : R -> itree E S) (X : Type) (k2 : X -> itree E S)
    (seq : sequence (itree E R)) (e0 : E X) (k0 : X -> itree E R),
    (forall n : nat, weak_itree_approx eq (seq n) (Vis e0 k0)) ->
    forall (a : X) (n : nat),
      weak_itree_approx eq (map (ITree.subst k) seq n) (Vis e0 k2) ->
      weak_itree_approx eq (map (ITree.subst k) (peel_vis taa e0 a seq) n) (k2 a).
Proof.
  intros R S k X k2. unfold peel_vis. unfold map. intros.
  specialize (H n) as Hn. remember (seq n) as t. clear Heqt n.
  generalize dependent t. ginit. gcofix CIH. intros t Hek2 Ht.
  punfold Ht. red in Ht. remember (observe t) as ot. cbn in Ht.
  remember (VisF e0 k0) as y. hinduction Ht before r; intros; inv Heqy; inj_existT; subst; use_simpobs.
  - rewrite Heqot. rewrite peel_vis_elem_vis_eq. 2 : destruct Htaa; auto.
    pclearbot. rewrite Heqot in Hek2. setoid_rewrite bind_vis in Hek2.
    pinversion Hek2; inj_existT; subst; use_simpobs.
    gfinal. right. eapply paco2_mon; eauto; intros; contradiction.
  - rewrite Heqot. pclearbot. rewrite peel_vis_elem_tau. setoid_rewrite bind_tau.
    gstep. constructor. gfinal. left. eapply CIH.
    + rewrite Heqot in Hek2. rewrite tau_eutt in Hek2. auto.
    + rewrite <- itree_eta. auto.
Qed.

Lemma subst_scott_cont_vis_seq_aux:
  forall (R : Type) (seq : sequence (itree E R)) (X : Type) (e : E X) (k0 : X -> itree E R),
    supremum seq (Vis e k0) ->
    exists (n : nat) (kn : X -> itree E R),
      seq n ≈ Vis e kn.
Proof.
  intros R seq X e k0 H. 
  enough (~ forall n kn, ~ (seq n ≈ Vis e kn)).
  { match goal with |- ?g => destruct (classic g); auto end.
    exfalso. apply H0. intros. intro. apply H1. eauto. }
  intro Hcontra.
  destruct H. cbn in *.
  assert (forall n, seq n ≈ ITree.spin).
  { intros. specialize (Hub n). specialize (Hcontra n).
    remember (seq n) as t. clear Heqt. generalize dependent t.
    ginit. gcofix CIH. intros.
    punfold Hub. red in Hub. cbn in *. remember (observe t) as ot.
    remember (VisF e k0) as y. hinduction Hub before r; intros; inv Heqy;
                                 inj_existT; subst; use_simpobs.
    + exfalso. eapply Hcontra. rewrite Heqot. reflexivity.
    + rewrite Heqot. gstep. red. cbn. constructor. gfinal. left. eapply CIH.
      * pclearbot. rewrite <- itree_eta. auto.
      * intros. intro. eapply Hcontra. rewrite Heqot. rewrite tau_eutt.
        eauto.
  }
  specialize (Hlub ITree.spin). setoid_rewrite H in Hlub. 
  assert (weak_itree_approx eq (Vis e k0) ITree.spin).
  { apply Hlub. intros. apply weak_itree_approx_refl. }
  punfold H0. red in H0. cbn in *. remember (VisF e k0) as x.
  remember (TauF ITree.spin) as y. 
  hinduction H0 before R; intros; inv Heqx; inv Heqy; inj_existT; subst; eauto.
Qed.

Lemma subst_scott_cont_aux : forall (R S : Type) (k : R -> itree E S) (t : itree E R) 
                               (seq : sequence (itree E R)),
    supremum seq t -> supremum (map (ITree.subst k) seq ) (ITree.subst k t).
Proof.
  intros. destruct H. constructor; cbn.
  - red. cbn. intros. apply subst_mon. auto.
  - intros. unfold map. eapply weak_itree_approx_bind; cbn in *; eauto.
    intros; subst. apply weak_itree_approx_refl.
  - cbn in *. intros. generalize dependent t. generalize dependent seq. revert upper_bound.
    ginit. gcofix CIH. intros.
    destruct (observe t) eqn : Ht; symmetry in Ht; use_simpobs.
    + rewrite Ht. setoid_rewrite bind_ret_l.
      setoid_rewrite Ht in Hub.
      unfold map in H0. setoid_rewrite Ht in Hlub.
      clear CIH. enough (weak_itree_approx eq (k r0) upper_bound ).
      { gfinal. right. eapply paco2_mon; eauto; intros; contradiction. }
      assert (supremum seq (Ret r0) ). constructor; eauto.
      apply subst_scott_cont_aux_ret2 in H. destruct H as [n Hn].
      specialize (H0 n). rewrite Hn in H0. setoid_rewrite bind_ret_l in H0. auto.
    + rewrite Ht. setoid_rewrite bind_tau. gstep. constructor.
      gfinal. left. eapply CIH; eauto.
      * setoid_rewrite Ht in Hub. setoid_rewrite tau_eutt in Hub. auto.
      * intros. setoid_rewrite Ht in Hlub. setoid_rewrite tau_eutt in Hlub.
        eauto.
    + rewrite Ht. setoid_rewrite bind_vis.
      (* from here I show that all seq n must be eutt to Vis e k with some properties on k
         then can rewrite that into H and induct to show that upperbound must have some e
         actually there is a complication because I know there exists some n where seq n has that prop 
         (actually infinitely many but one is all I need)
       *)
      assert (exists (n : nat), exists kn, seq n ≈ Vis e kn /\ (forall a, weak_itree_approx eq (kn a) (k0 a) )  ).
      assert (supremum seq (Vis e k0)).
      setoid_rewrite Ht in Hub. setoid_rewrite Ht in Hlub. constructor; auto.
      apply subst_scott_cont_vis_seq_aux in H.
      decompose record H. eexists. eexists. split; eauto.
      specialize (Hub x). rewrite H2 in Hub. rewrite Ht in Hub.
      pinversion Hub. inj_existT. subst. auto.
      decompose record H. rename x0 into kn. specialize (H0 x) as Hx.
      unfold map in Hx. rewrite H1 in Hx. setoid_rewrite bind_vis in Hx.
      punfold Hx. red in Hx. cbn in *. remember (VisF e (fun x : X => ITree.bind (kn x) k)) as y.
      remember (observe upper_bound) as oub. hinduction Hx before r; intros;
                                               inv Heqy; inj_existT; use_simpobs; subst.
      * rewrite Heqoub. gstep. constructor. gfinal. pclearbot. left. 
        eapply CIH with (seq := peel_vis taa e0 a seq); eauto.
        -- apply peel_vis_preserves_monotone_approx; destruct Htaa; eauto.
        -- setoid_rewrite Heqoub in H0. rename H0 into Hseq.
           intros n. 
           specialize (Hseq n) as Hseqn. 
           setoid_rewrite Ht in Hub. 
           eapply peel_vis_upper_bound_aux; eauto.
        -- intros. 
           assert (supremum seq (Vis e0 k0)).
           setoid_rewrite Ht in Hub. setoid_rewrite Ht in Hlub. constructor; auto.
           eapply peel_vis_supremum in H4. destruct H4; cbn in *; eauto.
        -- intros. 
           setoid_rewrite Ht in Hlub.
           assert (supremum seq (Vis e0 k0) ).
           constructor; auto. setoid_rewrite <- Ht. auto.
           assert (supremum (peel_vis taa e0 a seq) (k0 a) ).
           apply peel_vis_supremum; auto.
           destruct H6. eapply Hlub0. apply H4.
      * rewrite Heqoub. rewrite tau_euttge. eapply IHHx; eauto.
        setoid_rewrite Heqoub in H0. setoid_rewrite tau_eutt in H0. auto.
Qed.

Lemma subst_scott_cont R S (k : R -> itree E S) : scott_continuous (ITree.subst k).
Proof.
  red. intros seq Hmon. eapply CPO.sup_correct in Hmon as Hsup.
  eapply subst_scott_cont_aux in Hsup. Unshelve. all : auto.
  eapply supremum_unique; eauto. apply itree_weak_cpo_laws; auto.
  apply CPO.sup_correct. red. cbn. intros.
  cbn. unfold map. eapply subst_mon. auto.
Qed.

Lemma subst_seq_unfold R S (k : R -> itree E S) (seq : sequence (itree E R) ) : 
  monotone_seq seq ->
  sup (map (ITree.subst k) seq ) ≈ ITree.subst k (sup seq).
Proof.
  intros H. specialize (subst_scott_cont R S k) as Hscott.
  red in Hscott. cbn in *. setoid_rewrite Hscott; auto. reflexivity.
Qed.

(*Lemma subst_scott_cont_gen R S U (k : R -> itree E S -> itree E U) *)


End Fixable.
