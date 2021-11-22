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
    bot := ITree.spin;
  |}.

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
- cbn. apply strong_itree_approx_spin_bottom.
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

Section Fixable.
Context (E : Type -> Type).
Context (taa : forall {A B C : Type} (e1 : E A) (a : A) (e2 : E B) (k : B -> C) (default : C) , C).
Context (Htaa : test_and_apply_correct E taa).

Instance E_itree_cpo {R} : weak_cpo (itree E R) := itree_weak_cpo taa.
Instance E_itree_cpo_laws {R} : weak_cpo_laws (@E_itree_cpo R) := itree_weak_cpo_laws taa Htaa.

(*only talks about monotyped bind, thats a little weird *)
Lemma subst_mon R (k : R -> itree E R) : monotone_fun (ITree.subst k).
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
    + rewrite H2. Admitted.


Lemma subst_scott_cont R (k : R -> itree E R) : scott_continuous (ITree.subst k).
Proof.
  red. cbn. unfold monotone_seq. cbn. ginit. gcofix CIH. intros seq Hmon.
  assert (strong_itree_approx eq (seq 0) (seq 1) ). auto.
  pinversion H; use_simpobs.
  - unfold map. rewrite sup_head_ret; eauto. setoid_rewrite bind_ret_l.
    subst.
    (* from here I can prove that seq n ≅ k r2 forall n, then can prove that the sup of a constant seq is the constant 
       val, then I am done, will require more meta theory, but nothing I haven't already though of*)
    admit.
  - unfold map. rewrite sup_head_vis; eauto. setoid_rewrite bind_vis.
    setoid_rewrite sup_head_vis. 2 : rewrite H0; setoid_rewrite bind_vis; reflexivity.
    gstep. constructor. 
    unfold ITree.bind. (*if I can commute peel vis with map ITree.subst then this should work out fine *)
    admit.
    (* gfinal. left. eapply CIH. *)
  - unfold map. rewrite sup_head_tau; eauto. setoid_rewrite bind_tau.
    setoid_rewrite sup_head_tau at 2.
    2 : { rewrite H0. setoid_rewrite bind_tau. reflexivity. }
    unfold ITree.bind. gstep. constructor. (*again need to move map ITree.subst to the front *) admit.
  - unfold map. rewrite sup_head_tau; eauto. setoid_rewrite bind_tau.
    setoid_rewrite sup_head_tau at 2.
    2 : { rewrite H0. setoid_rewrite bind_tau. reflexivity. }
    gstep. constructor. (*one again same *) admit.
Admitted.

End Fixable.
