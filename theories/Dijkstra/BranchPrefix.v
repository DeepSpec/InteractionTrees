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
     Logic.IndefiniteDescription
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     EuttEv
     Divergence
     Dijkstra.IBranch
     Dijkstra.EuttDiv
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive branch_prefixF {E : Type -> Type} {R S : Type} (F : ibranch E R -> ibranch E S -> Prop) : ibranch' E R -> ibranch' E S ->  Prop :=
  | ret_prefix (r : R) (b : ibranch E S) : branch_prefixF F (RetF r) (observe b)
  | tau_prefix (br : ibranch E R) (bs : ibranch E S) : F br bs -> branch_prefixF F (TauF br) (TauF bs)
  | tau_r_prefix (br : ibranch E R) (obs : ibranch' E S) : branch_prefixF F (observe br) obs -> branch_prefixF F (TauF br) obs
  | tau_l_prefix (obr : ibranch' E R) (bs : ibranch E S) : branch_prefixF F (obr) (observe bs) -> branch_prefixF F (obr) (TauF bs)
  | tau_vis_empty {A : Type} (e : E A) (H: A -> void) (kr : void -> ibranch E R) (ks : void -> ibranch E S) : 
      branch_prefixF F (VisF (evempty A H e) kr) (VisF (evempty A H e) ks )
  | tau_vis_ans {A : Type} (e : E A) (ans : A) (kr : unit -> ibranch E R) (ks : unit -> ibranch E S) :
      F (kr tt) (ks tt) -> branch_prefixF F (VisF (evans A e ans) kr ) (VisF (evans A e ans) ks)
.

Hint Constructors branch_prefixF.

Definition branch_prefix_ {E R S} F (br : ibranch E R) (bs : ibranch E S) := branch_prefixF F (observe br) (observe bs).

Hint Unfold branch_prefix_.

Lemma branch_prefix_monot {E R S} : monotone2 (@branch_prefix_ E R S).
Proof.
  repeat intro. red. red in IN. induction IN; eauto.
Qed.

Hint Resolve branch_prefix_monot : paco.

Definition branch_prefix {E R S} : ibranch E R -> ibranch E S -> Prop := paco2 branch_prefix_ bot2.

Lemma prefix_vis : forall E R S A (e : E A) (ans : A) (k : unit -> ibranch E R) (t : ibranch E S), 
                     branch_prefix (Vis (evans _ e ans) k ) t -> exists k', (t ≈ Vis (evans _ e ans) k' )%itree.
Proof.
  intros E R S A e ans k t Hbp. punfold Hbp. red in Hbp. cbn in *.
  dependent induction Hbp.
  - apply simpobs in x. enough (exists k', bs ≈ (Vis (evans A e ans) k' ))%itree.
    + destruct H as [k' Hk']. exists k'. rewrite x. rewrite tau_eutt. auto.
    + eapply IHHbp; eauto.
  - exists ks. apply simpobs in x. rewrite x. reflexivity.
Qed.

Lemma branch_prefix_ret : forall E R S F (ob : ibranch' E S) (r : R), branch_prefixF F (RetF r) ob.
Proof.
  intros. remember (go ob) as b. assert (observe b = ob).
  { subst. auto. }
  rewrite <- H. auto.
Qed.

Lemma branch_prefix_proper_aux_vis: forall (E : Type -> Type) (S R : Type)
                                  (t1 : itree (EvAns E) R) (b2 : ibranch E R),
    eqitF eq true true id
          (upaco2 (eqit_ eq true true id) bot2)
          (observe t1) (observe b2) ->
    forall (r : ibranch E R -> ibranch E S -> Prop)
      (X : Type) (e : EvAns E X)
      (k : X -> itree (EvAns E) S),
      branch_prefixF (upaco2 branch_prefix_ bot2)
                     (observe t1) (VisF e k) ->
      (forall (b1 b2 : ibranch E R)
         (b : ibranch E S),
          (b1 ≈ b2)%itree ->
          branch_prefix b1 b -> r b2 b) ->
        branch_prefixF (upaco2 branch_prefix_ r)
        (observe b2) (VisF e k).
Proof.
  intros E S R t1 b2 Heutt r X e k H0 CIH.
  dependent induction H0.
  - rewrite <- x0 in Heutt. dependent induction Heutt.
    + rewrite <- x. apply branch_prefix_ret.
    + rewrite <- x. constructor. eapply IHHeutt; eauto.
  - eapply IHbranch_prefixF; auto.
    apply simpobs in x. assert (t1 ≈ b2)%itree; auto.
    rewrite x in H. rewrite tau_eutt in H. punfold H.
  - rewrite <- x in Heutt. dependent induction Heutt.
    + rewrite <- x. constructor.
    + rewrite <- x. constructor. eapply IHHeutt; eauto.
  - pclearbot. rewrite <- x in Heutt. dependent induction Heutt.
    + rewrite <- x. constructor. right. pclearbot. eapply CIH; eauto.
    + rewrite <- x. constructor. eapply IHHeutt; eauto.
Qed.

Lemma branch_prefix_tau_inv:
  forall (E : Type -> Type) (S R : Type)
    (m1 : itree (EvAns E) R) (t : itree (EvAns E) S),
    branch_prefixF (upaco2 branch_prefix_ bot2)
                   (TauF m1) (TauF t) -> branch_prefix m1 t.
Proof.
  intros E S R m1 t Hbp.
  dependent induction  Hbp.
  - pclearbot. auto.
  - pfold. red. clear IHHbp. dependent induction Hbp.
    + rewrite <- x0. auto.
    + rewrite <- x. constructor. pclearbot. punfold H.
    + rewrite <- x. constructor. eapply IHHbp; eauto.
    + auto.
  - pfold. red. clear IHHbp. dependent induction Hbp.
    + rewrite <- x. constructor. pclearbot. punfold H.
    + auto.
    + rewrite <- x. constructor. eapply IHHbp; eauto.
Qed.

Lemma branch_prefix_proper_l : forall E R S (b1 b2 : ibranch E R) (b : ibranch E S),
    (b1 ≈ b2)%itree -> branch_prefix b1 b -> branch_prefix b2 b.
Proof.
  intros E R S. pcofix CIH. intros b1 b2 b Heutt Hbp.
  pfold. red. punfold Heutt. red in Heutt. punfold Hbp. red in Hbp.
  dependent induction Heutt.
  - rewrite <- x. constructor.
  - rewrite <- x. rewrite <- x0 in Hbp. clear x0 x. pclearbot. 
    destruct (observe b) eqn : Heqb.
    + inv Hbp. constructor. dependent induction  H0. 
      * apply simpobs in x0. assert (m1 ≈ m2); auto.
        rewrite x0 in H. clear x x0 Heqb CIH REL.
        punfold H. red in H. cbn in *. dependent induction H.
        ++ rewrite <- x. apply branch_prefix_ret.
        ++ rewrite <- x. constructor. eapply IHeqitF; eauto.
      * eapply IHbranch_prefixF; auto.
        apply simpobs in x. assert (m1 ≈ m2); auto.
        rewrite x in H. rewrite tau_eutt in H. auto.
    + constructor. right. eapply CIH; eauto. eapply branch_prefix_tau_inv; eauto.
    + constructor. clear Heqb. inv Hbp. dependent induction H0. 
      * apply simpobs in x0. assert (m1 ≈ m2); auto.
        rewrite x0 in H. punfold H. red in H. cbn in *.
        dependent induction H.
       ++ rewrite <- x. apply branch_prefix_ret.
       ++ rewrite <- x. constructor. eapply IHeqitF; eauto.
          assert (m1 ≈ m2); auto.
          apply simpobs in x. rewrite x in H0. rewrite tau_eutt in H0. auto.
      * eapply IHbranch_prefixF; auto.
        assert (m1 ≈ m2); auto. apply simpobs in x.
        rewrite x in H. rewrite tau_eutt in H. auto.
      * assert (m1 ≈ m2); auto. apply simpobs in x.
        rewrite x in H0.
        punfold H0. red in H0. cbn in *.
        dependent induction H0.
        ++ rewrite <- x. constructor.
        ++ rewrite <- x. constructor. eapply IHeqitF; eauto.
           assert (m1 ≈ m2); auto.
           apply simpobs in x. rewrite x in H1. rewrite tau_eutt in H1. auto.
      * pclearbot. apply simpobs in x. assert (m1 ≈ m2); auto.
        rewrite x in H0. punfold H0. red in H0. cbn in *.
        dependent induction H0.
        ++ rewrite <- x. constructor. right. pclearbot. eapply CIH; eauto.
        ++ rewrite <- x. constructor. eapply IHeqitF; eauto. 
           assert (m1 ≈ m2); auto.
           apply simpobs in x. rewrite x in H1. rewrite tau_eutt in H1. auto.
  - rewrite <- x. rewrite <- x0 in Hbp. clear x x0. pclearbot.
    dependent induction Hbp.
    + rewrite <- x. constructor. eapply IHHbp; eauto.
    + rewrite <- x. constructor.
    + rewrite <- x. pclearbot. constructor. right. eapply CIH; eauto.
  - rewrite <- x in Hbp.
    destruct (observe b) eqn : Heqb.
    + clear IHHeutt. inv Hbp. clear Heqb x.
      dependent induction H0.
      * rewrite <- x0 in Heutt. clear CIH x0 x.
        dependent induction  Heutt.
        ++ rewrite <- x. apply branch_prefix_ret.
        ++ rewrite <- x. constructor. eapply IHHeutt; eauto.
       * eapply IHbranch_prefixF; auto.
         assert (t1 ≈ b2)%itree; auto.
         apply simpobs in x. rewrite x in H. rewrite tau_eutt in H. punfold H.
    + constructor. eapply IHHeutt; eauto. pstep_reverse. eapply branch_prefix_tau_inv; eauto.
    + clear IHHeutt. inv Hbp. eapply branch_prefix_proper_aux_vis; eauto.
  - rewrite <- x. constructor. eapply IHHeutt; eauto.
Qed.

Lemma branch_prefixF_tau_inv_r:
  forall (E : Type -> Type) (S R : Type)
    (t1 : itree (EvAns E) S) (b : ibranch E R),
    branch_prefixF (upaco2 branch_prefix_ bot2)
                   (observe b) (TauF t1) ->
    branch_prefixF (upaco2 branch_prefix_ bot2)
                   (observe b) (observe t1).
Proof.
  intros E S R t1 b Hbp.
  dependent induction  Hbp.
  - rewrite <- x0. apply branch_prefix_ret.
  - pclearbot. rewrite <- x. constructor. punfold H.
  - rewrite <- x. constructor. eapply IHHbp; eauto.
  - auto.
Qed.
  
Lemma branch_prefixF_vis_l:
  forall (E : Type -> Type) (S R : Type)
    (m1 m2 : itree (EvAns E) S),
    paco2 (eqit_ eq true true id) bot2 m1 m2 ->
    forall (r : ibranch E R -> ibranch E S -> Prop)
      (X : Type) (e : EvAns E X)
      (k : X -> itree (EvAns E) R),
      branch_prefixF (upaco2 branch_prefix_ bot2)
                     (VisF e k) (observe m1) ->
      (forall (b : ibranch E R)
         (b1 b2 : ibranch E S),
          (b1 ≈ b2)%itree ->
          branch_prefix b b1 -> r b b2 ) ->
      branch_prefixF (upaco2 branch_prefix_ r) 
                     (VisF e k) (observe m2).
Proof.
  intros E S R m1 m2 REL r X e k H1 CIH.
  punfold REL. red in REL.
  dependent induction H1.
  - eapply IHbranch_prefixF; auto. rewrite <- x in REL.
    assert (Tau bs ≈ m2).
    { pfold. auto. }
    rewrite tau_eutt in H. punfold H.
  - rewrite <- x in REL. dependent induction REL.
    + rewrite <- x. constructor.
    + rewrite <- x. constructor. eapply IHREL; eauto.
  - pclearbot. rewrite <- x in REL. dependent induction REL.
    + rewrite <- x. constructor. right. pclearbot. eapply CIH; eauto. 
    + rewrite <- x. constructor. eapply IHREL; eauto.
Qed.

Lemma branch_prefix_proper_r : forall E R S (b : ibranch E R) (b1 b2 : ibranch E S),
    (b1 ≈ b2)%itree -> branch_prefix b b1 -> branch_prefix b b2.
Proof.
  intros E R S. pcofix CIH. intros b b1 b2 Heutt Hbp.
  punfold Heutt. red in Heutt. punfold Hbp. red in Hbp.
  pfold. red. dependent induction Heutt.
  - rewrite <- x. rewrite <- x0 in Hbp. clear x0 x. induction Hbp; auto.
    + pclearbot. constructor. right. eapply CIH; eauto. reflexivity.
    + constructor. pclearbot. left. eapply paco2_mon; eauto. intuition.
  - pclearbot. rewrite <- x0 in Hbp. rewrite <- x. clear x0 x.
    destruct (observe b).
    + apply branch_prefix_ret.
    + constructor. right. pclearbot. eapply CIH; eauto. apply branch_prefix_tau_inv. auto.
    + inv Hbp. constructor. eapply branch_prefixF_vis_l; eauto.
  - rewrite <- x. rewrite <- x0 in Hbp. pclearbot. clear x x0. dependent induction Hbp.
    + rewrite <- x0. apply branch_prefix_ret.
    + rewrite <- x. constructor. eapply IHHbp; eauto.
    + rewrite <- x. constructor.
    + rewrite <- x. constructor. right. pclearbot. eapply CIH; eauto.
  - eapply IHHeutt; auto. rewrite <- x in Hbp. eapply branch_prefixF_tau_inv_r; eauto.
  - rewrite <- x. constructor. eapply IHHeutt; eauto.
Qed.
  
Instance branch_prefix_proper {E R S} : Proper (eutt eq ==> eutt eq ==> iff) (@branch_prefix E R S).
Proof.
  repeat intro. split; intros.
  - eapply branch_prefix_proper_l; eauto.
    eapply branch_prefix_proper_r; eauto.
  - symmetry in H. symmetry in H0.
    eapply branch_prefix_proper_l; eauto.
    eapply branch_prefix_proper_r; eauto.
Qed.

Inductive ind_comb {E R S} : ibranch E R -> ibranch E S -> ibranch E S -> Prop :=
  | left_ret_comb (r : R) b1 b2 b : (b1 ≈ Ret r)%itree -> (b2 ≈ b)%itree -> ind_comb b1 b2 b
  | left_vis_comb {A : Type} (e : E A) (ans : A) (k1 : unit -> ibranch E R) (k2 : unit -> ibranch E S) b1 b2 b 
    : (b1 ≈ Vis (evans _ e ans) k1)%itree -> (b ≈ (Vis (evans _ e ans) k2 ))%itree -> ind_comb (k1 tt) b2 (k2 tt) -> 
    ind_comb b1 b2 b.


Lemma ind_comb_bind : forall E R S (b1 : ibranch E R) (b2 : ibranch E S) (b : ibranch E S),
    ind_comb b1 b2 b -> (ITree.bind b1 (fun x => b2) ≈ b)%itree.
Proof.
  intros E R S b1 b2 b Hind. induction Hind.
  - rewrite H. rewrite bind_ret_l. auto.
  - rewrite H. rewrite H0. rewrite bind_vis. pfold. red. constructor. intros.
    left. destruct v. apply IHHind.
Qed.

Inductive branch_prefix_ind {E R S} : ibranch E R -> ibranch E S -> Prop :=
  | left_ret_bp (r : R) b1 b2 : (b1 ≈ Ret r)%itree -> branch_prefix_ind b1 b2
  | left_vis_bp {A : Type} (e : E A) (ans : A) (k1 : unit -> ibranch E R) (k2 : unit -> ibranch E S) b1 b2 :
      (b1 ≈ Vis (evans _ e ans) k1)%itree -> (b2 ≈ Vis (evans _ e ans) k2 )%itree -> branch_prefix_ind (k1 tt) (k2 tt) ->
      branch_prefix_ind b1 b2
.

Lemma branch_prefix_ind_comb : forall E R S (b1 : ibranch E R) (b2 : ibranch E S), branch_prefix_ind b1 b2 ->
                                                                          exists b3, ind_comb b1 b3 b2.
Proof.
  intros E R S b1 b2 Hpre. induction Hpre.
  - exists b2. econstructor; eauto. reflexivity.
  - destruct IHHpre as [b3 Hb3].
    exists b3. eapply left_vis_comb; eauto.
Qed.

Lemma branch_prefix_ind_bind : forall E R S (b1 : ibranch E R) (b2 : ibranch E S), branch_prefix_ind b1 b2 -> 
  exists g, (ITree.bind b1 g ≈ b2)%itree.
Proof.
  intros. apply branch_prefix_ind_comb in H. destruct H as [b3 Hb3].
  apply ind_comb_bind in Hb3. exists (fun _ => b3). auto.
Qed.

Lemma converge_branch_prefix : forall E R S (b1 : ibranch E R) (b2 : ibranch E S) (r : R), 
    branch_prefix b1 b2 -> can_converge r b1 -> branch_prefix_ind b1 b2.
Proof.
  intros E R S b1 b2 r Hbp Hconv. generalize dependent b2. induction Hconv; intros.
  - eapply left_ret_bp; eauto.
  - rewrite H in Hbp. destruct e; try contradiction.
    apply prefix_vis in Hbp as Hb2.
    destruct Hb2 as [k' Hk']. rewrite Hk' in Hbp.
    eapply left_vis_bp; eauto. destruct b. apply IHHconv.
    punfold Hbp. red in Hbp. cbn in *. inversion Hbp. subst; inj_existT; subst.
    pclearbot. auto.
Qed.

Lemma branch_prefix_div : forall E R S (b1 : ibranch E R) (b2 : ibranch E S),
    must_diverge b1 -> branch_prefix b1 b2 -> eutt_div b1 b2.
Proof.
  intros E R S. pcofix CIH. intros b1 b2 Hdiv Hbf. pfold. red.
  punfold Hbf. red in Hbf. punfold Hdiv. red in Hdiv. induction Hbf.
  - inv Hdiv.
  - constructor. inv Hdiv. pclearbot. right. apply CIH; auto.
  - constructor; auto. apply IHHbf. pstep_reverse. inv Hdiv. pclearbot. auto.
  - constructor; auto. 
  - constructor. intuition.
  - pclearbot. constructor. intros. right. pclearbot. inv Hdiv. inj_existT; subst.
    pclearbot. destruct v. apply CIH; auto. apply H1.
Qed.

Lemma branch_prefix_bind : forall E R S (b1 : ibranch E R) (b2 : ibranch E S),
    branch_prefix b1 b2 -> exists g, (ITree.bind b1 g ≈ b2)%itree.
Proof.
  intros. destruct (classic_converge _ _ b1).
  - destruct H0 as [r Hconv]. eapply converge_branch_prefix in Hconv; eauto.
    apply branch_prefix_ind_bind. auto.
  - eapply branch_prefix_div in H0 as Heuttdiv; eauto.
    exists (fun _ => ITree.spin). apply eutt_div_subrel. apply eutt_div_sym. 
    eapply div_bind_nop with (f := (fun _ => ITree.spin) ) in H0 as H1.
    eapply eutt_div_trans; try apply H1. apply eutt_div_sym. auto.
Qed.
 
