From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     ITrace.ITraceFacts
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.


Variant itree_forallF (E : Type -> Type) (R : Type) (F : itree E R -> Prop) (PE : forall A : Type, E A -> Prop) (PR : R -> Prop ) : itree' E R -> Prop :=
  | itree_forall_retF r : PR r -> itree_forallF E R F PE PR (RetF r)
  | itree_forall_tauF t : F t ->  itree_forallF E R F PE PR (TauF t)
  | itree_forall_visF A (e : E A) k : PE A e -> (forall a : A, F (k a)) -> itree_forallF E R F PE PR (VisF e k)
.

Hint Constructors itree_forallF.

Definition itree_forall_ E R PE PR F t := itree_forallF E R F PE PR (observe t).

Lemma itree_forall_monot {E R} PE PR : monotone1 (@itree_forall_ E R PE PR).
Proof.
  repeat intro. red in IN. red. induction IN; auto.
Qed.

Hint Resolve itree_forall_monot : paco.

Definition itree_forall {E R} PE PR t := paco1 (itree_forall_ E R PE PR) bot1 t.

Lemma itree_forall_proper_aux: forall (E : Type -> Type) (R : Type) (PE : forall A : Type, E A -> Prop)
                                  (PR : R -> Prop) (t1 t2 : itree E R),
    (t1 ≈ t2) -> itree_forall PE PR t1 -> itree_forall PE PR t2.
Proof.
  intros E R PE PR. pcofix CIH. intros t1 t2 Heutt Hforall.
  pfold. red. punfold Hforall. red in Hforall.
  punfold Heutt. red in Heutt. induction Heutt; subst; auto.
  - inv Hforall. auto.
  - inv Hforall. pclearbot. constructor. right. eapply CIH; eauto.
  - inv Hforall. inj_existT. subst. pclearbot.
    constructor; auto. intros. right. eapply CIH; eauto. apply H3.
  - apply IHHeutt. inv Hforall. pclearbot. punfold H0.
  - constructor. left. pfold. red. apply IHHeutt. auto.
Qed.

Global Instance itree_forall_proper_eutt {E R PE PR} : Proper (eutt eq ==> iff) (@itree_forall E R PE PR).
Proof.
  intros t1 t2 Heutt. split; intros.
  - eapply itree_forall_proper_aux; eauto.
  - symmetry in Heutt. eapply itree_forall_proper_aux; eauto.
Qed.

Variant itree_forall_bind_clo E R PE (PR : R -> Prop)  (r : itree E R -> Prop ) : itree E R -> Prop := 
  | ifbc_intro S (t : itree E S) (k : S -> itree E R) (Pinv : S -> Prop) :
      itree_forall PE Pinv t -> (forall s, Pinv s -> r (k s) ) ->
      itree_forall_bind_clo E R PE PR r (ITree.bind t k)
.

Lemma itree_forall_bind_clo_wcompat E R PE PR : 
  wcompatible1 (itree_forall_ E R PE PR) (itree_forall_bind_clo E R PE PR) .
Proof.
  constructor.
  - red. intros. induction IN; eauto. econstructor; eauto.
  - intros r t Hclo. inv Hclo. red. unfold observe. cbn. punfold H.
    red in H. inv H.
    + eapply itree_forall_monot; eauto.
      intros t Hrt. red. gfinal. eauto.
    + cbn. constructor. gclo. pclearbot. econstructor; eauto. intros.
      gfinal. right. pfold. eapply itree_forall_monot; eauto.
    + cbn. pclearbot. constructor; auto. intros. gclo.
      econstructor; try apply H3. intros.  gfinal.
      right. pfold. eapply itree_forall_monot; eauto.
Qed.

Inductive itree_forall_trans_clo E R (r : itree E R -> Prop)
  : itree E R -> Prop :=
| itree_forall_trans_clo_intro t1 t1'
      (EQV: t1 ≅ t1')
      (Ht2 : r t1')
  : itree_forall_trans_clo E R r t1.

Lemma itree_forall_trans_clo_wcompat E R PE PR : 
  wcompatible1 (itree_forall_ E R PE PR) (itree_forall_trans_clo E R ) .
Proof.
  constructor.
  - red. intros. induction IN; eauto. econstructor; eauto.
  - intros r t1 Hclo. inv Hclo. red. red in Ht2. punfold EQV.
    red in EQV. inv EQV; try inv CHECK.
    + rewrite <- H in Ht2. inv Ht2. constructor; auto.
    + constructor. pclearbot. rewrite <- H in Ht2. inv Ht2. gclo.
      econstructor; eauto. gfinal. eauto.
    + pclearbot. rewrite <- H in Ht2. inv Ht2. ITraceFacts.inj_existT; subst.
      constructor; auto. intros. gclo. econstructor; eauto. gfinal. eauto.
Qed.

Hint Resolve itree_forall_trans_clo_wcompat : paco.

Locate geuttgen_cong_eqit_eq.

Instance itree_forall_gpaco_proper {E R PE PR r rg} : Proper (eq_itree eq ==> flip impl) 
                                                             (gpaco1 (itree_forall_ E R PE PR) (itree_forall_trans_clo E R) r rg).
Proof.
  intros t1 t2 Heq H. gclo. econstructor; eauto. 
Qed.

Lemma itree_forall_clo_bind E R PE PR : 
  itree_forall_bind_clo E R PE PR <2= gupaco1 (itree_forall_ E R PE PR) (itree_forall_trans_clo E R).
Proof.
  intros r t H. generalize dependent t. gcofix CIH. intros t Ht. inv Ht.
  pinversion H; try apply simpobs in H1.
  - rewrite H1. rewrite bind_ret_l. gfinal. eauto.
  - rewrite H1. rewrite bind_tau. gstep. constructor. gfinal. left. eapply CIH.
    econstructor; eauto.
  - rewrite H1. rewrite bind_vis. gstep. constructor; auto. intros. gfinal. left. apply CIH.
    econstructor; eauto. apply H3.
Qed.

Lemma itree_forall_bind E S R (PE : forall A, E A -> Prop) (PS : S -> Prop) (PR : R -> Prop) t k :
  itree_forall PE PS t -> (forall s, PS s -> itree_forall PE PR (k s) ) ->
  itree_forall PE PR (ITree.bind t k).
Proof.
  intros. ginit. guclo itree_forall_clo_bind. econstructor; eauto.
  intros. gfinal. right. apply H0; auto.
Qed.

Lemma itree_forall_iter_ev (A B : Type) E  (body : A -> itree E (A + B) ) init
  (PE : forall A, E A -> Prop) : (forall a, itree_forall PE (fun _ => True) (body a) ) -> itree_forall PE (fun _ => True) (iter body init).
Proof.
  revert init. ginit. gcofix CIH. intros a Hbody. setoid_rewrite unfold_iter.
  guclo itree_forall_clo_bind. econstructor. apply Hbody. intros [a' | b] _.
  - gstep. constructor. gfinal; eauto.
  - gstep. constructor; auto.
Qed.

Lemma itree_forall_ret E R (PE : forall A, E A -> Prop) (PR : R -> Prop) (r : R) :
  PR r -> itree_forall PE PR (Ret r).
Proof.
  intros. pfold. constructor; auto.
Qed.

Lemma itree_forall_vis E R (PE : forall A, E A -> Prop) PR A (e : E A) (k : A -> itree E R) :
  PE A e -> (forall a, itree_forall PE PR (k a) ) -> itree_forall PE PR (Vis e k).
Proof.
  intros. pfold. constructor; auto. left. apply H0.
Qed.

Lemma itree_forall_mon E R (PE1 PE2 : forall A, E A -> Prop) (PR1 PR2 : R -> Prop) t :
   (forall A (e : E A), PE1 A e -> PE2 A e) -> (forall r, PR1 r -> PR2 r) ->
   itree_forall PE1 PR1 t -> itree_forall PE2 PR2 t.
Proof.
  intros HPE HPR. revert t. pcofix CIH. intros t Ht. punfold Ht. red in Ht.
  pfold. red. inv Ht; pclearbot; eauto.
  constructor; eauto. right. eapply CIH; auto; apply H1.
Qed.
