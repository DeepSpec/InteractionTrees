(** * Infiniteness of ITrees *)

(** - [all_infinite]: all branches of an ITree are infinite.
    - [any_infinite]: there exists an infinite branch. *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Axioms
     Basics
     Core.ITreeDefinition
     Eq.Eqit
     Eq.Shallow.
(* end hide *)

Import ITreeNotations.
#[local] Open Scope itree.

Set Implicit Arguments.

(** ** Infinite * *)

Inductive any_infiniteF {E X} (P : itree E X -> Prop) : itree' E X -> Prop :=
  | DivTau : forall (t : itree E X), P t -> any_infiniteF P (TauF t)
  | DivVis : forall {A} (k : A -> itree E X) (e: E A) (a : A), P (k a) -> any_infiniteF P (VisF e k).
#[global] Hint Constructors any_infiniteF : itree.

Definition any_infinite_ {E X} sim :=
  fun t1 => @any_infiniteF E X sim (observe t1).
#[global] Hint Unfold any_infinite_ : itree.

Lemma any_infiniteF_mono {E X} sim sim' x0
      (IN: any_infiniteF sim x0)
      (LE: sim <1= sim'):
  @any_infiniteF E X sim' x0.
Proof.
  intros. induction IN; eauto with itree.
Qed. 

Lemma any_infiniteF__mono {E X} :
  monotone1 (@any_infinite_ E X).
Proof.
  do 2 red. intros. eapply any_infiniteF_mono; eauto.
Qed. 
#[global] Hint Resolve any_infiniteF__mono : paco.

Definition any_infinite {E A} : itree E A -> Prop :=
  paco1 (@any_infinite_ E A) bot1.

#[global]
Instance any_infinite_proper_eutt {E X R} : Proper (eutt R ==> iff) (@any_infinite E X).
Proof.
  repeat intro. split.
  - revert x y H. pcofix CH. intros.
    punfold H0. unfold_eqit. pfold. red. punfold H1. red in H1.
    induction H0.
    + inversion H1.
    + apply DivTau. inversion H1; subst. right. eapply CH.
      red in H0. pclearbot. apply REL.
      pclearbot. apply H0.
    + inversion H1; subst. dependent destruction H3. eapply DivVis. 
      pclearbot. right. eapply CH. apply REL. eapply H0.
    + apply IHeqitF. inversion H1; subst.
      pclearbot. punfold H2.
    + econstructor. left. pfold. red.
      apply IHeqitF. apply H1.
  - revert x y H. pcofix CH. intros.
    punfold H0. unfold_eqit. pfold. red. punfold H1. red in H1.
    induction H0.
    + inversion H1.
    + apply DivTau. inversion H1; subst. right. eapply CH.
      red in H0. pclearbot. apply REL.
      pclearbot. apply H0.
    + inversion H1; subst. dependent destruction H3. eapply DivVis.
      pclearbot. right. eapply CH. apply REL. eapply H0.
    + econstructor. left. pfold. red.
      apply IHeqitF. apply H1.
    + apply IHeqitF. inversion H1; subst.
      pclearbot. punfold H2.
Qed.

Theorem spin_infinite {E A} : @any_infinite E A ITree.spin.
Proof.
  unfold any_infinite, ITree.spin.
  pcofix H. pfold. constructor. right. apply H.
Qed. 

Variant all_infiniteF {E : Type -> Type} {A : Type} (F : itree E A -> Prop) : itree' E A -> Prop :=
  | MDivTau (t : itree E A) : F t -> all_infiniteF F (TauF t)
  | MDivVis (B : Type) (k : B -> itree E A) (e : E B) :
      (forall b, F (k b)) -> all_infiniteF F (VisF e k).
#[global] Hint Constructors all_infiniteF : itree.

Definition all_infinite_ {E A} (sim : itree E A -> Prop) t := all_infiniteF sim (observe t).

Lemma all_infiniteF_mono {E A} (sim sim' : itree E A -> Prop) t
      (IN : all_infiniteF sim t)
      (LE : sim <1= sim') : all_infiniteF sim' t.
Proof.
  induction IN; eauto with itree.
Qed.

Lemma all_infiniteF_mono' {E A} : monotone1 (@all_infinite_ E A).
Proof.
  unfold all_infinite_.
  red. intros. eapply all_infiniteF_mono; eauto.
Qed.
#[global] Hint Resolve all_infiniteF_mono' : paco.

Definition all_infinite {E A} := paco1 (@all_infinite_ E A) bot1.

#[global] Hint Unfold all_infinite : itree.

Inductive may_converge {E : Type -> Type} {A : Type} (a : A) : itree E A -> Prop :=
| conv_ret (t : itree E A) : t ≈ Ret a -> may_converge a t
| conv_vis (t : itree E A ) {B : Type} (e : E B) (k : B -> itree E A) (b : B) :
    t ≈ Vis e k -> may_converge a (k b) -> may_converge a t.
#[global] Hint Constructors may_converge : itree.

#[global]
Instance eutt_proper_con_converge {A E} {a : A} : Proper (eutt eq ==> iff) (@may_converge E _ a).
Proof.
  intros t1 t2 Ht. split; intros.
  - induction H.
    + apply conv_ret; auto. rewrite <- Ht. auto.
    + eapply conv_vis; eauto. rewrite <- H.
      symmetry. auto.
  - induction H.
    + apply conv_ret; auto. rewrite Ht. auto.
    + eapply conv_vis; eauto. rewrite Ht.
      eauto.
Qed.

Ltac contra_void := try match goal with | a : void |- _ => contradiction end.

#[global]
Instance eutt_proper_all_infinite {E A R} : Proper (eutt R ==> iff) (@all_infinite E A).
Proof.
  intros t1 t2 Ht. split.
  - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
    punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
    induction Ht.
    + inversion Hdiv.
    + constructor. inversion Hdiv. subst. right.
      pclearbot.
      eapply CIH; eauto.
    + constructor. inversion Hdiv. subst. ddestruction.
      subst. intros. right. inversion Hdiv. ddestruction.
      subst. pclearbot. eapply CIH; auto with itree.
    + apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
    + constructor. left. pfold. apply IHHt. auto.
  - revert t1 t2 Ht. pcofix CIH. intros t1 t2 Ht Hdiv.
    punfold Ht. unfold_eqit. pfold. red. punfold Hdiv. red in Hdiv.
    induction Ht.
    + inversion Hdiv.
    + constructor. inversion Hdiv. subst. right.
      pclearbot; eauto.
    + constructor. inversion Hdiv. subst. ddestruction.
      subst. intros. right. inversion Hdiv. subst. ddestruction.
      subst. pclearbot. eapply CIH; auto with itree.
    +  constructor. left. pfold. apply IHHt. auto.
    +  apply IHHt. inversion Hdiv. subst. pclearbot. punfold H0.
Qed.

Lemma not_converge_to_all_infinite : forall (E : Type -> Type) (A : Type) (t : itree E A),
    (forall a, ~ may_converge a t) -> all_infinite t.
Proof.
  intros E A. pcofix CIH. intros t Hcon. pfold.
  red. destruct (observe t) eqn : Heq;
         specialize (itree_eta t) as Ht; rewrite Heq in Ht.
  - exfalso. apply (Hcon r0). rewrite Ht. constructor. reflexivity.
  - constructor. right. apply CIH.
    setoid_rewrite Ht in Hcon. setoid_rewrite tau_eutt in Hcon.
    auto.
  - constructor. right. apply CIH.
    intros a Hcontra. setoid_rewrite Ht in Hcon.
    apply (Hcon a). eapply conv_vis; try reflexivity; eauto.
Qed.

Lemma classic_converge : forall (E : Type -> Type) (A : Type) (t : itree E A),
    (exists a, may_converge a t) \/ all_infinite t.
Proof.
  intros. destruct (classic (exists a, may_converge a t) ); auto.
  right. apply not_converge_to_all_infinite. intros a Hcontra.
  apply H. exists a. auto.
Qed.

Lemma all_infinite_not_converge : forall (E : Type -> Type) (R : Type) (t : itree E R) (r : R),
    may_converge r t -> ~ all_infinite t.
Proof.
  intros E R t r Hc Hd. induction Hc.
  - rewrite H in Hd. pinversion Hd.
  - apply IHHc. rewrite H in Hd. pinversion Hd.
    ddestruction. subst.
    apply H1.
Qed.

Lemma may_converge_Ret_inv E (A : Type) (a a' : A) : may_converge (E := E) a (Ret a') -> a = a'.
Proof.
  intros. inversion H.
  - apply eutt_inv_Ret in H0. auto.
  - apply eqit_inv in H0; cbn in H0; contradiction.
Qed.

(* Derives contradiction from evidence that a return tree is infinite *)
Ltac inv_infinite_ret := match goal with [ H : any_infiniteF _ (RetF _) |- _  ] => inversion H end.

(* Infinite trees never return a value*)
Lemma no_infinite_ret (E : Type -> Type) (A : Type) (t: itree E A) (a : A)
  : any_infinite t -> t ≈ Ret a -> False.
Proof.
  intros H HContra. rewrite HContra in H. pinversion H.
Qed.
