(** * Infiniteness of ITrees *)

(** - [all_infinite]: all branches of an ITree are infinite.
    - [any_infinite]: there exists an infinite branch. *)

(* begin hide *)

From Coinduction Require Import all. 

From Stdlib Require Import
     Setoid
     Morphisms
     RelationClasses.

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

Lemma any_infinite__mono {E X} : 
Proper (leq ==> leq) (@any_infinite_ E X).
Proof. 
  repeat red; intros. 
  induction H0; eauto with mono itree.  
Qed. 

Definition any_infinite_mon {E X} : mon (itree E X -> Prop) := 
   {| body := @any_infinite_ E X ; Hbody := any_infinite__mono |}.

Definition any_infinite {E X} : itree E X -> Prop :=
  gfp any_infinite_mon.

#[global]
Instance any_infinite_proper_eutt {E X R} : Proper (eutt R ==> iff) (@any_infinite E X).
Proof.
  intros t1 t2 Ht. split; intros Hinf.
  - revert t2 t1 Ht Hinf. unfold any_infinite at 2. coinduction c CIH.
    intros t2 t1 Ht Hinf. step in Ht. cbn[eqit_mon body] in Ht. unfold eqit_ in Ht.
    cbn[any_infinite_mon body]. unfold any_infinite_.
    apply (gfp_fp any_infinite_mon) in Hinf.
    cbn[any_infinite_mon body] in Hinf. unfold any_infinite_ in Hinf.
    induction Ht.
    + inversion Hinf.
    + inversion Hinf; subst. constructor. eapply CIH; eauto.
    + inversion Hinf; subst. dependent destruction H2.
      econstructor. eapply CIH; [apply REL|]. eauto.
    + apply IHHt. inversion Hinf; subst.
      apply (gfp_fp any_infinite_mon) in H0.
      cbn[any_infinite_mon body] in H0. unfold any_infinite_ in H0. exact H0.
    + constructor. step. cbn[any_infinite_mon body]. unfold any_infinite_.
      apply IHHt. exact Hinf.
  - revert t1 t2 Ht Hinf. unfold any_infinite at 2. coinduction c CIH.
    intros t1 t2 Ht Hinf. step in Ht. cbn[eqit_mon body] in Ht. unfold eqit_ in Ht.
    cbn[any_infinite_mon body]. unfold any_infinite_.
    apply (gfp_fp any_infinite_mon) in Hinf.
    cbn[any_infinite_mon body] in Hinf. unfold any_infinite_ in Hinf.
    induction Ht.
    + inversion Hinf.
    + inversion Hinf; subst. constructor. eapply CIH; eauto.
    + inversion Hinf; subst. dependent destruction H2.
      econstructor. eapply CIH; [apply REL|]. eauto.
    + constructor. step. cbn[any_infinite_mon body]. unfold any_infinite_.
      apply IHHt. exact Hinf.
    + apply IHHt. inversion Hinf; subst.
      apply (gfp_fp any_infinite_mon) in H0.
      cbn[any_infinite_mon body] in H0. unfold any_infinite_ in H0. exact H0.
Qed.

Theorem spin_infinite {E A} : @any_infinite E A ITree.spin.
Proof.
  unfold any_infinite. coinduction c CIH.
  cbn[any_infinite_mon body]. unfold any_infinite_. cbn.
  constructor. exact CIH.
Qed.

Variant all_infiniteF {E : Type -> Type} {A : Type} (F : itree E A -> Prop) : itree' E A -> Prop :=
  | MDivTau (t : itree E A) : F t -> all_infiniteF F (TauF t)
  | MDivVis (B : Type) (k : B -> itree E A) (e : E B) :
      (forall b, F (k b)) -> all_infiniteF F (VisF e k).
#[global] Hint Constructors all_infiniteF : itree.

Definition all_infinite_ {E A} (sim : itree E A -> Prop) t := all_infiniteF sim (observe t).

Lemma all_infiniteF_mono {E A} (sim sim' : itree E A -> Prop) t
      (IN : all_infiniteF sim t)
      (LE : forall x, sim x -> sim' x) : all_infiniteF sim' t.
Proof.
  induction IN; eauto with itree.
Qed.

Lemma all_infinite__mono {E A} : Proper (leq ==> leq) (@all_infinite_ E A).
Proof.
  repeat red; intros sim sim' LE t IN.
  unfold all_infinite_ in *. eapply all_infiniteF_mono; eauto.
Qed.

Definition all_infinite_mon {E A} : mon (itree E A -> Prop) :=
  {| body := @all_infinite_ E A ; Hbody := all_infinite__mono |}.

Definition all_infinite {E A} : itree E A -> Prop := gfp (@all_infinite_mon E A).

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
  intros t1 t2 Ht. split; intros Hinf.
  - revert t1 t2 Ht Hinf. unfold all_infinite at 2. coinduction c CIH.
    intros t1 t2 Ht Hinf. step in Ht. cbn[eqit_mon body] in Ht. unfold eqit_ in Ht.
    cbn[all_infinite_mon body]. unfold all_infinite_.
    apply (gfp_fp all_infinite_mon) in Hinf.
    cbn[all_infinite_mon body] in Hinf. unfold all_infinite_ in Hinf.
    induction Ht.
    + inversion Hinf.
    + inversion Hinf; subst. constructor. eapply CIH; eauto.
    + inversion Hinf; subst. dependent destruction H2.
      econstructor. intros b. eapply CIH; [apply REL|]. apply H0.
    + apply IHHt. inversion Hinf; subst.
      apply (gfp_fp all_infinite_mon) in H0.
      cbn[all_infinite_mon body] in H0. unfold all_infinite_ in H0. exact H0.
    + constructor. step. cbn[all_infinite_mon body]. unfold all_infinite_.
      apply IHHt. exact Hinf.
  - revert t1 t2 Ht Hinf. unfold all_infinite at 2. coinduction c CIH.
    intros t1 t2 Ht Hinf. step in Ht. cbn[eqit_mon body] in Ht. unfold eqit_ in Ht.
    cbn[all_infinite_mon body]. unfold all_infinite_.
    apply (gfp_fp all_infinite_mon) in Hinf.
    cbn[all_infinite_mon body] in Hinf. unfold all_infinite_ in Hinf.
    induction Ht.
    + inversion Hinf.
    + inversion Hinf; subst. constructor. eapply CIH; eauto.
    + inversion Hinf; subst. dependent destruction H2.
      econstructor. intros b. eapply CIH; [apply REL|]. apply H0.
    + constructor. step. cbn[all_infinite_mon body]. unfold all_infinite_.
      apply IHHt. exact Hinf.
    + apply IHHt. inversion Hinf; subst.
      apply (gfp_fp all_infinite_mon) in H0.
      cbn[all_infinite_mon body] in H0. unfold all_infinite_ in H0. exact H0.
Qed.

Lemma not_converge_to_all_infinite : forall (E : Type -> Type) (A : Type) (t : itree E A),
    (forall a, ~ may_converge a t) -> all_infinite t.
Proof.
  intros E A. unfold all_infinite. coinduction c CIH. intros t Hcon.
  cbn[all_infinite_mon body]. unfold all_infinite_.
  destruct (observe t) eqn:Heq;
    specialize (itree_eta t) as Ht; rewrite Heq in Ht.
  - exfalso. apply (Hcon r). rewrite Ht. constructor. reflexivity.
  - constructor. apply CIH.
    setoid_rewrite Ht in Hcon. setoid_rewrite tau_eutt in Hcon. auto.
  - constructor. intros b. apply CIH.
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
  - rewrite H in Hd. apply (gfp_fp all_infinite_mon) in Hd.
    cbn[all_infinite_mon body] in Hd. unfold all_infinite_ in Hd.
    inversion Hd.
  - apply IHHc. rewrite H in Hd.
    apply (gfp_fp all_infinite_mon) in Hd.
    cbn[all_infinite_mon body] in Hd. unfold all_infinite_ in Hd.
    inversion Hd. ddestruction. subst. apply H1.
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
  intros H HContra. rewrite HContra in H.
  apply (gfp_fp any_infinite_mon) in H.
  cbn[any_infinite_mon body] in H. unfold any_infinite_ in H.
  inversion H.
Qed.
