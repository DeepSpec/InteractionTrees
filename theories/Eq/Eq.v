From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     ProofIrrelevance.

From Paco Require Import paco.

From ITree Require Import
     Core.


(* TODO: move to tactics area / document *)
Ltac auto_inj_pair2 :=
  repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
          end).

(* SAZ: Move elsewhere? Add to Coq standard library? *)
Lemma pointwise_relation_fold {A B} {r: relation B} f g: (forall v:A, r (f v) (g v)) -> pointwise_relation _ r f g.
  Proof. red. eauto. Qed.

  
(* Coinductively defined equality on itrees, also called: strong bisimulation,
   extensional equality.  *)
Section eq_itree.
  Context {E : Type -> Type} {R : Type}.

  Inductive eq_itreeF (sim : relation (itree E R)) : relation (itreeF E R (itree E R)) :=
  | EqRet : forall x, eq_itreeF sim (RetF x) (RetF x)
  | EqTau : forall m1 m2
      (REL: sim m1 m2), eq_itreeF sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2
      (REL: forall v, sim (k1 v) (k2 v)),
      eq_itreeF sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eq_itreeF.

  Global Instance Reflexive_eq_itreeF sim
  : Reflexive sim -> Reflexive (eq_itreeF sim).
  Proof.
    red. destruct x; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF sim 
  : Symmetric sim -> Symmetric (eq_itreeF sim).
  Proof.
    red. inversion 2; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF sim
  : Transitive sim -> Transitive (eq_itreeF sim).
  Proof.
    red. inversion 2; inversion 1; eauto.
    subst. dependent destruction H6. dependent destruction H7. eauto.
  Qed.

  Definition eq_itree_ (sim: relation (itree E R)) : relation (itree E R) :=
    fun t1 t2 => eq_itreeF sim (observe t1) (observe t2).
  Hint Unfold eq_itree_.

  Lemma eq_itreeF_mono : forall x0 x1 r r'
    (IN: eq_itreeF r x0 x1) (LE: forall x2 x3, (r x2 x3 : Prop) -> r' x2 x3 : Prop), eq_itreeF r' x0 x1.
  Proof. pmonauto. Qed.

  Lemma eq_itreeF__mono : monotone2 eq_itree_.
  Proof. do 2 red. pmonauto. Qed.

  Definition eq_itree : relation (itree E R) := paco2 eq_itree_ bot2.

  Global Instance Reflexive_eq_itree_ sim
  : Reflexive sim -> Reflexive (eq_itree_ sim).
  Proof. red; red; reflexivity. Qed.

  Global Instance Symmetric_eq_itree_ sim
  : Symmetric sim -> Symmetric (eq_itree_ sim).
  Proof. red; red; symmetry; auto. Qed.

  Global Instance Transitive_eq_itree_ sim
  : Transitive sim -> Transitive (eq_itree_ sim).
  Proof. red; red; etransitivity; eauto. Qed.

End eq_itree.

Hint Constructors eq_itreeF.
Hint Unfold eq_itree_.
Hint Resolve eq_itreeF_mono : paco.
Hint Unfold eq_itree.

Definition go_sim {E R} (r: relation (itree E R)) : relation (itreeF E R (itree E R)) :=
  fun ot1 ot2 => r (go ot1) (go ot2).

Ltac unfold_eq_itree :=
  (try match goal with [|- eq_itree_ _ _ _ ] => red end);
  (repeat match goal with [H: eq_itree_ _ _ _ |- _ ] => red in H end).

Delimit Scope eq_itree_scope with eq_itree.
Notation "t1 ≅ t2" := (eq_itree t1%itree t2%itree) (at level 70).
(* you can write ≅ using \cong in tex-mode *)



(* Some simple congruences -------------------------------------------------- *)

Lemma itree_eq_tau : forall {E R} (t1 t2 : itree E R),
    t1 ≅ t2 -> Tau t1 ≅ Tau t2.
Proof.
  intros E R t1 t2 H.
  pfold. econstructor. left. assumption.
Qed.

Lemma itree_eq_vis : forall {E R S} (e : E R) (k1 k2 : R -> itree E S)
    (h : forall (r:R), (k1 r) ≅ (k2 r)),  Vis e k1 ≅ Vis e k2.
Proof.
  intros E R S e k1 k2 h. 
  pfold. econstructor. intros v. left. apply h.
Qed.  


(* eq_itree is an equivalence ----------------------------------------------- *)

Lemma eq_itree_refl {E R} r x : paco2 (@eq_itree_ E R) r x x.
Proof.
  revert x. pcofix CIH; intros.
  pfold. unfold_eq_itree. destruct (observe x); eauto.
Qed.
Hint Resolve eq_itree_refl : refl.

Global Instance Reflexive_eq_itree {E R} : Reflexive (@eq_itree E R).
Proof.
  eauto with refl.
Qed.

Global Instance Symmetric_eq_itree {E R} : Symmetric (@eq_itree E R).
Proof.
  pcofix CIH; intros.
  pfold. unfold_eq_itree. punfold H0. inv H0; eauto.
  - pclearbot. eauto.
  - econstructor. intros. specialize (REL v). pclearbot. eauto.
Qed.

Global Instance Transitive_eq_itree {E R} : Transitive (@eq_itree E R).
Proof.
  pcofix CIH. intros.
  pfold. punfold H0. punfold H1. unfold_eq_itree.
  genobs x ox; genobs y oy; genobs z oz.
  remember oy as oy' in H1.
  destruct H0, H1; inversion Heqoy'; subst; auto.
  - pclearbot; eauto.
  - apply inj_pair2 in H1.
    apply inj_pair2 in H2.
    subst; econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto.
Qed.

Global Instance Equivalence_eq_itree {E R} :
  Equivalence (@eq_itree E R).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance Equivalence_go_eq_itree {E R} :
  Equivalence (go_sim (@eq_itree E R)).
Proof.
  constructor; repeat intro; red; eauto with refl.
  - symmetry; eauto.
  - etransitivity; eauto.
Qed.





Instance eq_itree_go {E R} :
  Proper (go_sim (@eq_itree E R) ==> @eq_itree E R) (@go E R).
Proof.
  repeat intro. eauto.
Qed.

Instance eq_itree_observe {E R} :
  Proper (@eq_itree E R ==> go_sim (@eq_itree E R)) (@observe E R).
Proof.
  repeat intro. punfold H. pfold. eapply eq_itreeF_mono; eauto.
Qed.

Instance eq_itree_tauF {E R} :
  Proper (@eq_itree E R ==> go_sim (@eq_itree E R)) (@TauF E R _).
Proof.
  repeat intro. pfold. econstructor. eauto.
Qed.

Instance eq_itree_VisF {E R u} (e: E u) :
  Proper (pointwise_relation _ eq_itree ==> go_sim (@eq_itree E R)) (VisF e).
Proof.
  repeat intro. red in H. pfold. econstructor. left. apply H.
Qed.

Lemma itree_eta {E R} (t: itree E R): t ≅ go (observe t).
Proof.
  pfold. red. cbn. eapply Reflexive_eq_itreeF; eauto with refl.
Qed.

Lemma bind_unfold {E R S}
           (t : itree E R) (k : R -> itree E S) :
  observe (ITree.bind t k) = observe (ITree.bind_match k (ITree.bind' k) (observe t)).
Proof. eauto with refl. Qed.

Lemma unfold_bind {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree.bind_match k (ITree.bind' k) (observe t).
Proof. rewrite itree_eta, bind_unfold, <-itree_eta. eauto with refl. Qed.

Lemma ret_bind {E R S} (r : R) :
  forall k : R -> itree E S,
    ITree.bind (Ret r) k ≅ (k r).
Proof.
  intros. rewrite unfold_bind. eauto with refl.
Qed.

Lemma tau_bind {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof.
  setoid_rewrite unfold_bind at 1. eauto with refl.
Qed.

Lemma vis_bind {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof.
  setoid_rewrite unfold_bind at 1. eauto with refl.
Qed.

Inductive eq_itree_trans_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| eq_itree_trans_clo_intro (t1 t2 t3 t4: itree E R)
      (EQVl: t1 ≅ t2)
      (EQVr: t4 ≅ t3)
      (RELATED: r t2 t3)
  : eq_itree_trans_clo r t1 t4
.
Hint Constructors eq_itree_trans_clo.

Lemma eq_itree_clo_trans E R: weak_respectful2 eq_itree_ (@eq_itree_trans_clo E R).
Proof.
  econstructor; [pmonauto|].
  intros. dependent destruction PR.
  apply GF in RELATED.
  punfold EQVl. punfold EQVr. unfold_eq_itree.
  genobs t1 ot1; genobs t2 ot2; genobs t3 ot3; genobs t4 ot4.
  destruct EQVl;
    inversion EQVr; clear EQVr;
    inversion RELATED; clear RELATED;
      subst; simpobs; try discriminate.

  - inversion H0; auto.
  - inversion H0; subst; pclearbot; eauto using rclo2.

  - inversion H0; subst; auto_inj_pair2; subst.
    pclearbot.
    econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto using rclo2.
Qed.


Inductive eq_itree_bind_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| pbc_intro U t1 t2 (k1 k2: U -> _)
      (EQV: t1 ≅ t2)
      (REL: forall v, r (k1 v) (k2 v))
  : eq_itree_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eq_itree_bind_clo.

Lemma eq_itree_clo_bind E R: weak_respectful2 eq_itree_ (@eq_itree_bind_clo E R).
Proof.
  econstructor; try pmonauto.
  intros. dependent destruction PR.
  punfold EQV. unfold_eq_itree.
  rewrite !bind_unfold; inv EQV; simpobs.
  - eapply eq_itreeF__mono; eauto using rclo2.
  - simpl. fold_bind. pclearbot. eauto 7 using rclo2.
  - econstructor.
    intros x. specialize (REL0 x). fold_bind. pclearbot. eauto 7 using rclo2.
Qed.

Instance eq_itree_bind {E R S} :
  Proper (@eq_itree E R ==>
          pointwise_relation _ eq_itree ==>
          @eq_itree E S) ITree.bind.
Proof.
  repeat intro. pupto2_init.
  pupto2 eq_itree_clo_bind. econstructor; eauto.
  intros. pupto2_final. apply H0.
Qed.

Instance eq_itree_paco {E R} r:
  Proper (@eq_itree E R ==> @eq_itree E R ==> flip impl)
         (paco2 (eq_itree_ ∘ gres2 eq_itree_) r).
Proof.
  repeat intro. pupto2 eq_itree_clo_trans. eauto.
Qed.

Lemma bind_ret {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  pcofix CIH. intros.
  pfold. unfold_eq_itree. rewrite !bind_unfold. simpl.
  genobs s os. destruct os; simpl; eauto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  revert R S. pcofix CIH. intros.
  pfold. unfold_eq_itree. rewrite !bind_unfold.
  genobs s os; destruct os; unfold_bind; simpl; eauto.
  eapply Reflexive_eq_itreeF. eauto with refl.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  pupto2_init. rewrite bind_bind.
  pupto2 eq_itree_clo_bind. econstructor; eauto with refl.
  intros. rewrite ret_bind.
  pupto2_final. eauto with refl.
Qed.


Hint Rewrite @ret_bind : itree.
Hint Rewrite @tau_bind : itree.
Hint Rewrite @vis_bind : itree.
Hint Rewrite @bind_ret : itree.
