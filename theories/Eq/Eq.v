(* Coinductively defined equality on itrees,
   also called: strong bisimulation, extensional equality.
 *)

(* TODO: paco-fy this *)

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     ProofIrrelevance.

From Paco Require Import paco.

From ITree Require Import
     Core.

Lemma pointwise_relation_fold {A B} {r: relation B} f g: (forall v:A, r (f v) (g v)) -> pointwise_relation _ r f g.
  Proof. red. eauto. Qed.

Section eq_itree.
  Context {E : Type -> Type} {R : Type}.

  Inductive eq_itreeF' (sim : relation (itree E R)) : relation (itreeF E R (itree E R)) :=
  | EqRet : forall x, eq_itreeF' sim (RetF x) (RetF x)
  | EqTau : forall m1 m2
      (REL: sim m1 m2), eq_itreeF' sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2
      (REL: forall v, sim (k1 v) (k2 v)),
      eq_itreeF' sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eq_itreeF'.

  Global Instance Reflexive_eq_itreeF' sim
  : Reflexive sim -> Reflexive (eq_itreeF' sim).
  Proof.
    red. destruct x; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF' sim 
  : Symmetric sim -> Symmetric (eq_itreeF' sim).
  Proof.
    red. inversion 2; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF' sim
  : Transitive sim -> Transitive (eq_itreeF' sim).
  Proof.
    red. inversion 2; inversion 1; eauto.
    subst. dependent destruction H6. dependent destruction H7. eauto.
  Qed.

  Definition eq_itreeF (sim: relation (itree E R)) : relation (itree E R) :=
    fun t1 t2 => eq_itreeF' sim (observe t1) (observe t2).
  Hint Unfold eq_itreeF.

  Lemma eq_itreeF'_mono : forall x0 x1 r r'
    (IN: eq_itreeF' r x0 x1) (LE: forall x2 x3, (r x2 x3 : Prop) -> r' x2 x3 : Prop), eq_itreeF' r' x0 x1.
  Proof. pmonauto. Qed.

  Lemma eq_itreeF_mono : monotone2 eq_itreeF.
  Proof. do 2 red. pmonauto. Qed.

  Definition eq_itree : relation (itree E R) := paco2 eq_itreeF bot2.

End eq_itree.

Hint Constructors eq_itreeF'.
Hint Unfold eq_itreeF.
Hint Resolve eq_itreeF_mono : paco.
Hint Unfold eq_itree.

Definition go_sim {E R} (r: relation (itree E R)) : relation (itreeF E R (itree E R)) :=
  fun ot1 ot2 => r (go ot1) (go ot2).

Ltac unfold_eq_itree :=
  (try match goal with [|- eq_itreeF _ _ _ ] => red end);
  (repeat match goal with [H: eq_itreeF _ _ _ |- _ ] => red in H end).

Delimit Scope eq_itree_scope with eq_itree.
(* note(gmm): overriding `=` seems like a bad idea *)
Notation "t1 ≅ t2" := (eq_itree t1%itree t2%itree) (at level 70).
(* you can write ≅ using \cong in tex-mode *)

Lemma eq_itree_refl {E R} r x : paco2 (@eq_itreeF E R) r x x.
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
  destruct H0; dependent destruction H1; cbn; eauto.
  - pclearbot. eauto.
  - econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto.
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
  pfold. red. cbn. eapply Reflexive_eq_itreeF'; eauto with refl.
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

Lemma eq_itree_clo_trans E R: weak_respectful2 eq_itreeF (@eq_itree_trans_clo E R).
Proof.
  econstructor; [pmonauto|].
  intros. dependent destruction PR.
  apply GF in RELATED.
  punfold EQVl. punfold EQVr. unfold_eq_itree.
  genobs t1 ot1; genobs t2 ot2; genobs t3 ot3; genobs t4 ot4.
  dependent destruction EQVl; dependent destruction EQVr; pclearbot
  ; dependent destruction RELATED; cbn; eauto using rclo2.

  econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto using rclo2.
Qed.

Inductive eq_itree_bind_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| pbc_intro U t1 t2 (k1 k2: U -> _)
      (EQV: t1 ≅ t2)
      (REL: forall v, r (k1 v) (k2 v))
  : eq_itree_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eq_itree_bind_clo.

Lemma eq_itree_clo_bind E R: weak_respectful2 eq_itreeF (@eq_itree_bind_clo E R).
Proof.
  econstructor; try pmonauto.
  intros. dependent destruction PR.
  punfold EQV. unfold_eq_itree.
  rewrite !bind_unfold; inv EQV; simpobs.
  - eapply eq_itreeF_mono; eauto using rclo2.
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
         (paco2 (eq_itreeF ∘ gres2 eq_itreeF) r).
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
  eapply Reflexive_eq_itreeF'. eauto with refl.
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

(*
Import Hom.

Lemma hom_bind {E1 E2 R S} (f : E1 ~> itree E2)
      (s : itree E1 R) (k : R -> itree E1 S) :
  ((hom f _ (s >>= k))
   =
   (hom f _ s >>= fun x => hom f _ (k x)))%eq_itree.
Proof.
  simpl.
  generalize dependent s.
  cofix hom_bind.
  intros s.
  do 2 rewrite hom_def.
  destruct s.
  - do 2 rewrite bind_def.
    constructor. reflexivity.
  - rewrite bind_def.
    simpl.
    remember (f _ e) as t0 eqn:foo.
    clear foo.
    generalize dependent t0.
    (* nested cofix... *)
    cofix bind_assoc.
    intros t0.
    rewrite (bind_def t0).
    rewrite (bind_def (bind_itree _ _)).
    destruct t0; constructor.
    + apply hom_bind.
    + intros x0.
      apply bind_assoc.
    + apply bind_assoc.
  - do 2 rewrite bind_def.
    constructor.
    apply hom_bind.
Defined.

Lemma hom_ret {E1 E2 R} (f : E1 ~> itree E2) (r : R) :
  hom f _ (Ret r) = Ret r.
Proof.
  rewrite hom_def.
  constructor.
Defined.

Lemma hom_while {E1 E2 S} (phi : E1 ~> itree E2)
      (f : S -> bool) (body : S -> itree E1 S) : forall (s : S),
    (hom phi _ (while f body s)
     =
     while f (fun s' => hom phi _ (body s')) s)%eq_itree.
Proof.
  cofix hom_while.
  intros s.
  do 2 rewrite while_loop_unfold.
  destruct (f s); simpl.
  - remember (body s) as t eqn:Et; clear Et; generalize dependent t.
    cofix bind_hom.
    intros t.
    rewrite hom_def.
    destruct t.
    + rewrite (bind_def (hom _ _ _)).
      constructor.
      apply hom_while.
    + rewrite hom_def.
      rewrite (bind_def (Vis _ _)).
      simpl.
      remember (phi _ _) as u eqn:Eu; clear Eu; generalize dependent u.
      cofix bind_phi.
      intros u.
      do 2 rewrite bind_def.
      destruct u;
        constructor;
        [ auto | | ];
        try intro; apply bind_phi.
    + rewrite (bind_def (hom _ _ _)).
      constructor.
      apply bind_hom.
  - rewrite hom_def; constructor.
Qed.
*)
