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


From ITree Require Import
     paco2_respectful
     Core.

From Paco Require Import paco.

Ltac absobs x ox := revert_until x; try rewrite (itree_eta x); generalize (observe x); clear x; simpl observe; intro ox; intros.

Section eq_itree.
  Context {E : Type -> Type} {R : Type}.

  Inductive eq_itreeF' (sim : relation (itree E R)) : relation (@itreeF E R (itree E R)) :=
  | EqRet : forall x, eq_itreeF' sim (RetF x) (RetF x)
  | EqTau : forall m1 m2
      (REL: sim m1 m2), eq_itreeF' sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2
      (REL: forall v, sim (k1 v) (k2 v)),
      eq_itreeF' sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eq_itreeF'.

  Global Instance Reflexive_eq_itreeF' sim
  : Reflexive sim -> Reflexive (@eq_itreeF' sim).
  Proof.
    red. destruct x; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF' sim 
  : Symmetric sim -> Symmetric (@eq_itreeF' sim).
  Proof.
    red. inversion 2; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF' sim
  : Transitive sim -> Transitive (@eq_itreeF' sim).
  Proof.
    red. inversion 2; inversion 1; eauto.
    subst. dependent destruction H6. dependent destruction H7. eauto.
  Qed.

  Definition eq_itreeF (sim: relation (itree E R)) : relation (itree E R) :=
    fun t1 t2 => eq_itreeF' sim (observe t1) (observe t2).
  Hint Unfold eq_itreeF.

  Lemma eq_itreeF'_mono : forall x0 x1 r r'
    (IN: @eq_itreeF' r x0 x1) (LE: forall x2 x3, (r x2 x3 : Prop) -> r' x2 x3 : Prop), eq_itreeF' r' x0 x1.
  Proof. pmonauto. Qed.

  Lemma eq_itreeF_mono : monotone2 eq_itreeF.
  Proof. do 2 red. pmonauto. Qed.

  Definition peq_itree r := paco2 eq_itreeF r.

  Definition eq_itree : relation (itree E R) := peq_itree bot2.

End eq_itree.

Hint Constructors eq_itreeF'.
Hint Unfold eq_itreeF.
Hint Resolve eq_itreeF_mono : paco.
Hint Unfold peq_itree.
Hint Unfold eq_itree.

Ltac unfold_eq_itree :=
  (try match goal with [|- eq_itreeF _ _ _ ] => red end);
  (repeat match goal with [H: eq_itreeF _ _ _ |- _ ] => red in H end).

Delimit Scope eq_itree_scope with eq_itree.
(* note(gmm): overriding `=` seems like a bad idea *)
Notation "t1 ≅ t2" := (eq_itree t1%itree t2%itree) (at level 70).
(* you can write ≅ using \cong in tex-mode *)

Global Instance Reflexive_eq_itree {E R} : Reflexive (@eq_itree E R).
Proof.
  pcofix CIH; intros.
  pfold. unfold_eq_itree. absobs x ox; destruct ox; eauto.
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
  pfold. punfold H0. punfold H1. unfold_eq_itree. absobs x ox; absobs y oy; absobs z oz.
  destruct H0; dependent destruction H1; cbn; eauto.
  - pclearbot. eauto.
  - econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto.
Qed.

Global Instance Equivalence_eq_itree {E R} :
  Equivalence (@eq_itree E R).
Proof.
  constructor; typeclasses eauto.
Qed.

(* The right notion of equality for coinductive types is the bisimilarity.
   We can axiomatize it in Coq as we axiomatize the function extensionality for function types.
   Though it is possible to use setoids for bisimilarity without using this axiom,
   assuming it would make proof engineering much simpler.
 *)
(* Axiom eq_itree_eq: forall E R (s t: itree E R), eq_itree s t -> s = t. *)

Definition bind_unfold {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k = ITree.bind_match k (ITree.bind' k) t.
Proof.
  setoid_rewrite (itree_eta (ITree.bind t k)). cbn.
  setoid_rewrite <-itree_eta. reflexivity.
Qed.

Lemma ret_bind {E R S} (r : R) :
  forall k : R -> itree E S,
    ITree.bind (Ret r) k = (k r).
Proof.
  intros. rewrite bind_unfold. reflexivity.
Qed.

Lemma tau_bind {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k = Tau (ITree.bind t k).
Proof.
  setoid_rewrite bind_unfold at 1. reflexivity.
Qed.

Lemma vis_bind {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  setoid_rewrite bind_unfold at 1. reflexivity.
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
  absobs t1 ot1; absobs t2 ot2; absobs t3 ot3; absobs t4 ot4.
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
  punfold EQV. unfold_eq_itree. absobs t1 ot1. absobs t2 ot2. inv EQV; cbn. 
  - eapply eq_itreeF_mono; eauto using rclo2.
  - fold_bind. pclearbot. eauto 7 using rclo2.
  - econstructor.
    intros x. specialize (REL0 x). fold_bind. pclearbot. eauto 7 using rclo2.
Qed.

Instance eq_itree_bind {E R S} :
  Proper (@eq_itree E R ==>
          pointwise_relation _ eq_itree ==>
          @eq_itree E S) ITree.bind.
Proof.
  repeat intro. pupto2_init.
  pupto2 (eq_itree_clo_bind E S). econstructor; eauto.
  intros. pupto2_final. apply H0.
Qed.

Instance eq_itree_tau {E R} :
  Proper (@eq_itree E R ==>
          @eq_itree E R) (fun t => Tau t).
Proof. repeat intro. pfold. unfold_eq_itree. cbn. eauto. Qed.

Instance eq_itree_vis {E R u} (e: E u) :
  Proper (pointwise_relation _ eq_itree ==>
          @eq_itree E R) (fun k => Vis e k).
Proof.
  repeat intro. pfold. econstructor.
  intros. left. apply H.
Qed.

Lemma bind_ret {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  pcofix CIH. intros.
  pfold. unfold_eq_itree. absobs s os. destruct os; cbn; eauto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  revert R S.
  pcofix CIH. intros.
  absobs s os; destruct os; cbn.
  - rewrite !ret_bind.
    eapply paco2_mon; [apply Reflexive_eq_itree|contradiction].
  - rewrite !tau_bind. pfold; unfold_eq_itree; simpl; eauto.
  - rewrite !vis_bind. pfold; unfold_eq_itree; simpl; eauto.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. revert R S.
  pcofix CIH. intros.
  pfold. unfold_eq_itree. absobs t ot. destruct ot.
  - rewrite !ret_bind. cbn; eauto.
  - rewrite !tau_bind. cbn; eauto.
  - rewrite !vis_bind. cbn; eauto.
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
