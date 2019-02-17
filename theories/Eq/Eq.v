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

(* TODO: Send to paco *)
Global Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

Global Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
Proof. auto. Qed.

Ltac auto_inj_pair2 :=
  repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
          end).

Definition go_sim {E R1 R2} (r : itree E R1 -> itree E R2 -> Prop) :
  itreeF E R1 (itree E R1) -> itreeF E R2 (itree E R2) -> Prop :=
  fun ot1 ot2 => r (go ot1) (go ot2).

Global Instance Equivalence_go_sim E R sim
       (Esim : @Equivalence (itree E R) sim) :
  Equivalence (go_sim sim).
Proof.
  constructor; red; unfold go_sim.
  - reflexivity.
  - symmetry; eauto.
  - etransitivity; eauto.
Qed.

Global Instance subrelation_go_sim E R sim sim' :
  @subrelation (itree E R) sim sim' ->
  subrelation (go_sim sim) (go_sim sim').
Proof. cbv; eauto. Qed.

Lemma pointwise_relation_fold {A B} {r: relation B} f g: (forall v:A, r (f v) (g v)) -> pointwise_relation _ r f g.
  Proof. red. eauto. Qed.

Section eq_itree.
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  Inductive eq_itreeF {I J} (sim : I -> J -> Prop) :
    itreeF E R1 I -> itreeF E R2 J -> Prop :=
  | EqRet : forall r1 r2, RR r1 r2 -> eq_itreeF sim (RetF r1) (RetF r2)
  | EqTau : forall m1 m2
      (REL: sim m1 m2), eq_itreeF sim (TauF m1) (TauF m2)
  | EqVis : forall {u} (e : E u) k1 k2
      (REL: forall v, sim (k1 v) (k2 v)),
      eq_itreeF sim (VisF e k1) (VisF e k2)
  .
  Hint Constructors eq_itreeF.

  Definition eq_itree_ (sim: itree E R1 -> itree E R2 -> Prop) :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eq_itreeF sim (observe t1) (observe t2).
  Hint Unfold eq_itree_.

  Lemma eq_itreeF_mono I J x0 x1 (r r' : I -> J -> Prop) :
    forall
      (IN: eq_itreeF r x0 x1)
      (LE: forall x2 x3, r x2 x3 -> r' x2 x3 : Prop),
        eq_itreeF r' x0 x1.
  Proof. pmonauto. Qed.

  Lemma eq_itree__mono : monotone2 eq_itree_.
  Proof. do 2 red. pmonauto. Qed.

  Definition eq_itree : itree E R1 -> itree E R2 -> Prop :=
    paco2 eq_itree_ bot2.

End eq_itree.

Hint Constructors eq_itreeF.
Hint Unfold eq_itree_.
Hint Resolve eq_itree__mono : paco.
Hint Unfold eq_itree.

Ltac unfold_eq_itree :=
  (try match goal with [|- eq_itree_ _ _ _ _ ] => red end);
  (repeat match goal with [H: eq_itree_ _ _ _ _ |- _ ] => red in H end).

Lemma flip_eq_itree {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (u : itree E R1) (v : itree E R2),
    eq_itree RR u v -> eq_itree (flip RR) v u.
Proof.
  pcofix self.
  intros u v euv. pfold. punfold euv. unfold_eq_itree.
  destruct euv; pclearbot; auto 10.
Qed.

Delimit Scope eq_itree_scope with eq_itree.
(* note(gmm): overriding `=` seems like a bad idea *)
Notation "t1 ≅ t2" := (eq_itree eq t1%itree t2%itree) (at level 70).
(* you can write ≅ using \cong in tex-mode *)

Section eq_itree_h.

Lemma itree_eq_tau {E R1 R2 RR} (t1 : itree E R1) (t2 : itree E R2) :
  eq_itree RR t1 t2 -> eq_itree RR (Tau t1) (Tau t2).
Proof.
  intro; pfold. econstructor. left. assumption.
Qed.

Lemma itree_eq_vis {E U R1 R2 RR} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eq_itree RR (k1 u) (k2 u)) ->
  eq_itree RR (Vis e k1) (Vis e k2).
Proof.
  intro H; pfold. econstructor. intros v. left. eapply H.
Qed.

End eq_itree_h.

Section eq_itree_eq.
  Context {E : Type -> Type} {R : Type}.

  Let eq_itreeF {I J} := @eq_itreeF E R _ eq I J.
  Let eq_itree_ := @eq_itree_ E R _ eq.
  Let eq_itree := @eq_itree E R _ eq.

  Global Instance Reflexive_eq_itreeF I (sim : I -> I -> Prop)
  : Reflexive sim -> Reflexive (eq_itreeF sim).
  Proof.
    red. destruct x; constructor; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF I (sim : I -> I -> Prop)
  : Symmetric sim -> Symmetric (eq_itreeF sim).
  Proof.
    red. inversion 2; constructor; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF I (sim : I -> I -> Prop)
  : Transitive sim -> Transitive (eq_itreeF sim).
  Proof.
    red. inversion 2; inversion 1; subst; repeat auto_inj_pair2; subst; constructor; eauto.
  Qed.

  Global Instance Reflexive_eq_itree_ sim
  : Reflexive sim -> Reflexive (eq_itree_ sim).
  Proof. repeat red. reflexivity. Qed.

  Global Instance Symmetric_eq_itree_ sim
  : Symmetric sim -> Symmetric (eq_itree_ sim).
  Proof. repeat red; symmetry; auto. Qed.

  Global Instance Transitive_eq_itree_ sim
  : Transitive sim -> Transitive (eq_itree_ sim).
  Proof. repeat red; etransitivity; eauto. Qed.

Global Instance Reflexive_eq_itree r : Reflexive (paco2 eq_itree_ r).
Proof.
  pcofix CIH; intros.
  pfold. do 2 red. destruct (observe x); eauto.
Qed.

Global Instance Symmetric_eq_itree r (SYMr : Symmetric r) :
  Symmetric (paco2 eq_itree_ r).
Proof.
  pcofix CIH; intros.
  pfold. do 2 red. punfold H0. inv H0; eauto.
  - constructor; destruct REL; eauto.
  - constructor. intros. destruct (REL v); eauto.
Qed.

Global Instance Transitive_eq_itree : Transitive eq_itree.
Proof.
  pcofix CIH. intros.
  pfold. red.
  punfold H0; red in H0.
  punfold H1; red in H1.
  destruct H0; inversion H1; subst; eauto.
  - pclearbot; eauto.
  - auto_inj_pair2; subst.
    subst; econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto.
Qed.

Global Instance Equivalence_eq_itree : Equivalence eq_itree.
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance eq_itree_go :
  Proper (go_sim eq_itree ==> eq_itree) (@go E R).
Proof.
  repeat intro. eauto.
Qed.

Global Instance eq_itree_observe :
  Proper (eq_itree ==> go_sim eq_itree) (@observe E R).
Proof.
  repeat intro. punfold H. pfold. eapply eq_itreeF_mono; eauto.
Qed.

Global Instance eq_itree_tauF :
  Proper (eq_itree ==> go_sim eq_itree) (@TauF E R _).
Proof.
  repeat intro. pfold. econstructor. eauto.
Qed.

Global Instance eq_itree_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eq_itree ==> go_sim eq_itree) (VisF e).
Proof.
  repeat intro. red in H. pfold. econstructor. left. apply H.
Qed.

Lemma itree_eta (t: itree E R): eq_itree t (go (observe t)).
Proof.
  pfold. red. cbn. apply Reflexive_eq_itreeF.
  auto using reflexivity.
Qed.

Inductive eq_itree_trans_clo (r : itree E R -> itree E R -> Prop) :
  itree E R -> itree E R -> Prop :=
| eq_itree_trans_clo_intro (t1 t2 t3 t4: itree E R)
      (EQVl: eq_itree t1 t2)
      (EQVr: eq_itree t4 t3)
      (RELATED: r t2 t3)
  : eq_itree_trans_clo r t1 t4
.
Hint Constructors eq_itree_trans_clo.

Lemma eq_itree_clo_trans : weak_respectful2 eq_itree_ eq_itree_trans_clo.
Proof.
  econstructor; [pmonauto|].
  intros. dependent destruction PR.
  apply GF in RELATED.
  punfold EQVl. punfold EQVr. red in RELATED. red. unfold_eq_itree.
  inversion EQVl; clear EQVl;
    inversion EQVr; clear EQVr;
    inversion RELATED; clear RELATED;
      subst; simpobs; try discriminate.

  - inversion H0; inversion H3; auto.
  - inversion H; inversion H3; subst; pclearbot; eauto using rclo2.

  - inversion H; inversion H3; subst; auto_inj_pair2; subst.
    pclearbot.
    econstructor. intros. specialize (REL v). specialize (REL0 v). pclearbot. eauto using rclo2.
Qed.

End eq_itree_eq.

Arguments eq_itree_clo_trans : clear implicits.

Hint Constructors eq_itree_trans_clo.

Lemma bind_unfold {E R S}
           (t : itree E R) (k : R -> itree E S) :
  observe (ITree.bind t k) = observe (ITree.bind_match k (ITree.bind' k) (observe t)).
Proof. eauto. Qed.

Lemma unfold_bind {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree.bind_match k (ITree.bind' k) (observe t).
Proof. rewrite itree_eta, bind_unfold, <-itree_eta. reflexivity. Qed.

Lemma ret_bind {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. apply unfold_bind. Qed.

Lemma tau_bind {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. apply @unfold_bind. Qed.

Lemma vis_bind {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. apply @unfold_bind. Qed.

Inductive eq_itree_bind_clo {E R} (r: relation (itree E R)) : relation (itree E R) :=
| pbc_intro U t1 t2 (k1 k2: U -> _)
      (EQV: t1 ≅ t2)
      (REL: forall v, r (k1 v) (k2 v))
  : eq_itree_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eq_itree_bind_clo.

Lemma eq_itree_clo_bind E R: weak_respectful2 (eq_itree_ eq) (@eq_itree_bind_clo E R).
Proof.
  econstructor; try pmonauto.
  intros. dependent destruction PR.
  punfold EQV. unfold_eq_itree.
  rewrite !bind_unfold; inv EQV; simpobs.
  - eapply eq_itreeF_mono; [eapply GF |]; eauto using rclo2.
  - simpl. fold_bind. pclearbot. eauto 7 using rclo2.
  - econstructor.
    intros x. specialize (REL0 x). fold_bind. pclearbot. eauto 7 using rclo2.
Qed.

Instance eq_itree_bind {E R S} :
  Proper (eq_itree eq ==>
          pointwise_relation _ (eq_itree eq) ==>
          eq_itree eq) (@ITree.bind E R S).
Proof.
  repeat intro. pupto2_init.
  pupto2 eq_itree_clo_bind. econstructor; eauto.
  intros. pupto2_final. apply H0.
Qed.

Instance eq_itree_paco {E R} r:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (paco2 (@eq_itree_ E R _ eq ∘ gres2 (eq_itree_ eq)) r).
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
  eapply Reflexive_eq_itreeF. auto using reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  pupto2_init. rewrite bind_bind.
  pupto2 eq_itree_clo_bind.
  econstructor.
  - reflexivity.
  - intros. rewrite ret_bind.
    pupto2_final. apply reflexivity.
Qed.

Lemma map_bind {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  pupto2_init. rewrite bind_bind.
  pupto2 eq_itree_clo_bind.
  econstructor.
  - reflexivity.
  - intros. rewrite ret_bind.
    pupto2_final. apply reflexivity.
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

Hint Rewrite @ret_bind : itree.
Hint Rewrite @tau_bind : itree.
Hint Rewrite @vis_bind : itree.
Hint Rewrite @bind_ret : itree.
