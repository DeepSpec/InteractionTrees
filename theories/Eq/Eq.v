(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a coinductive notion of equivalence,
    which can be intuitively thought of as a form of extensional
    equality. It is weaker than [eq] (we will have to use setoid
    rewriting everywhere), but makes equivalences provable in practice.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Core.ITree.

From ITree Require Export
     Eq.Shallow.

Import ITreeNotations.

(* TODO: Send to paco *)
Global Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

Global Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
Proof. auto. Qed.
(* end hide *)

(** ** Coinductive reasoning with Paco *)

(** Similarly to the way we deal with cofixpoints explained in
    [Core.ITree], and also similarly to the definition of [itree]
    itself, coinductive properties are defined in two steps,
    as greatest fixed points of monotone relation transformers.

    - a _relation transformer_, a.k.a. _generating function_,
      is a function mapping relations to relations;
    - _monotonicity_ is with respect to relations ordered by
      set inclusion (a.k.a. implication, when viewed as predicates);
    - the Paco library provides a combinator defining the greatest
      fixed point when that function is indeed monotone.

    By thus avoiding [CoInductive] to define coinductive properties,
    Paco spares us from thinking about guardedness of proof terms,
    instead encoding a form of productivity visibly in types.
 *)

Section eq_itree.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eq_itree_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eq_itreeF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eq_itree_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

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

  (** [eq_itreeF] and [eq_itree_] are both monotone. *)

  Lemma eq_itreeF_mono I J x0 x1 (r r' : I -> J -> Prop) :
    forall
      (IN: eq_itreeF r x0 x1)
      (LE: forall x2 x3, r x2 x3 -> r' x2 x3 : Prop),
        eq_itreeF r' x0 x1.
  Proof. pmonauto. Qed.

  Lemma eq_itree__mono : monotone2 eq_itree_.
  Proof. do 2 red. pmonauto. Qed.

  (** Strong bisimulation on itrees. If [eq_itree RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)
  Definition eq_itree : itree E R1 -> itree E R2 -> Prop :=
    paco2 eq_itree_ bot2.

End eq_itree.

(* begin hide *)
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
(* end hide *)

Delimit Scope eq_itree_scope with eq_itree.

(** A notation of [eq_itree eq]. You can write [≅] using [[\cong]] in
    tex-mode *)
Notation "t1 ≅ t2" := (eq_itree eq t1%itree t2%itree) (at level 70).

Section eq_itree_h.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** [eq_itree] is a congruence for [itree] constructors. *)

Lemma eq_itree_Tau (t1 : itree E R1) (t2 : itree E R2) :
  eq_itree RR (Tau t1) (Tau t2) <-> eq_itree RR t1 t2.
Proof.
  split; intros H.
  - punfold H; inversion H; pclearbot; auto.
  - pfold. constructor; auto.
Qed.

Lemma eq_itree_Vis {U} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
      (forall u, eq_itree RR (k1 u) (k2 u))
  <-> eq_itree RR (Vis e k1) (Vis e k2).
Proof.
  split; intros H.
  - pfold. econstructor; left; eapply H.
  - punfold H; inversion H; pclearbot; auto_inj_pair2; subst; auto.
Qed.

Lemma eq_itree_Ret (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eq_itree E _ _ RR (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - pfold. constructor; auto.
  - punfold H; inversion H; pclearbot; auto_inj_pair2; subst; auto.
Qed.

(** *** "Up-to" principles for coinduction. *)

Inductive eq_itree_trans_clo (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| eq_itree_trans_clo_intro t1 t2 t3 t4
      (EQVl: eq_itree eq t1 t2)
      (EQVr: eq_itree eq t4 t3)
      (RELATED: r t2 t3)
  : eq_itree_trans_clo r t1 t4
.
Hint Constructors eq_itree_trans_clo.

Lemma eq_itree_clo_trans : weak_respectful2 (eq_itree_ RR) eq_itree_trans_clo.
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

Inductive eq_itree_bind_clo (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eq_itree RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eq_itree_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eq_itree_bind_clo.

Lemma eq_itree_clo_bind :
  weak_respectful2 (eq_itree_ RR) eq_itree_bind_clo.
Proof.
  econstructor; [pmonauto|].
  intros. dependent destruction PR.
  punfold EQV. unfold_eq_itree.
  rewrite !unfold_bind; inv EQV; simpobs.
  - eapply eq_itreeF_mono; [eapply GF |]; eauto using rclo2.
  - simpl. pclearbot. eauto 7 using rclo2.
  - econstructor.
    intros x. specialize (REL0 x). pclearbot. eauto 7 using rclo2.
Qed.

End eq_itree_h.

Arguments eq_itree_clo_trans : clear implicits.
Arguments eq_itree_clo_bind : clear implicits.

Hint Constructors eq_itree_trans_clo.
Hint Constructors eq_itree_bind_clo.

(** *** One-sided inversion *)

Lemma eq_itree_ret_inv1 {E R} (t : itree E R) r :
  t ≅ (Ret r) -> observe t = RetF r.
Proof.
  intros; punfold H; inversion H; subst; auto.
Qed.

Lemma eq_itree_vis_inv1 {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; punfold H; inversion H; subst; auto_inj_pair2; subst; pclearbot; eauto.
Qed.

Lemma eq_itree_tau_inv1 {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; punfold H; inversion H; pclearbot; eauto.
Qed.

(** ** Properties of relations *)

Section eq_itree_eq.

  (** *** Properties of relation transformers. *)

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

(** *** [eq_itree] is an equivalence relation *)

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

(** *** Congruence properties *)

Global Instance eq_itree_observe :
  Proper (eq_itree ==> going eq_itree) (@observe E R).
Proof.
  constructor; punfold H. pfold. eapply eq_itreeF_mono; eauto.
Qed.

Global Instance eq_itree_tauF :
  Proper (eq_itree ==> going eq_itree) (@TauF E R _).
Proof.
  constructor; pfold. econstructor. eauto.
Qed.

Global Instance eq_itree_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eq_itree ==> going eq_itree) (VisF e).
Proof.
  constructor; red in H. pfold; econstructor. left. apply H.
Qed.

  Global Instance observing_eq_itree_eq_ r `{Reflexive _ r} :
    subrelation (observing eq) (eq_itree_ r).
  Proof.
    repeat red; intros x _ [[]]; destruct observe; auto.
  Qed.

  Global Instance observing_eq_itree_eq :
    subrelation (observing eq) eq_itree.
  Proof.
    repeat red; intros; pfold. apply observing_eq_itree_eq_; auto.
    left; apply reflexivity.
  Qed.

(** *** Eta-expansion *)

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply observing_eq_itree_eq. econstructor. reflexivity. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eq_itree_eq.

(** ** Equations for core combinators *)

(* TODO (LATER): I keep these [...bind_] lemmas around temporarily
   in case I run some issues with slow typeclass resolution. *)

Lemma unfold_bind_ {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree._bind k (fun t => ITree.bind t k) (observe t).
Proof. rewrite unfold_bind. reflexivity. Qed.

Lemma ret_bind_ {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. rewrite ret_bind. reflexivity. Qed.

Lemma tau_bind_ {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. rewrite tau_bind. reflexivity. Qed.

Lemma vis_bind_ {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. rewrite vis_bind. reflexivity. Qed.

Lemma eq_itree_bind {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop)
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eq_itree RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eq_itree RS (k1 r1) (k2 r2)) ->
  @eq_itree E _ _ RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  repeat intro. pupto2_init.
  pupto2 eq_itree_clo_bind. econstructor; eauto.
  intros. pupto2_final; apply H0; auto.
Qed.

Instance eq_itree_eq_bind {E R S} :
  Proper (pointwise_relation _ (eq_itree eq) ==>
          eq_itree eq ==>
          eq_itree eq) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eq_itree_bind; eauto.
  intros; subst; auto.
Qed.

Lemma eq_itree_map {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop)
      (RS : S1 -> S2 -> Prop)
      f1 f2 t1 t2 :
  (forall r1 r2, RR r1 r2 -> RS (f1 r1) (f2 r2)) ->
  @eq_itree E _ _ RR t1 t2 ->
  eq_itree RS (ITree.map f1 t1) (ITree.map f2 t2).
Proof.
  unfold ITree.map; intros.
  eapply eq_itree_bind; eauto.
  intros; pfold; constructor; auto.
Qed.

Instance eq_itree_eq_map {E R S} :
  Proper (pointwise_relation _ eq ==>
          eq_itree eq ==>
          eq_itree eq) (@ITree.map E R S).
Proof.
  repeat intro; eapply eq_itree_map; eauto.
  intros; subst; auto.
Qed.

Instance eq_itree_paco {E R} r:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (paco2 (cgres2 (@eq_itree_ E R _ eq)) r).
Proof.
  repeat intro. pupto2 eq_itree_clo_trans. eauto.
Qed.

Lemma bind_ret {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  pcofix CIH. intros.
  pfold. unfold_eq_itree. rewrite !unfold_bind. simpl.
  genobs s os. destruct os; simpl; eauto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  pcofix CIH. intros.
  pfold. unfold_eq_itree.
  rewrite !unfold_bind. (* TODO: this is a bit slow (0.5s). *)
  genobs s os; destruct os; simpl; auto.
  apply Reflexive_eq_itreeF. auto using reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite ret_bind. reflexivity.
Qed.

Lemma map_bind {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite ret_bind. reflexivity.
Qed.

Lemma bind_map {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
  (ITree.map f (x <- t;; k x)) ≅ (x <- t;; ITree.map f (k x)).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_bind.
  reflexivity.
Qed.

Lemma map_ret {E A B} (f : A -> B) (a : A) :
    @ITree.map E _ _ f (Ret a) ≅ Ret (f a).
Proof.
  intros.
  unfold ITree.map.
  rewrite ret_bind; reflexivity.
Qed.

Hint Rewrite @ret_bind_ : itree.
Hint Rewrite @tau_bind_ : itree.
Hint Rewrite @vis_bind_ : itree.
Hint Rewrite @map_bind : itree.
Hint Rewrite @map_ret : itree.
Hint Rewrite @bind_ret : itree.
Hint Rewrite @bind_bind : itree.
