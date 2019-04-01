(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a weaker, coinductive notion of equivalence,
    [eq_itree], which can be intuitively thought of as a form of extensional
    equality. We shall rely extensively on setoid rewriting.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

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
    [Core.ITreeDefinition], coinductive properties are defined in two steps,
    as greatest fixed points of monotone relation transformers.

    - a _relation transformer_, a.k.a. _generating function_,
      is a function mapping relations to relations
      [gf : (i -> i -> Prop) -> (i -> i -> Prop)];
    - _monotonicity_ is with respect to relations ordered by set inclusion
      (a.k.a. implication, when viewed as predicates)
      [(r1 <2= r2) -> (gf r1 <2= gf r2)];
    - the Paco library provides a combinator [paco2] defining the greatest
      fixed point [paco2 gf] when [gf] is indeed monotone.

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

  Inductive eq_itreeF (sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
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

  Lemma eq_itreeF_mono x0 x1 (r r' : itree E R1 -> itree E R2 -> Prop) :
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
    cpn2 eq_itree_ bot2.

  Lemma eq_itree_fold :
    eq_itree <2= cpn2 eq_itree_ bot2.
  Proof. intros. apply PR. Qed.
  Hint Resolve eq_itree_fold.
  
End eq_itree.

(* begin hide *)
Hint Constructors eq_itreeF.
Hint Unfold eq_itree_.
Hint Resolve eq_itree__mono : paco.
Hint Unfold eq_itree.
Hint Resolve eq_itree_fold.

Ltac unfold_eq_itree :=
  (try match goal with [|- eq_itree_ _ _ _ _ ] => red end);
  (repeat match goal with [H: eq_itree_ _ _ _ _ |- _ ] => red in H end).

Lemma flip_eq_itree {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (u : itree E R1) (v : itree E R2),
    eq_itree RR u v -> eq_itree (flip RR) v u.
Proof.
  ucofix self.
  intros u v euv. uunfold euv.
  repeat red; destruct euv; eauto 10 with paco.
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
  - uunfold H; inversion H; eauto.
  - ustep. constructor; auto.
Qed.

Lemma eq_itree_Vis {U} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
      (forall u, eq_itree RR (k1 u) (k2 u))
  <-> eq_itree RR (Vis e k1) (Vis e k2).
Proof.
  split; intros H.
  - ustep. econstructor. eauto with paco. 
  - uunfold H. inversion H; auto_inj_pair2; subst; auto.
Qed.

Lemma eq_itree_Ret (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eq_itree E _ _ RR (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - ustep. constructor; auto.
  - uunfold H. inversion H; auto_inj_pair2; subst; auto.
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

Lemma eq_itree_clo_trans : eq_itree_trans_clo <3= cpn2 (eq_itree_ RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. dependent destruction PR.
  uunfold EQVl. uunfold EQVr. unfold_eq_itree.
  destruct EQVl;
    inversion EQVr; clear EQVr;
    inversion RELATED; clear RELATED;
      subst; simpobs; try discriminate.

  - inversion H0; inversion H1; auto.
  - inversion H; inversion H3; subst; eauto with rclo.
  - inversion H; inversion H3; subst; auto_inj_pair2; subst.
    econstructor. intros. specialize (REL v). specialize (REL0 v).
    eauto with rclo.
Qed.

Inductive eq_itree_bind_clo (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eq_itree RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eq_itree_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eq_itree_bind_clo.

Lemma eq_itree_clo_bind : eq_itree_bind_clo <3= cpn2 (eq_itree_ RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. dependent destruction PR.
  uunfold EQV. unfold_eq_itree.
  rewrite !unfold_bind; destruct EQV; simpobs.
  - eapply eq_itreeF_mono; [eapply REL |]; eauto with rclo.
  - simpl. eauto 8 with rclo.
  - econstructor.
    intros x. specialize (REL0 x). eauto 7 with rclo.
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
  intros; uunfold H; inversion H; subst; auto.
Qed.

Lemma eq_itree_vis_inv1 {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; uunfold H; inversion H; subst; auto_inj_pair2; subst; eauto.
Qed.

Lemma eq_itree_tau_inv1 {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; uunfold H; inversion H; eauto.
Qed.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eq_itree_eq.

  (** *** Properties of relation transformers. *)

  Context {E : Type -> Type} {R : Type}.

  Local Notation eq_itree := (@eq_itree E R R eq).

  Global Instance Reflexive_eq_itreeF (sim : itree E R -> itree E R -> Prop)
  : Reflexive sim -> Reflexive (eq_itreeF eq sim).
  Proof.
    red. destruct x; constructor; eauto.
  Qed.

  Global Instance Symmetric_eq_itreeF (sim : itree E R -> itree E R -> Prop)
  : Symmetric sim -> Symmetric (eq_itreeF eq sim).
  Proof.
    red. inversion 2; constructor; eauto.
  Qed.

  Global Instance Transitive_eq_itreeF (sim : itree E R -> itree E R -> Prop)
  : Transitive sim -> Transitive (eq_itreeF eq sim).
  Proof.
    red. inversion 2; inversion 1; subst; repeat auto_inj_pair2; subst; constructor; eauto.
  Qed.

  Global Instance Reflexive_eq_itree_ (sim : itree E R -> itree E R -> Prop)
  : Reflexive sim -> Reflexive (eq_itree_ eq sim).
  Proof. repeat red. reflexivity. Qed.

  Global Instance Symmetric_eq_itree_ (sim : itree E R -> itree E R -> Prop)
  : Symmetric sim -> Symmetric (eq_itree_ eq sim).
  Proof. repeat red; symmetry; auto. Qed.

  Global Instance Transitive_eq_itree_ (sim : itree E R -> itree E R -> Prop)
  : Transitive sim -> Transitive (eq_itree_ eq sim).
  Proof. repeat red; etransitivity; eauto. Qed.

(** *** [eq_itree] is an equivalence relation *)

Global Instance Reflexive_eq_itree_gen (r: itree E R -> itree E R -> Prop) :
  Reflexive (cpn2 (eq_itree_ eq) r).
Proof.
  ucofix CIH; intros.
  repeat red. destruct (observe x); eauto with paco.
Qed.

Global Instance Reflexive_eq_itree_gen_guard (r: itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eq_itree_ eq) r).
Proof.
  repeat intro. apply Reflexive_eq_itreeF, Reflexive_eq_itree_gen.
Qed.
  
Global Instance Reflexive_eq_itree : Reflexive eq_itree.
Proof.
  apply Reflexive_eq_itree_gen.
Qed.

Global Instance Symmetric_eq_itree : Symmetric eq_itree.
Proof.
  ucofix CIH; intros.
  repeat red. uunfold H0. inv H0; eauto with paco.
Qed.

Global Instance Transitive_eq_itree : Transitive eq_itree.
Proof.
  ucofix CIH. intros.
  repeat red.
  uunfold H0; repeat red in H0.
  uunfold H1; repeat red in H1.
  destruct H0; inversion H1; subst; eauto.
  - eauto with paco.
  - auto_inj_pair2; subst.
    subst; econstructor. intros. specialize (REL v). specialize (REL0 v). eauto with paco.
Qed.

Global Instance Equivalence_eq_itree : Equivalence eq_itree.
Proof.
  constructor; try typeclasses eauto.
Qed.

(** *** Congruence properties *)

Global Instance eq_itree_observe :
  Proper (eq_itree ==> going eq_itree) (@observe E R).
Proof.
  constructor; uunfold H. ustep. eapply eq_itreeF_mono; eauto.
Qed.

Global Instance eq_itree_tauF :
  Proper (eq_itree ==> going eq_itree) (@TauF E R _).
Proof.
  constructor; ustep. econstructor. eauto.
Qed.

Global Instance eq_itree_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eq_itree ==> going eq_itree) (VisF e).
Proof.
  constructor; red in H. ustep; econstructor. apply H.
Qed.

  Global Instance observing_eq_itree_eq_ (r: itree E R -> itree E R -> Prop) `{Reflexive _ r} :
    subrelation (observing eq) (eq_itree_ eq r).
  Proof.
    repeat red; intros x _ [[]]; destruct observe; auto.
  Qed.
  
  Global Instance observing_eq_itree_eq :
    subrelation (observing eq) eq_itree.
  Proof.
    repeat red; intros; ustep. apply observing_eq_itree_eq_; auto.
    apply Reflexive_eq_itree.
  Qed.

(** ** Eta-expansion *)

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply observing_eq_itree_eq. econstructor. reflexivity. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eq_itree_eq.

Hint Resolve Reflexive_eq_itree Reflexive_eq_itree_gen : reflexivity.

(** ** Equations for core combinators *)

(* TODO (LATER): I keep these [...bind_] lemmas around temporarily
   in case I run some issues with slow typeclass resolution. *)

Lemma unfold_bind_ {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree._bind k (fun t => ITree.bind t k) (observe t).
Proof. rewrite unfold_bind. reflexivity. Qed.

Lemma bind_ret_ {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. rewrite bind_ret. reflexivity. Qed.

Lemma bind_tau_ {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. rewrite bind_tau. reflexivity. Qed.

Lemma bind_vis_ {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. rewrite bind_vis. reflexivity. Qed.

Lemma unfold_forever_ {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ (t >>= fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (_ >>= _)).
  reflexivity.
Qed.

Lemma eq_itree_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop)
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eq_itree RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eq_itree RS (k1 r1) (k2 r2)) ->
  @eq_itree E _ _ RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  uclo eq_itree_clo_bind. eauto 7 with paco.
Qed.

Instance eq_itree_bind {E R S} :
  Proper (pointwise_relation _ (eq_itree eq) ==>
          eq_itree eq ==>
          eq_itree eq) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eq_itree_bind'; eauto.
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
  eapply eq_itree_bind'; eauto.
  intros; ustep; constructor; auto.
Qed.

Instance eq_itree_eq_map {E R S} :
  Proper (pointwise_relation _ eq ==>
          eq_itree eq ==>
          eq_itree eq) (@ITree.map E R S).
Proof.
  repeat intro; eapply eq_itree_map; eauto.
  intros; subst; auto.
Qed.

Definition eq_itree_cpn_ {E R1 R2 RS} :
  Proper (eq ==> eq_itree eq ==> eq_itree eq ==> flip impl)
         (cpn2 (@eq_itree_ E R1 R2 RS)).
Proof.
  repeat intro; subst. uclo eq_itree_clo_trans. eauto.
Qed.

Definition eq_itree_gcpn_ {E R1 R2 RS} :
  Proper (eq ==> eq_itree eq ==> eq_itree eq ==> flip impl)
         (gcpn2 (@eq_itree_ E R1 R2 RS)).
Proof.
  repeat intro; subst. uclo eq_itree_clo_trans. eauto.
Qed.

Instance eq_itree_cpn {E R1 R2 RS} :
  Proper (eq ==> eq_itree eq ==> eq_itree eq ==> iff)
         (cpn2 (@eq_itree_ E R1 R2 RS)).
Proof.
  split; apply eq_itree_cpn_; auto using symmetry.
Qed.

Instance eq_itree_gcpn {E R1 R2 RS}:
  Proper (eq ==> eq_itree eq ==> eq_itree eq ==> iff)
         (gcpn2 (@eq_itree_ E R1 R2 RS)).
Proof.
  split; apply eq_itree_gcpn_; auto using symmetry.
Qed.

Lemma bind_ret2 {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  ucofix CIH. intros.
  rewrite !unfold_bind. repeat red.
  genobs s os. destruct os; simpl; eauto with paco.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  ucofix CIH. intros.
  unfold_eq_itree.
  rewrite !unfold_bind.
  repeat red. genobs s os; destruct os; simpl; eauto with paco.
  apply Reflexive_eq_itreeF. eauto with reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret. reflexivity.
Qed.

Lemma map_bind {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
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
  rewrite bind_ret; reflexivity.
Qed.

Hint Rewrite @bind_ret_ : itree.
Hint Rewrite @bind_tau_ : itree.
Hint Rewrite @bind_vis_ : itree.
Hint Rewrite @bind_map : itree.
Hint Rewrite @map_ret : itree.
Hint Rewrite @bind_ret2 : itree.
Hint Rewrite @bind_bind : itree.
