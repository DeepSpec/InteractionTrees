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
    [eqit], which can be intuitively thought of as a form of extensional
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
Local Open Scope itree.

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

Coercion is_true : bool >-> Sortclass.

Section eqit.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Inductive eqitF (b1 b2: bool) (hsim sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF b1 b2 hsim sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF b1 b2 hsim sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, sim (k1 v) (k2 v) \/ hsim (k1 v) (k2 v)):
      eqitF b1 b2 hsim sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
        (CHECK: b1)
        (REL: eqitF b1 b2 hsim sim (observe t1) ot2):
      eqitF b1 b2 hsim sim (TauF t1) ot2
  | EqTauR ot1 t2
        (CHECK: b2)
        (REL: eqitF b1 b2 hsim sim ot1 (observe t2)):
      eqitF b1 b2 hsim sim ot1 (TauF t2)
  .
  Hint Constructors eqitF.

  Definition eqit_ b1 b2 (hsim sim: itree E R1 -> itree E R2 -> Prop) :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 hsim sim (observe t1) (observe t2).
  Hint Unfold eqit_.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono b1 b2 x0 x1 (hsim hsim' sim sim' : itree E R1 -> itree E R2 -> Prop)
        (IN: eqitF b1 b2 hsim sim x0 x1)
        (LEh: forall x2 x3, hsim x2 x3 -> hsim' x2 x3 : Prop)
        (LE: forall x2 x3, sim x2 x3 -> sim' x2 x3 : Prop):
    eqitF b1 b2 hsim' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
    econstructor. intros. edestruct REL; eauto.
  Qed.

  Lemma eqit__mono b1 b2 hsim : monotone2 (eqit_ b1 b2 hsim).
  Proof. do 2 red. intros. eapply eqitF_mono; eauto. Qed.

  Hint Resolve eqit__mono : paco.
  
  Definition eqit b1 b2 : itree E R1 -> itree E R2 -> Prop :=
    paco2 (eqit_ b1 b2 bot2) bot2.

  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)
  
  Definition eq_itree := eqit false false.

  Definition eutt := eqit true true.

  Definition euttle := eqit false true.

End eqit.

(* begin hide *)
Hint Constructors eqitF.
Hint Unfold eqit_.
Hint Resolve eqit__mono : paco.
Hint Unfold eqit.
Hint Unfold eq_itree.
Hint Unfold eutt.
Hint Unfold euttle.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma eqit_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2:
  forall (u : itree E R1) (v : itree E R2),
    eqit (flip RR) b2 b1 v u -> eqit RR b1 b2 u v.
Proof.
  pcofix self; pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
Qed.

Lemma eqit_mon {E R1 R2} RR RR' (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <2= RR'):
  @eqit E R1 R2 RR b1 b2 <2= eqit RR' b1' b2'.
Proof.
  pcofix self. pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
Qed.

(* end hide *)

Delimit Scope eq_itree_scope with eq_itree.

(** A notation of [eq_itree eq]. You can write [≅] using [[\cong]] in
    tex-mode *)

Open Scope itree.

Infix "≅" := (eq_itree eq) (at level 70) : itree_scope.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Infix "≲" := (euttle eq) (at level 70) : itree_scope.

Section eqit_closure.
  
Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** *** "Up-to" principles for coinduction. *)

Inductive eqit_trans_clo b1 b2 b1' b2' (r : itree E R1 -> itree E R2 -> Prop)
  : itree E R1 -> itree E R2 -> Prop :=
| eqit_trans_clo_intro t1 t2 t1' t2'
      (EQVl: eqit eq b1 b1' t1 t1')
      (EQVr: eqit eq b2 b2' t2 t2')
      (RELATED: r t1' t2')
  : eqit_trans_clo b1 b2 b1' b2' r t1 t2
.
Hint Constructors eqit_trans_clo.

Definition eqitC b1 b2 := eqit_trans_clo b1 b2 false false.
Hint Unfold eqitC.

Lemma eqitC_wcompat b1 b2 gH (CLO: eqitC b1 b2 gH <2= gH) :
  wcompatible2 (@eqit_ E R1 R2 RR b1 b2 gH) (eqitC b1 b2).
Proof.
  econstructor. pmonauto.
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction RELATED before r; intros; clear t1' t2'.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. econstructor. gclo.
    econstructor; cycle -1; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; eauto.
    remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; eauto.
    econstructor. intros. pclearbot.
    destruct (REL1 v).
    + left. gclo. econstructor; eauto with paco.
    + right. apply CLO. eauto.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. punfold REL.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. punfold REL.
Qed.

Hint Resolve eqitC_wcompat : paco.

Lemma eqitC_bot_clo b1 b2: eqitC b1 b2 bot2 <2= bot2.
Proof.
  intros. destruct PR. contradiction.
Qed.
Hint Resolve eqitC_bot_clo : paco.

Lemma eqitC_dist b1 b2:
  forall r1 r2, eqitC b1 b2 (r1 \2/ r2) <2= (eqitC b1 b2 r1 \2/ eqitC b1 b2 r2).
Proof.
  intros. destruct PR. destruct RELATED; eauto.
Qed.

Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans b1 b2 gH (CLO: eqitC b1 b2 gH <2= gH) :
  eqit_trans_clo b1 b2 false false <3= gupaco2 (eqit_ RR b1 b2 gH) (eqitC b1 b2).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End eqit_closure.

Hint Unfold eqitC.
Hint Resolve eqitC_wcompat : paco.
Hint Resolve eqitC_bot_clo : paco.
Hint Resolve eqitC_dist : paco.
Arguments eqit_clo_trans : clear implicits.
Hint Constructors eqit_trans_clo.

(** *** One-sided inversion *)

Lemma eq_itree_inv_ret {E R} (t : itree E R) r :
  t ≅ (Ret r) -> observe t = RetF r.
Proof.
  intros; punfold H; inv H; try inv CHECK; eauto.
Qed.

Lemma eq_itree_inv_vis {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; punfold H; inv H; auto_inj_pair2; subst; try inv CHECK.
  eexists; split; eauto.
  intros. destruct (REL u); try contradiction; pclearbot; eauto.
Qed.

Lemma eq_itree_inv_tau {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
Qed.

Lemma eqit_inv_tauL {E R1 R2 RR} b1 t1 t2 :
  @eqit E R1 R2 RR b1 true (Tau t1) t2 -> eqit RR b1 true t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before b1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt1. punfold_reverse H.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma eqit_inv_tauR {E R1 R2 RR} b2 t1 t2 :
  @eqit E R1 R2 RR true b2 t1 (Tau t2) -> eqit RR true b2 t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t2) as tt2. genobs t1 ot1.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt2. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt2. punfold_reverse H.
Qed.

Lemma eqit_tauL {E R1 R2 RR} b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR true b2 t1 t2 -> eqit RR true b2 (Tau t1) t2.
Proof.
  intros. pstep. econstructor; eauto. punfold H.
Qed.

Lemma eqit_tauR {E R1 R2 RR} b1 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR b1 true t1 t2 -> eqit RR b1 true t1 (Tau t2).
Proof.
  intros. pstep. econstructor; eauto. punfold H.
Qed.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (@eqit E R R eq).

Global Instance Reflexive_eqitF b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq b1 b2 bot2 sim).
Proof.
  red. destruct x; constructor; eauto.
Qed.

Global Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b bot2 sim).
Proof.
  red. induction 2; constructor; subst; eauto.
  intros. destruct (REL v); try contradiction; eauto.
Qed.

Global Instance Reflexive_eqit_ b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqit_ eq b1 b2 bot2 sim).
Proof. repeat red. reflexivity. Qed.

Global Instance Symmetric_eqit_ b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqit_ eq b b bot2 sim).
Proof. repeat red; symmetry; auto. Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen b1 b2 (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gpaco2 (eqit_ eq b1 b2 bot2) (eqitC b1 b2) r rg).
Proof.
  repeat intro. eapply gpaco2_mon_bot; eauto with paco.
  revert x. gcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto with paco.
Qed.

Global Instance Reflexive_eqit b1 b2 : Reflexive (eqit b1 b2).
Proof.
  red; intros. ginit. apply Reflexive_eqit_gen.
Qed.

Global Instance Symmetric_eqit b : Symmetric (eqit b b).
Proof.
  red; intros. apply eqit_flip.
  eapply eqit_mon, H; eauto.
  intros; subst. reflexivity.
Qed.

Global Instance Transitive_eqit (b: bool) : Transitive (eqit false b).
Proof.
  ginit. intros.
  guclo eqit_clo_trans; eauto.
  econstructor; [reflexivity|..]; eauto with paco.
  apply eqit_flip. eapply eqit_mon, H1; eauto. intros; subst; reflexivity.
Qed.

Global Instance Equivalence_eqit : Equivalence (eqit false false).
Proof.
  constructor; try typeclasses eauto.
Qed.

(** *** Congruence properties *)

Global Instance eqit_observe b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@observe E R).
Proof.
  constructor; punfold H.
Qed.

Global Instance eqit_tauF b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@TauF E R _).
Proof.
  constructor; pstep. econstructor. eauto.
Qed.

Global Instance eqit_VisF b1 b2 {u} (e: E u) :
  Proper (pointwise_relation _ (eqit b1 b2) ==> going (eqit b1 b2)) (VisF e).
Proof.
  constructor; red in H. unfold eqit in *. pstep; econstructor; eauto.
Qed.

Global Instance observing_sub_eqit l r :
  subrelation (observing eq) (eqit l r).
Proof.
  repeat red; intros. destruct H.
  pstep. red. rewrite H. apply Reflexive_eqitF. left. apply reflexivity.
Qed.

Global Instance eq_sub_eqit l r:
  subrelation (eqit false false) (eqit l r).
Proof.
  ginit. gcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; eauto 7 with paco.
Qed.  

Global Instance eqit_sub_eutt l r:
  subrelation (eqit l r) (eqit true true).
Proof.
  ginit. gcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; pclearbot; eauto 7 with paco.
Qed.  

(** ** Eta-expansion *)

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply observing_sub_eqit. econstructor. reflexivity. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eqit_eq.

Hint Resolve Reflexive_eqit Reflexive_eqit_gen : reflexivity.

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

Instance eqit_gpaco {E R1 R2 RS} b1 b2 r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 bot2) (eqitC b1 b2) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. econstructor; cycle -1; eauto.
  - eapply eqit_mon, H; eauto; discriminate.
  - eapply eqit_mon, H0; eauto; discriminate.
Qed.

Instance eqit_eqit {E R} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R R eq b1 b2).
Proof.
  ginit. intros. rewrite H1, H0. gfinal. eauto.
Qed.

Section eqit_h.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** [eqit] is a congruence for [itree] constructors. *)

Lemma eqit_Tau b1 b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR b1 b2 (Tau t1) (Tau t2) <-> eqit RR b1 b2 t1 t2.
Proof.
  split; intros H.
  - punfold H. red in H. simpl in *. pstep. red.
    remember (TauF t1) as ot1. remember (TauF t2) as ot2.
    hinduction H before RR; intros; subst; try inv Heqot1; try inv Heqot2; eauto.
    + pclearbot. punfold REL.
    + inv H; eauto.
    + inv H; eauto.
  - pstep. constructor; auto.
Qed.

Lemma eqit_Vis b1 b2 {U} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
      (forall u, eqit RR b1 b2 (k1 u) (k2 u))
  <-> eqit RR b1 b2 (Vis e k1) (Vis e k2).
Proof.
  split; intros H.
  - pstep. econstructor. left. left. eapply H.
  - punfold H. inv H; auto_inj_pair2; subst; auto.
    intros. pclearbot. eauto.
Qed.

Lemma eqit_Ret b1 b2 (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eqit E _ _ RR b1 b2 (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - pstep. constructor; auto.
  - punfold H. inversion H; auto_inj_pair2; subst; auto.
Qed.

(** *** "Up-to" principles for coinduction. *)

Inductive eqit_bind_clo b1 b2 (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eqit RU b1 b2 t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eqit_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eqit_bind_clo.

Lemma eqit_clo_bind b1 b2: eqit_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 bot2) (eqitC b1 b2).
Proof.
  gcofix CIH. intros. destruct PR.
  do 2 rewrite (itree_eta (x <- _;; _ x)), unfold_bind_.
  punfold EQV. unfold_eqit.
  hinduction EQV before CIH; intros; pclearbot.
  - rewrite <- !itree_eta. eauto with paco.
  - gstep. econstructor. eauto with paco.
  - gstep. econstructor. left. eauto with paco.
  - destruct b1; try discriminate.
    guclo eqit_clo_trans. econstructor; cycle -1; eauto; try reflexivity.
    eapply eqit_tauL. rewrite unfold_bind_, <-itree_eta. reflexivity.
  - destruct b2; try discriminate.
    guclo eqit_clo_trans. econstructor; cycle -1; eauto; try reflexivity.
    eapply eqit_tauL. rewrite unfold_bind_, <-itree_eta. reflexivity.
Qed.

End eqit_h.

Arguments eqit_clo_bind : clear implicits.
Hint Constructors eqit_bind_clo.

Lemma eqit_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit RR b1 b2 t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit RS b1 b2 (k1 r1) (k2 r2)) ->
  @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit. guclo eqit_clo_bind. unfold eqit in *.
  econstructor; eauto with paco.
Qed.

Instance eqit_bind {E R S} b1 b2 :
  Proper (pointwise_relation _ (eqit eq b1 b2) ==>
          eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

Instance eqit_bind_ {E R S} b1 b2 k :
  Proper (going (eqit eq b1 b2) ==>
          eqit eq b1 b2) (@ITree._bind E R S k (@ITree.bind' E R S k)).
Proof.
  ginit. intros. destruct H0.
  rewrite (itree_eta' x), (itree_eta' y), <- !unfold_bind_.
  guclo eqit_clo_bind. econstructor; eauto.
  intros. subst. apply reflexivity.
Qed.

Lemma eqit_map {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      f1 f2 t1 t2 :
  (forall r1 r2, RR r1 r2 -> RS (f1 r1) (f2 r2)) ->
  @eqit E _ _ RR b1 b2 t1 t2 ->
  eqit RS b1 b2 (ITree.map f1 t1) (ITree.map f2 t2).
Proof.
  unfold ITree.map; intros.
  eapply eqit_bind'; eauto.
  intros; pstep; constructor; auto.
Qed.

Instance eqit_eq_map {E R S} b1 b2 :
  Proper (pointwise_relation _ eq ==>
          eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Lemma bind_ret2 {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_bind_. gstep. repeat red.
  genobs s os. destruct os; simpl; eauto with paco.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  ginit. gcofix CIH. intros. rewrite !unfold_bind_.
  gstep. repeat red. destruct (observe s); simpl; eauto with paco.
  apply reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_. reflexivity.
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
