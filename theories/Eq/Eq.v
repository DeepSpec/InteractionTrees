
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
     Basics.Basics
     Basics.HeterogeneousRelations
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

  Inductive eqitF (b1 b2: bool) vclo (sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF b1 b2 vclo sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF b1 b2 vclo sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, vclo sim (k1 v) (k2 v) : Prop):
      eqitF b1 b2 vclo sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
        (CHECK: b1)
        (REL: eqitF b1 b2 vclo sim (observe t1) ot2):
      eqitF b1 b2 vclo sim (TauF t1) ot2
  | EqTauR ot1 t2
        (CHECK: b2)
        (REL: eqitF b1 b2 vclo sim ot1 (observe t2)):
      eqitF b1 b2 vclo sim ot1 (TauF t2)
  .
  Hint Constructors eqitF: core.

  Definition eqit_ b1 b2 vclo sim :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 vclo sim (observe t1) (observe t2).
  Hint Unfold eqit_: core.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono b1 b2 x0 x1 vclo vclo' sim sim'
        (IN: eqitF b1 b2 vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    eqitF b1 b2 vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma eqit__mono b1 b2 vclo (MON: monotone2 vclo) : monotone2 (eqit_ b1 b2 vclo).
  Proof. do 2 red. intros. eapply eqitF_mono; eauto. Qed.

  Hint Resolve eqit__mono : paco.

  Lemma eqit_idclo_mono: monotone2 (@id (itree E R1 -> itree E R2 -> Prop)).
  Proof. unfold id. eauto. Qed.

  Hint Resolve eqit_idclo_mono : paco.

  Definition eqit b1 b2 : itree E R1 -> itree E R2 -> Prop :=
    paco2 (eqit_ b1 b2 id) bot2.

  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)

  Definition eq_itree := eqit false false.

  Definition eutt := eqit true true.

  Definition euttge := eqit true false.

End eqit.

(* begin hide *)
Hint Constructors eqitF: core.
Hint Unfold eqit_: core.
Hint Resolve eqit__mono : paco.
Hint Resolve eqit_idclo_mono : paco.
Hint Unfold eqit: core.
Hint Unfold eq_itree: core.
Hint Unfold eutt: core.
Hint Unfold euttge: core.
Hint Unfold id: core.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma fold_eqitF:
  forall {E R1 R2} (RR: R1 -> R2 -> Prop) b1 b2 (t1 : itree E R1) (t2 : itree E R2) ot1 ot2,
    eqitF RR b1 b2 id (upaco2 (eqit_ RR b1 b2 id) bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    eqit RR b1 b2 t1 t2.
Proof.
  intros * eq -> ->; pfold; auto.
Qed.

Instance eqitF_Proper_R {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> (eq_rel ==> eq_rel) ==> eq_rel ==> eq_rel)
    (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; unfold subrelationH; intros.
  - induction H0; try auto.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
  - induction H0; try auto.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
Qed.

Instance eqitF_Proper_R2 {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; try auto.
    econstructor. apply H. assumption.
  - induction H0; try auto.
    econstructor. apply H. assumption.
Qed.

Instance eqit_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> iff) (@eqit E R1 R2).
Proof.
  repeat red.
  intros. subst.
  split.
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H1. red in H1. red.
     hinduction H1 before CIH; intros; eauto.
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL.
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL.
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H1. red in H1. red.
     hinduction H1 before CIH; intros; eauto.
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL.
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL.
Qed.

Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  unfold eutt. repeat red.
  intros. split; intros; subst.
  - rewrite <- H. assumption.
  - rewrite H. assumption.
Qed.


Definition flip_clo {A B C} clo r := @flip A B C (clo (@flip B A C r)).

Lemma eqitF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 vclo r:
  flip (eqitF (flip RR) b2 b1 (flip_clo vclo) (flip r)) <2= @eqitF E R1 R2 RR b1 b2 vclo r.
Proof.
  intros. induction PR; eauto.
Qed.

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

Hint Unfold flip: core.

(* end hide *)

(*
  The following line removes the warning on >=8.10, but is incompatible for <8.10
 *)
(* Declare Scope eq_itree_scope. *)
Delimit Scope eq_itree_scope with eq_itree.

(** A notation of [eq_itree eq]. You can write [≅] using [[\cong]] in
    tex-mode *)

Open Scope itree.

Infix "≅" := (eq_itree eq) (at level 70) : itree_scope.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Infix "≳" := (euttge eq) (at level 70) : itree_scope.

Section eqit_closure.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(** *** "Up-to" principles for coinduction. *)

Inductive eqit_trans_clo b1 b2 b1' b2' (r : itree E R1 -> itree E R2 -> Prop)
  : itree E R1 -> itree E R2 -> Prop :=
| eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' t1 t1')
      (EQVr: eqit RR2 b2 b2' t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y)
  : eqit_trans_clo b1 b2 b1' b2' r t1 t2
.
Hint Constructors eqit_trans_clo: core.

Definition eqitC b1 b2 := eqit_trans_clo b1 b2 false false.
Hint Unfold eqitC: core.

Lemma eqitC_mon b1 b2 r1 r2 t1 t2
      (IN: eqitC b1 b2 r1 t1 t2)
      (LE: r1 <2= r2):
  eqitC b1 b2 r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve eqitC_mon : paco.

Lemma eqitC_wcompat b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC b1 b2) vclo <3= compose vclo (eqitC b1 b2)):
  wcompatible2 (@eqit_ E R1 R2 RR b1 b2 vclo) (eqitC b1 b2).
Proof.
  econstructor. pmonauto.
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
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
    eapply MON.
    + apply CMP. econstructor; eauto.
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. punfold REL.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. punfold REL.
Qed.

Hint Resolve eqitC_wcompat : paco.

Lemma eqit_idclo_compat b1 b2: compose (eqitC b1 b2) id <3= compose id (eqitC b1 b2).
Proof.
  intros. apply PR.
Qed.
Hint Resolve eqit_idclo_compat : paco.

Lemma eqitC_dist b1 b2:
  forall r1 r2, eqitC b1 b2 (r1 \2/ r2) <2= (eqitC b1 b2 r1 \2/ eqitC b1 b2 r2).
Proof.
  intros. destruct PR. destruct REL; eauto.
Qed.

Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC b1 b2) vclo <3= compose vclo (eqitC b1 b2)):
  eqit_trans_clo b1 b2 false false <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC b1 b2).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End eqit_closure.

Hint Unfold eqitC: core.
Hint Resolve eqitC_mon : paco.
Hint Resolve eqitC_wcompat : paco.
Hint Resolve eqit_idclo_compat : paco.
Hint Resolve eqitC_dist : paco.
Arguments eqit_clo_trans : clear implicits.
Hint Constructors eqit_trans_clo: core.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).

Global Instance Reflexive_eqitF b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqitF RR b1 b2 id sim).
Proof.
  red. destruct x; constructor; eauto.
Qed.

Global Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqitF RR b b id sim).
Proof.
  red. induction 3; constructor; subst; eauto.
  intros. apply H0. apply (REL v).
Qed.

Global Instance Reflexive_eqit_ b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqit_ RR b1 b2 id sim).
Proof. repeat red. intros. reflexivity. Qed.

Global Instance Symmetric_eqit_ b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqit_ RR b b id sim).
Proof. repeat red; symmetry; auto. Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen b1 b2 (r rg: itree E R -> itree E R -> Prop) :
  Reflexive RR -> Reflexive (gpaco2 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) r rg).
Proof.
  gcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto with paco.
Qed.

Global Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. ginit. apply Reflexive_eqit_gen; eauto.
Qed.

Global Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E _ _ RR b b).
Proof.
  red; intros. apply eqit_flip.
  eapply eqit_mon, H0; eauto.
Qed.

Global Instance eq_sub_euttge:
  subrelation (@eq_itree E _ _ RR) (euttge RR).
Proof.
  ginit. gcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; eauto 7 with paco.
Qed.

Global Instance euttge_sub_eutt:
  subrelation (@euttge E _ _ RR) (eutt RR).
Proof.
  ginit. gcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; pclearbot; eauto 7 with paco.
Qed.

Global Instance eq_sub_eutt:
  subrelation (@eq_itree E _ _ RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. apply H.
Qed.

End eqit_gen.

Hint Resolve Reflexive_eqit Reflexive_eqit_gen : reflexivity.

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (@eqit E R R eq).

Global Instance Reflexive_eqitF_eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq b1 b2 id sim).
Proof.
  apply Reflexive_eqitF; eauto.
Qed.

Global Instance Symmetric_eqitF_eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b id sim).
Proof.
  apply Symmetric_eqitF; eauto.
Qed.

Global Instance Reflexive_eqit__eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqit_ eq b1 b2 id sim).
Proof. apply Reflexive_eqit_; eauto. Qed.

Global Instance Symmetric_eqit__eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqit_ eq b b id sim).
Proof. apply Symmetric_eqit_; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen_eq b1 b2 (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gpaco2 (eqit_ eq b1 b2 id) (eqitC eq b1 b2) r rg).
Proof.
  apply Reflexive_eqit_gen; eauto.
Qed.

Global Instance Reflexive_eqit_eq b1 b2 : Reflexive (eqit b1 b2).
Proof.
  apply Reflexive_eqit; eauto.
Qed.

Global Instance Symmetric_eqit_eq b : Symmetric (eqit b b).
Proof.
  apply Symmetric_eqit; eauto.
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
  pstep. red. rewrite H. apply Reflexive_eqitF; eauto. left. apply reflexivity.
Qed.

(** ** Eta-expansion *)

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply observing_sub_eqit. econstructor. reflexivity. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eqit_eq.

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

Lemma eqit_inv_ret {E R1 R2 RR} b1 b2 r1 r2 :
  @eqit E R1 R2 RR b1 b2 (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma eqit_inv_vis {E R1 R2 RR} b1 b2 {u} (e1 e2: E u) (k1: u -> itree E R1) (k2: u -> itree E R2) :
  eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2) -> e1 = e2 /\ (forall u, eqit RR b1 b2 (k1 u) (k2 u)).
Proof.
  intros. punfold H. repeat red in H. simpl in H.
  dependent destruction H. pclearbot. eauto.
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

Lemma eqit_inv_tauLR {E R1 R2 RR} b1 b2 t1 t2 :
  @eqit E R1 R2 RR b1 b2 (Tau t1) (Tau t2) -> eqit RR b1 b2 t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. remember (TauF t2) as tt2.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt1. inv Heqtt2. pclearbot. eauto.
  - inv Heqtt1. inv H; eauto.
    + pclearbot. punfold REL. pstep. red. simpobs. eauto.
    + pstep. red. simpobs. econstructor; eauto. pstep_reverse. apply IHeqitF; eauto.
  - inv Heqtt2. inv H; eauto.
    + pclearbot. punfold REL. pstep. red. simpobs. eauto.
    + pstep. red. simpobs. econstructor; eauto. pstep_reverse. apply IHeqitF; eauto.
Qed.

Lemma eqit_inv_ret_vis: forall {E X R1 R2 RR} b1 b2 (r: R1) (e: E X) k,
    @eqit E R1 R2 RR b1 b2 (Ret r) (Vis e k) -> False.
Proof.
  intros.
  punfold H; inv H.
Qed.

Lemma eutt_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
Proof.
  intros; eapply eqit_inv_ret_vis; eauto.
Qed.

Lemma eqitree_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≅ Vis e k -> False.
Proof.
  intros; eapply eqit_inv_ret_vis; eauto.
Qed.

Lemma eqit_inv_tau_vis: forall {E X R1 R2 RR} b2 (e: E X) k t,
    @eqit E R1 R2 RR false b2 (Tau t) (Vis e k) -> False.
Proof.
  intros.
  punfold H; inv H.
  inv CHECK.
Qed.

Lemma eqit_inv_vis_tau: forall {E X R1 R2 RR} b1 (e: E X) k t,
    @eqit E R1 R2 RR b1 false (Vis e k) (Tau t) -> False.
Proof.
  intros.
  punfold H; inv H.
  inv CHECK.
Qed.

Lemma euttge_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Vis e k ≳ Tau a -> False.
Proof.
  intros; eapply eqit_inv_vis_tau; eauto.
Qed.

Lemma eqitree_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Tau a ≅ Vis e k -> False.
Proof.
  intros; eapply eqit_inv_tau_vis; eauto.
Qed.

Lemma eqit_inv_ret_tau: forall {E R1 R2 RR} b1 (r: R1) t,
    @eqit E R1 R2 RR b1 false (Ret r) (Tau t) -> False.
Proof.
  intros.
  punfold H; inv H.
  inv CHECK.
Qed.

Lemma eqit_inv_tau_ret: forall {E R1 R2 RR} b2 (r: R2) t,
    @eqit E R1 R2 RR false b2 (Tau t) (Ret r) -> False.
Proof.
  intros.
  punfold H; inv H.
  inv CHECK.
Qed.

Lemma euttge_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≳ Tau a -> False.
Proof.
  intros; eapply eqit_inv_ret_tau; eauto.
Qed.

Lemma eqitree_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≅ Tau a -> False.
Proof.
  intros; eapply eqit_inv_ret_tau; eauto.
Qed.

Lemma eutt_inv_ret {E R} r1 r2 :
  (Ret r1: itree E R) ≈ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_ret; eauto.
Qed.

Lemma eqitree_inv_ret {E R} r1 r2 :
  (Ret r1: itree E R) ≅ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_ret; eauto.
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

Lemma tau_euttge {E R} (t: itree E R) :
  Tau t ≳ t.
Proof.
  apply eqit_tauL. reflexivity.
Qed.

Lemma tau_eutt {E R} (t: itree E R) :
  Tau t ≈ t.
Proof.
  apply euttge_sub_eutt, tau_euttge.
Qed.

Lemma simpobs {E R} {ot} {t: itree E R} (EQ: ot = observe t): t ≅ go ot.
Proof.
  pstep. repeat red. simpobs. simpl. subst. pstep_reverse. apply Reflexive_eqit; eauto.
Qed.

(** *** Transitivity properties *)

Inductive rcompose {R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) (r1: R1) (r3: R3) : Prop :=
| rcompose_intro r2 (REL1: RR1 r1 r2) (REL2: RR2 r2 r3)
.
Hint Constructors rcompose: core.

Lemma trans_rcompose {R} RR (TRANS: Transitive RR):
  forall x y : R, rcompose RR RR x y -> RR x y.
Proof.
  intros. destruct H; eauto.
Qed.

Lemma eqit_trans {E R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) b1 b2 t1 t2 t3
      (INL: eqit RR1 b1 b2 t1 t2)
      (INR: eqit RR2 b1 b2 t2 t3):
  @eqit E _ _ (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  revert_until b2. pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2; eauto.
  - remember (RetF r2) as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with paco.
  - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply eqit_inv_tauLR. eauto.
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      pclearbot. punfold REL. red in REL.
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * remember (RetF r1) as ot.
        hinduction REL0 before CIH; intros; inv Heqot; eauto with paco.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; dependent destruction Heqot; eauto with paco.
        econstructor. intros. right.
        destruct (REL v), (REL0 v); try contradiction. eauto.
      * eapply IHREL0; eauto. pstep_reverse.
        destruct b1; inv CHECK0.
        apply eqit_inv_tauR. eauto.
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
    econstructor. intros.
    destruct (REL v), (REL0 v); try contradiction; eauto.
  - remember (TauF t0) as ot.
    hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
    eapply IHINL; eauto. pclearbot. punfold REL.
Qed.

Global Instance Transitive_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. eapply eqit_mon, eqit_trans; eauto using (trans_rcompose RR).
Qed.

Global Instance Transitive_eqit_eq {E : Type -> Type} {R: Type} (b1 b2: bool):
  Transitive (@eqit E R R eq b1 b2).
Proof.
  apply Transitive_eqit. repeat intro; subst; eauto.
Qed.

Global Instance Equivalence_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b: bool):
  Equivalence RR -> Equivalence (@eqit E R R RR b b).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance Equivalence_eqit_eq {E : Type -> Type} {R: Type} (b: bool):
  Equivalence (@eqit E R R eq false false).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance Transitive_eutt {E R RR} : Transitive RR -> Transitive (@eutt E R R RR).
Proof.
  red; intros. eapply eqit_mon, eqit_trans; eauto using (trans_rcompose RR).
Qed.

Global Instance Equivalence_eutt {E R RR} : Equivalence RR -> Equivalence (@eutt E R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance geuttgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2 r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. econstructor; cycle -3; eauto.
  - eapply eqit_mon, H; eauto; discriminate.
  - eapply eqit_mon, H0; eauto; discriminate.
Qed.

Global Instance geuttgen_cong_eqit_eq {E R1 R2 RS} b1 b2 r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  eapply geuttgen_cong_eqit; intros; subst; eauto.
Qed.

Global Instance geuttge_cong_euttge {E R1 R2 RR1 RR2 RS} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true false id) (eqitC RS true false) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans.
Qed.

Global Instance geuttge_cong_euttge_eq {E R1 R2 RS} r rg:
  Proper (euttge eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true false id) (eqitC RS true false) r rg).
Proof.
  eapply geuttge_cong_euttge; intros; subst; eauto.
Qed.

Global Instance geutt_cong_euttge {E R1 R2 RR1 RR2 RS} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans.
Qed.

Global Instance geutt_cong_euttge_eq {E R1 R2 RS} r rg:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  eapply geutt_cong_euttge; intros; subst; eauto.
Qed.

Global Instance eqitgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  ginit. intros. eapply geuttgen_cong_eqit; eauto. gfinal. eauto.
Qed.

Global Instance eqitgen_cong_eqit_eq {E R1 R2 RS} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  ginit. intros. rewrite H1, H0. gfinal. eauto.
Qed.

Global Instance euttge_cong_euttge {E R RS}
       (TRANS: Transitive RS):
  Proper (euttge RS ==> flip (euttge RS) ==> flip impl)
         (@eqit E R R RS true false).
Proof.
  repeat intro. do 2 (eapply eqit_mon, eqit_trans; eauto using (trans_rcompose RS)).
Qed.

Global Instance euttge_cong_euttge_eq {E R}:
  Proper (euttge eq ==> flip (euttge eq) ==> flip impl)
         (@eqit E R R eq true false).
Proof.
  eapply euttge_cong_euttge; eauto using eq_trans.
Qed.

(** ** Equations for core combinators *)

(* TODO (LATER): I keep these [...bind_] lemmas around temporarily
   in case I run some issues with slow typeclass resolution. *)

Lemma unfold_bind {E R S}
           (t : itree E R) (k : R -> itree E S) :
  ITree.bind t k ≅ ITree._bind k (fun t => ITree.bind t k) (observe t).
Proof. rewrite unfold_bind_. reflexivity. Qed.

Lemma bind_ret_l {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. rewrite bind_ret_. reflexivity. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. rewrite bind_tau_. reflexivity. Qed.

Lemma bind_vis {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. rewrite bind_vis_. reflexivity. Qed.

Lemma bind_trigger {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k ≅ Vis e (fun x => k x).
Proof.
  rewrite unfold_bind; cbn.
  pstep.
  constructor.
  intros; red. left. rewrite bind_ret_l.
  apply Reflexive_eqit; eauto.
Qed.

Lemma unfold_iter {E A B} (f : A -> itree E (A + B)) (x : A) :
  (ITree.iter f x) ≅ (f x >>= fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite unfold_aloop_. reflexivity.
Qed.

Lemma unfold_forever {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ (t >>= fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (_ >>= _)).
  reflexivity.
Qed.

Ltac auto_ctrans :=
  intros; repeat (match goal with [H: rcompose _ _ _ _ |- _] => destruct H end); subst; eauto.
Ltac auto_ctrans_eq := try instantiate (1:=eq); auto_ctrans.

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
  - pstep. econstructor. left. apply H.
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
Hint Constructors eqit_bind_clo: core.

Lemma eqit_clo_bind b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo):
  eqit_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
Proof.
  gcofix CIH. intros. destruct PR.
  guclo eqit_clo_trans.
  econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
  punfold EQV. unfold_eqit.
  hinduction EQV before CIH; intros; pclearbot.
  - guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
    eauto with paco.
  - gstep. econstructor. eauto with paco.
  - gstep. econstructor. eauto 7 with paco.
  - destruct b1; try discriminate.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
  - destruct b2; try discriminate.
    guclo eqit_clo_trans. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
Qed.

Lemma eutt_clo_bind {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  intros. ginit. guclo eqit_clo_bind.
  econstructor; eauto. intros; subst. gfinal. right. apply EQK. eauto.
Qed.

End eqit_h.

Lemma eutt_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≈ Tau t2 <-> t1 ≈ t2.
Proof.
  apply eqit_Tau.
Qed.

Lemma eqitree_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≅ Tau t2 <-> t1 ≅ t2.
Proof.
  apply eqit_Tau.
Qed.

Arguments eqit_clo_bind : clear implicits.
Hint Constructors eqit_bind_clo: core.

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

Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eq_itree E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)):
  eq_itree RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  eapply eqit_bind'; eauto.
Qed.

Global Instance eqit_bind {E R S} b1 b2 :
  Proper (pointwise_relation _ (eqit eq b1 b2) ==>
          eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

Global Instance eqit_bind_ {E R S} b1 b2 k :
  Proper (going (eqit eq b1 b2) ==>
          eqit eq b1 b2) (@ITree._bind E R S k (@ITree.bind' E R S k)).
Proof.
  ginit. intros. destruct H0.
  rewrite (itree_eta' x), (itree_eta' y), <- !unfold_bind.
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

Global Instance eqit_eq_map {E R S} b1 b2 :
  Proper (pointwise_relation _ eq ==>
          eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_bind. gstep. repeat red.
  genobs s os. destruct os; simpl; eauto with paco.
Qed.

Lemma bind_ret_r' {E R} (u : itree E R) (f : R -> R) :
  (forall x, f x = x) ->
  (r <- u ;; Ret (f r)) ≅ u.
Proof.
  intro H. rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_Ret. auto.
  - reflexivity.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  ginit. gcofix CIH. intros. rewrite !unfold_bind.
  gstep. repeat red. destruct (observe s); simpl; eauto with paco.
  apply reflexivity.
Qed.

Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros.
  rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
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
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma map_tau {E A B} (f : A -> B) (t : itree E A) :
    @ITree.map E _ _ f (Tau t) ≅ Tau (ITree.map f t).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_tau; reflexivity.
Qed.

Hint Rewrite @bind_ret_l : itree.
Hint Rewrite @bind_ret_r : itree.
Hint Rewrite @bind_tau : itree.
Hint Rewrite @bind_vis : itree.
Hint Rewrite @bind_map : itree.
Hint Rewrite @map_ret : itree.
Hint Rewrite @map_tau : itree.
Hint Rewrite @bind_bind : itree.

(** ** Tactics *)

Ltac force_left :=
  match goal with
  | [ |- _ ?x _ ] => rewrite (itree_eta x); cbn
  end.

Ltac force_right :=
  match goal with
  | [ |- _ _ ?x ] => rewrite (itree_eta x); cbn
  end.

(** Remove all taus from the left hand side of the goal equation
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps_left :=
  repeat (force_left; rewrite tau_eutt); force_left.

(** Remove all taus from the right hand side of the goal equation. *)
Ltac tau_steps_right :=
  repeat (force_right; rewrite tau_eutt); force_right.

(** Remove all taus from both sides of the goal equation. *)
Ltac tau_steps :=
  tau_steps_left;
  tau_steps_right.

Lemma eqit_inv_bind_ret:
  forall {E X R1 R2 RR} b1 b2
    (ma : itree E X) (kb : X -> itree E R1) (b: R2),
    @eqit E R1 R2 RR b1 b2 (ITree.bind ma kb) (Ret b) ->
    exists a, @eqit E X X eq b1 b2 ma (Ret a) /\
         @eqit E R1 R2 RR b1 b2 (kb a) (Ret b).
Proof.
  intros.
  punfold H.
  unfold eqit_ in *.
  cbn in *.
  remember (ITree.bind ma kb) as tl.
  assert (tl ≅ ITree.bind ma kb) by (subst; reflexivity).
  clear Heqtl.
  genobs tl tl'.
  remember (RetF b) as tr.
  revert ma kb tl Heqtl' H0 b Heqtr.
  induction H.
  - intros; subst.
    inv Heqtr.
    destruct (observe tl) eqn: Hobtl; inv Heqtl'.
    rewrite unfold_bind in H0.
    destruct (observe ma) eqn: Hobma.
    * exists r0. split. rewrite <- Hobma. tau_steps. reflexivity.
      cbn in *. rewrite <- H0. rewrite itree_eta, Hobtl.
      apply eqit_Ret; auto.
    * cbn in H0. rewrite itree_eta in H0. rewrite Hobtl in H0.
      apply eqitree_inv_ret_tau in H0. contradiction.
    * cbn in H0. rewrite itree_eta, Hobtl in H0.
      apply eqitree_inv_ret_vis in H0. contradiction.
  - intros. inversion Heqtr.
  - intros. inversion Heqtr.
  - intros. subst.
    apply simpobs in Heqtl'. rewrite Heqtl' in H0; clear tl Heqtl'.
    rewrite unfold_bind in H0.
    destruct (observe ma) eqn: Hobma.
    + cbn in *.
      specialize (IHeqitF ma (fun _ => t1) t1 eq_refl).
      edestruct IHeqitF as (a & ? & ?);[| reflexivity |].
      * setoid_rewrite itree_eta at 4.
        rewrite Hobma, bind_ret_l.
        reflexivity.
      * exists a; split; auto.
        rewrite itree_eta, Hobma in H1.
        apply eqit_inv_ret in H1; subst.
        rewrite <- H0.
        destruct b1; [| inv CHECK].
        apply eqit_tauL; auto.
    + cbn in *. rewrite eqitree_Tau in H0.
      edestruct IHeqitF as (a & ? & ?);[reflexivity | apply H0 | reflexivity |].
      exists a; split; [| assumption].
      destruct b1; [| inv CHECK].
      rewrite itree_eta, Hobma; apply eqit_tauL; auto.
    + exfalso. cbn in H0; apply eqitree_inv_tau_vis in H0; contradiction.
  - intros. inversion Heqtr.
Qed.

Lemma eutt_inv_bind_ret:
  forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
    ITree.bind ma kb ≈ Ret b ->
    exists a, ma ≈ Ret a /\ kb a ≈ Ret b.
Proof.
  intros; apply eqit_inv_bind_ret; auto.
Qed.

Lemma eqitree_inv_bind_ret:
  forall {E A B} (ma : itree E A) (kb : A -> itree E B) b,
    ITree.bind ma kb ≅ Ret b ->
    exists a, ma ≅ Ret a /\ kb a ≅ Ret b.
Proof.
  intros; apply eqit_inv_bind_ret; auto.
Qed.

Lemma eqit_inv_bind_vis :
  forall {A B C E X RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxc : X -> itree E C),
    eqit RR b1 b2 (ITree.bind ma kab) (Vis e kxc) ->
    (exists (kxa : X -> itree E A), (eqit eq b1 b2 ma (Vis e kxa)) /\
                              forall (x:X), eqit RR b1 b2 (ITree.bind (kxa x) kab) (kxc x)) \/
    (exists (a : A), eqit eq b1 b2 ma (Ret a) /\ eqit RR b1 b2 (kab a) (Vis e kxc)).
Proof.
  intros. punfold H. unfold eqit_ in H. cbn in *.
  remember (ITree.bind ma kab) as tl.
  assert (tl ≅ (ITree.bind ma kab)) by (subst; reflexivity).
  clear Heqtl.
  genobs tl tl'.
  remember (VisF e kxc) as tr.
  revert ma kab tl Heqtl' H0 kxc Heqtr.
  induction H.
  - intros. inv Heqtr.
  - intros. inv Heqtr.
  - intros. rewrite unfold_bind in H0.
    destruct (observe ma) eqn: Hobma; cbn in *; rewrite itree_eta in H0; rewrite <- Heqtl' in H0.
    + right. exists r. split. rewrite itree_eta. rewrite Hobma. reflexivity.
      rewrite <- H0. apply eqit_Vis.
      intros. destruct (REL u0); auto. inv H.
    + symmetry in H0. apply eqitree_inv_tau_vis in H0. contradiction.
    + setoid_rewrite itree_eta at 1. rewrite Hobma. clear Hobma Heqtl'.
      inv Heqtr; auto_inj_pair2; subst.
      apply eq_itree_inv_vis in H0.
      destruct H0 as (? & ? & ?).
      inv H; auto_inj_pair2; subst.
      left. exists k. split; [reflexivity |].
      intros. rewrite <- H0. destruct (REL x0); auto. inv H.
  - intros. inv Heqtr.
    apply simpobs in Heqtl'. rewrite Heqtl' in H0; clear tl Heqtl'.
    destruct b1; try inv CHECK.
    rewrite unfold_bind in H0.
    destruct (observe ma) eqn: Hobma.
    + cbn in *.
      specialize (IHeqitF ma (fun _ => t1) t1 eq_refl).
      edestruct IHeqitF as [a | a]; [| reflexivity | | ].
      * setoid_rewrite itree_eta at 4.
        rewrite Hobma, bind_ret_l.
        reflexivity.
      * left.
        destruct a as (kca & HMA & HEQ).
        exfalso. eapply eqit_inv_ret_vis. eapply eqit_trans; [| apply HMA].
        apply eqit_flip. rewrite itree_eta. rewrite Hobma. reflexivity.
      * right. destruct a.
        destruct H1 as [H1 H2].
        rewrite itree_eta, Hobma in H1.
        apply eqit_inv_ret in H1; subst.
        setoid_rewrite itree_eta at 1.
        rewrite Hobma.
        exists x. split; try reflexivity. rewrite <- H0.
        pstep. unfold eqit_. constructor 4; auto.
    + cbn in *. rewrite eqitree_Tau in H0.
      edestruct IHeqitF as [a | a]; [reflexivity | apply H0 | reflexivity | |].
      * left. setoid_rewrite itree_eta at 1.
        rewrite Hobma.
        destruct a as (? & ? & ?). exists x; split; auto.
        punfold H1. pstep. unfold eqit_ in *. constructor 4; auto.
      * right. setoid_rewrite itree_eta at 1.
        rewrite Hobma.
        destruct a as (? & ? & ?). exists x; split; auto.
        punfold H1. pstep. unfold eqit_ in *. constructor 4; auto.
    + exfalso. cbn in H0; apply eqitree_inv_tau_vis in H0; contradiction.
  - intros. inv Heqtr.
Qed.

Lemma eutt_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≈ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≈ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≈ (kxb x)) \/
    (exists (a : A), (ma ≈ Ret a) /\ (kab a ≈ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.

Lemma eqitree_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≅ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≅ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≅ (kxb x)) \/
    (exists (a : A), (ma ≅ Ret a) /\ (kab a ≅ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.

Lemma eqit_inv_bind_tau:
  forall {E A B C RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (tc: itree E C),
    eqit RR b1 b2 (ITree.bind ma kab) (Tau tc) ->
    (exists (ma' : itree E A), eqit eq b1 b2 ma (Tau ma') /\ eqit RR b1 b2 (ITree.bind ma' kab) tc) \/
    (exists (a : A), eqit eq b1 b2 ma (Ret a) /\ eqit RR b1 b2 (kab a) (Tau tc)).
Proof.
  intros. punfold H. unfold eqit_ in H.
  remember (ITree.bind ma kab) as tl.
  assert (tl ≅ (ITree.bind ma kab)) by (subst; reflexivity).
  clear Heqtl.
  remember (Tau tc) as tr.
  genobs tl tl'. genobs tr tr'.
  revert ma kab tl Heqtl' tr Heqtr' H0 Heqtr.
  induction H.
  - intros. subst. inv Heqtr'.
  - intros. subst. inv Heqtr'.
    rewrite unfold_bind in H0.
    rewrite itree_eta in H0. rewrite <- Heqtl' in H0.
    destruct (observe ma) eqn:Hobma.
    + cbn in *.
      right. exists r. rewrite itree_eta. rewrite Hobma. split; [reflexivity |].
      rewrite <- H0. apply eqit_Tau. pclearbot. auto.
    + cbn in *.
      left. exists t. rewrite itree_eta. rewrite Hobma. split; [reflexivity |].
      rewrite eqitree_Tau in H0. rewrite <- H0. pclearbot. auto.
    + cbn in *.
      apply eqitree_inv_tau_vis in H0. contradiction.
  - intros. subst. inv Heqtr'.
  - intros. subst. rewrite itree_eta in H0. rewrite <- Heqtl' in H0.
    rewrite unfold_bind in H0.
    inv CHECK.
    destruct (observe ma) eqn:Hobma.
    + cbn in *.
      right. exists r. rewrite itree_eta. rewrite Hobma. split; [reflexivity |].
      rewrite <- H0. apply eqit_tauL. auto.
    + cbn in *.
      rewrite eqitree_Tau in H0.
      edestruct IHeqitF; eauto; auto.
      * left. destruct H1 as (t' & ? & ?).
        exists t'. rewrite itree_eta. rewrite Hobma. split; auto.
        apply eqit_tauL. auto.
      * left. destruct H1 as (a & ? & ?).
        exists (Ret a). rewrite itree_eta. rewrite Hobma. rewrite H1.
        split; [reflexivity |]. rewrite unfold_bind. cbn.
        apply eqit_tauL in H2. rewrite <- eqit_Tau. auto.
    + cbn in *. apply eqitree_inv_tau_vis in H0; contradiction.
  - intros. subst. inv Heqtr'.
    rewrite unfold_bind in H0.
    inv CHECK.
    destruct (observe ma) eqn:Hobma.
    + cbn in *.
      right. exists r. rewrite itree_eta. rewrite Hobma. split; [reflexivity |].
      rewrite <- H0. apply eqit_tauR. auto.
    + cbn in *.
      left. exists (Tau t). rewrite itree_eta. rewrite Hobma.
      split; [apply eqit_tauR; reflexivity |].
      rewrite unfold_bind. simpl. rewrite <- H0. auto.
    + cbn in *. left. exists (Vis e k). rewrite itree_eta. rewrite Hobma.
      split; [apply eqit_tauR; reflexivity |].
      rewrite bind_vis. rewrite <- H0. auto.
Qed.

Lemma eutt_inv_bind_tau:
  forall {E A B} (ma : itree E A) (kab : A -> itree E B) (t: itree E B),
    ITree.bind ma kab ≈ Tau t ->
    (exists (ma' : itree E A), ma ≈ Tau ma' /\ ITree.bind ma' kab ≈ t) \/
    (exists (a : A), ma ≈ Ret a /\ kab a ≈ Tau t).
Proof.
  intros. apply eqit_inv_bind_tau. auto.
Qed.

Lemma eqitree_inv_bind_tau:
  forall {E A B} (ma : itree E A) (kab : A -> itree E B) (t: itree E B),
    ITree.bind ma kab ≅ Tau t ->
    (exists (ma' : itree E A), ma ≅ Tau ma' /\ ITree.bind ma' kab ≅ t) \/
    (exists (a : A), ma ≅ Ret a /\ kab a ≅ Tau t).
Proof.
  intros. apply eqit_inv_bind_tau. auto.
Qed.

Lemma eutt_Ret_spin_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} (v: R1),
    eutt RR (Ret v) (@ITree.spin E R2) -> False.
Proof.
  intros.
  punfold H.
  unfold eqit_ in H.
  remember (observe (Ret v)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_spin_Ret_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} (v: R2),
    eutt RR (@ITree.spin E R1) (Ret v) -> False.
Proof.
  intros.
  punfold H.
  unfold eqit_ in H.
  remember (observe (Ret v)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_Vis_spin_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} {X} (e: E X) (k: X -> itree E R1),
    eutt RR (Vis e k) (@ITree.spin E R2) -> False.
Proof.
  intros.
  punfold H.
  unfold eqit_ in H.
  remember (observe (Vis e k)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

Lemma eutt_spin_Vis_abs: forall {E R1 R2} {RR: R1 -> R2 -> Prop} {X} (e: E X) (k: X -> itree E R2),
    eutt RR (@ITree.spin E R1) (Vis e k) -> False.
Proof.
  intros.
  punfold H.
  unfold eqit_ in H.
  remember (observe (Vis e k)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.

