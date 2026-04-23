(** * Relation up to tau *)

(** [rutt] ("relation up to tau") is a generalization of [eutt] that may relate trees
  indexed by different event type families [E]. *)

(** It corresponds roughly to the interpretation of "types as relations" from the relational
  parametricity model by Reynolds (Types, Abstraction and Parametric Polymorphism).
  Any polymorphic function [f : forall E R, itree E R -> ...] should respect this relation,
  in the sense that for any relations [rE], [rR], the implication
  [rutt rE rR t t' -> (f t ~~ f t')] should hold, where [~~] is some canonical relation on the
  codomain of [f].

  If we could actually quotient itrees "up to taus", and Coq could generate
  parametricity ("free") theorems on demand, the above might be a free theorem. *)

(** [rutt] is used to define the [trace_refine] relation in [ITree.ITrace.ITraceDefinition]. *)

From Stdlib Require Import
     Morphisms
     Program.

From Coinduction Require Import all.

From ITree Require Import
     Basics.Utils
     Axioms
     Core.ITreeDefinition
     Eq.Eqit
     Eq.Shallow.

Local Open Scope itree_scope.

Section RuttF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  (* From the point of view of relational parametricity, it would be more fitting
  to replace [(REv, RAns)] with one [REv : forall A1 A2, (A1 -> A2 -> Prop) -> (E1 A1 -> E2 A2 -> Prop)].
  Contributions to that effect are welcome. *)
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive ruttF (RR: R1 -> R2 -> Prop) (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttF RR sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttF RR sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttF RR sim (VisF e1 k1) (VisF e2 k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttF RR sim (observe t1) ot2 ->
      ruttF RR sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttF RR sim ot1 (observe t2) ->
      ruttF RR sim ot1 (TauF t2).
  Hint Constructors ruttF : itree.

  Definition rutt_ (sim : (R1 -> R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop) :
    (R1 -> R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop :=
    fun RR t1 t2 =>
      ruttF RR (sim RR) (observe t1) (observe t2).

  Lemma rutt_mono : Proper (leq ==> leq) rutt_.
  Proof.
    repeat intro. unfold rutt_ in *. induction H0; eauto with itree.
    constructor; now apply H. 
    constructor; intros; eauto; now apply H, H1. 
  Qed.

  Definition rutt_mon : mon ((R1 -> R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop) :=
    {| body := rutt_ ; Hbody := rutt_mono |}. 

  Definition rutt : (R1 -> R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop := gfp rutt_mon.
  Hint Unfold rutt : itree.

  Lemma ruttF_inv_VisF_r {sim} RR t1 U2 (e2: E2 U2) (k2: U2 -> _):
    ruttF RR sim t1 (VisF e2 k2) ->
    (exists U1 (e1: E1 U1) k1, t1 = VisF e1 k1 /\
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
    \/
    (exists t1', t1 = TauF t1' /\
      ruttF RR sim (observe t1') (VisF e2 k2)).
  Proof.
    refine (fun H =>
      match H in ruttF _ _ _ t2 return
        match t2 return Prop with
        | VisF e2 k2 => _
        | _ => True
        end
      with
      | EqVis _ _ _ _ _ _ _ _ _ _ => _
      | _ => _
      end); try exact I.
    - left; eauto.
    - destruct i0; eauto.
  Qed.

  Lemma ruttF_inv_VisF {sim}
      RR U1 U2 (e1 : E1 U1) (e2 : E2 U2) (k1 : U1 -> _) (k2 : U2 -> _)
    : ruttF RR sim (VisF e1 k1) (VisF e2 k2) ->
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2).
  Proof.
    intros H. dependent destruction H. assumption.
  Qed.

End RuttF.

(** ** Rutt-specific tactics *)

#[local] Ltac runfold    := unfold rutt.
#[local] Ltac runfold_in h := unfold rutt in h.

Ltac rcbn := cbn[rutt_mon body]; try unfold rutt_.
Ltac rcbn_in H := cbn[rutt_mon body] in H; try unfold rutt_ in H.

Tactic Notation "rcbn" "in" ident(h) := rcbn_in h.
Tactic Notation "rcbn" "in" "*" := cbn[rutt_mon body] in *; try unfold rutt_ in *.

(** [rstep] unfolds [rutt] one step, exposing the [ruttF] functor. *)
Tactic Notation "rstep" := runfold; step; rcbn.
Tactic Notation "rstep" "in" ident(h) := runfold_in h; step in h; rcbn in h.

#[local] Ltac refold :=
  repeat match goal with
  | |- context[gfp (@rutt_mon ?E1 ?E2 ?R1 ?R2 ?RE ?RA)] =>
      fold (@rutt E1 E2 R1 R2 RE RA)
  end.

Ltac fold_rutt :=
  match goal with
  | |- context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR) with (body (@rutt_mon E1 E2 R1 R2 REv RAns RR))
  end.
Ltac fold_rutt_in h :=
  match type of h with
  | context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR) with (body (@rutt_mon E1 E2 R1 R2 REv RAns RR)) in h
  end.
Tactic Notation "runstep" := fold_rutt; unstep.
Tactic Notation "runstep" "in" ident(h) := fold_rutt_in h; unstep in h.

Ltac to_rmon_core :=
match goal with
| |- context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR (?f ?RR) (observe ?t1) (observe ?t2)] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR (f RR) (observe t1) (observe t2))
      with (@rutt_mon E1 E2 R1 R2 REv RAns f RR t1 t2)
| |- context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR (?f ?RR) (?con1 ?a1) (?con2 ?a2)] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR (f RR) (con1 a1) (con2 a2))
      with (@rutt_mon E1 E2 R1 R2 REv RAns f RR (go (con1 a1)) (go (con2 a2)))
end.

Ltac to_rmon :=
let dummy := fresh "dummy" in
assert (dummy : True) by constructor;
          intros;
          to_rmon_core;
          revert_until dummy;
          clear dummy.

Ltac to_rmon_in h :=
match type of h with
| context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR (?f ?RR) (observe ?t1) (observe ?t2)] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR (f RR) (observe t1) (observe t2))
      with (@rutt_mon E1 E2 R1 R2 REv RAns f RR t1 t2) in h
| context[@ruttF ?E1 ?E2 ?R1 ?R2 ?REv ?RAns ?RR (?f ?RR) (?con1 ?a1) (?con2 ?a2)] =>
      change (@ruttF E1 E2 R1 R2 REv RAns RR (f RR) (con1 a1) (con2 a2))
      with (@rutt_mon E1 E2 R1 R2 REv RAns f RR (go (con1 a1)) (go (con2 a2))) in h
end.

Tactic Notation "to_rmon" "in" ident(h) := to_rmon_in h.

#[local] Ltac runfold_coind := unfold_coind_with runfold.
Tactic Notation "rcoinduction" simple_intropattern(R) simple_intropattern(H) :=
  runfold_coind; coinduction R H; rcbn; refold.


#[global] Hint Constructors ruttF : itree.
#[global] Hint Unfold rutt_ : itree.
#[global] Hint Unfold rutt_mon : itree.
#[global] Hint Unfold rutt : itree.

Section ConstructionInversion.
Variables (E1 E2: Type -> Type).
Variables (R1 R2: Type).
Variable (REv: forall T1 T2, E1 T1 -> E2 T2 -> Prop).
Variable (RAns: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).
Variable (RR: R1 -> R2 -> Prop).

Lemma rutt_Ret r1 r2:
  RR r1 r2 ->
  @rutt E1 E2 R1 R2 REv RAns RR (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. rstep. constructor; auto. Qed.

Lemma rutt_inv_Ret r1 r2:
  rutt REv RAns RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. rstep in H. inv H.
Qed.

Lemma rutt_inv_Ret_l r1 t2:
  rutt REv RAns RR (Ret r1) t2 -> exists r2, t2 ≳ Ret r2 /\ RR r1 r2.
Proof.
  intros Hrutt. rstep in Hrutt. rcbn in Hrutt. 
  setoid_rewrite (itree_eta t2). remember (observe (Ret r1)) as ot1; revert Heqot1.  
  induction Hrutt; intros; try discriminate.
  - inversion Heqot1; subst. exists r2. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot1) as [r2 [H1 H2]]. exists r2; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Ret_r t1 r2:
  rutt REv RAns RR t1 (Ret r2) -> exists r1, t1 ≳ Ret r1 /\ RR r1 r2.
Proof.
  intros Hrutt. rstep in Hrutt. rcbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (observe (Ret r2)) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot2) as [r1 [H1 H2]]. exists r1; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

(** Helper: inversion of [ruttF] at [TauF] on the left. *)
Lemma ruttF_inv_tau_l t1 ot2 :
  ruttF REv RAns RR (rutt REv RAns RR) (TauF t1) ot2 ->
  ruttF REv RAns RR (rutt REv RAns RR) (observe t1) ot2.
Proof.
  intros H. remember (TauF t1) as tt1.
  induction H; try discriminate.
  - inv Heqtt1. constructor. rstep in H. exact H.
  - inv Heqtt1.
  - constructor. auto.
Qed.

(** Helper: inversion of [ruttF] at [TauF] on the right. *)
Lemma ruttF_inv_tau_r ot1 t2 :
  ruttF REv RAns RR (rutt REv RAns RR) ot1 (TauF t2) ->
  ruttF REv RAns RR (rutt REv RAns RR) ot1 (observe t2).
Proof.
  intros H. remember (TauF t2) as tt2.
  induction H; try discriminate.
  - inv Heqtt2. constructor. rstep in H. exact H.
  - constructor. auto.
  - inv Heqtt2.
Qed.

Lemma rutt_inv_Tau_l t1 t2 :
  rutt REv RAns RR (Tau t1) t2 -> rutt REv RAns RR t1 t2.
Proof.
  intros. rstep in H. rstep.
  apply ruttF_inv_tau_l. exact H.
Qed.

Lemma rutt_add_Tau_l t1 t2 :
  rutt REv RAns RR t1 t2 -> rutt REv RAns RR (Tau t1) t2.
Proof.
  intros. rstep. constructor. rstep in H. exact H.
Qed.

Lemma rutt_inv_Tau_r t1 t2 :
  rutt REv RAns RR t1 (Tau t2) -> rutt REv RAns RR t1 t2.
Proof.
  intros. rstep in H. rstep.
  apply ruttF_inv_tau_r. exact H.
Qed.

Lemma rutt_add_Tau_r t1 t2 :
  rutt REv RAns RR t1 t2 -> rutt REv RAns RR t1 (Tau t2).
Proof.
  intros. rstep. constructor. rstep in H. exact H.
Qed.

Lemma rutt_inv_Tau t1 t2 :
  rutt REv RAns RR (Tau t1) (Tau t2) -> rutt REv RAns RR t1 t2.
Proof.
  intros; apply rutt_inv_Tau_r, rutt_inv_Tau_l; assumption.
Qed.

Lemma rutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
    (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 -> rutt REv RAns RR (k1 t1) (k2 t2)) ->
  rutt REv RAns RR (Vis e1 k1) (Vis e2 k2).
Proof.
  intros He Hk. rstep. constructor; auto.
Qed.

Lemma rutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  rutt REv RAns RR (Vis e1 k1) t2 ->
  exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> rutt REv RAns RR (k1 v1) (k2 v2)).
Proof.
  intros Hrutt. rstep in Hrutt. rcbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (observe (Vis e1 k1)) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename B into U2.
    exists U2, e2, k2; split. reflexivity. split; auto.
  - destruct (IHHrutt eq_refl) as (U2 & e2 & k2 & Ht0 & HAns).
    rewrite <- itree_eta in Ht0.
    exists U2, e2, k2; split; auto. now rewrite tau_eutt.
Qed.

Lemma rutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  rutt REv RAns RR t1 (Vis e2 k2) ->
  exists U1 (e1: E1 U1) k1,
    t1 ≈ Vis e1 k1 /\
    REv U1 U2 e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> rutt REv RAns RR (k1 v1) (k2 v2)).
Proof.
  intros Hrutt. rstep in Hrutt. rcbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (observe (Vis e2 k2)) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename A into U1.
    exists U1, e1, k1; split. reflexivity. split; auto.
  - destruct (IHHrutt eq_refl) as (U1 & e1 & k1 & Ht0 & HAns).
    rewrite <- itree_eta in Ht0.
    exists U1, e1, k1; split; auto. now rewrite tau_eutt.
Qed.

Lemma rutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  rutt REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
  forall u1 u2, RAns U1 U2 e1 u1 e2 u2 -> rutt REv RAns RR (k1 u1) (k2 u2).
Proof.
  intros H u1 u2 Hans. rstep in H.
  exact (ruttF_inv_VisF _ _ _ _ _ _ _ _ _ H u1 u2 Hans).
Qed.

End ConstructionInversion.