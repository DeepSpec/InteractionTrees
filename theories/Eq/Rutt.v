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

From Coq Require Import
     Morphisms
.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     Eq
     Basics
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section RuttF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  (* From the point of view of relational parametricity, it would be more fitting
  to replace [(REv, RAns)] with one [REv : forall A1 A2, (A1 -> A2 -> Prop) -> (E1 A1 -> E2 A2 -> Prop)].
  Contributions to that effect are welcome. *)
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
  Context (RR : R1 -> R2 -> Prop).
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive ruttF (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttF sim (VisF e1 k1) (VisF e2 k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttF sim (observe t1) ot2 ->
      ruttF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttF sim ot1 (observe t2) ->
      ruttF sim ot1 (TauF t2).
  Hint Constructors ruttF : itree.

  Definition rutt_ (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    ruttF sim (observe t1) (observe t2).
  Hint Unfold rutt_ : itree.

  Lemma rutt_monot : monotone2 rutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition rutt : itree E1 R1 -> itree E2 R2 -> Prop := paco2 rutt_ bot2.
  Hint Unfold rutt : itree.

  Lemma ruttF_inv_VisF_r {sim} t1 U2 (e2: E2 U2) (k2: U2 -> _):
    ruttF sim t1 (VisF e2 k2) ->
    (exists U1 (e1: E1 U1) k1, t1 = VisF e1 k1 /\
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
    \/
    (exists t1', t1 = TauF t1' /\
      ruttF sim (observe t1') (VisF e2 k2)).
  Proof.
    refine (fun H =>
      match H in ruttF _ _ t2 return
        match t2 return Prop with
        | VisF e2 k2 => _
        | _ => True
        end
      with
      | EqVis _ _ _ _ _ _ _ _ _ => _
      | _ => _
      end); try exact I.
    - left; eauto.
    - destruct i0; eauto.
  Qed.

  Lemma ruttF_inv_VisF {sim}
      U1 U2 (e1 : E1 U1) (e2 : E2 U2) (k1 : U1 -> _) (k2 : U2 -> _)
    : ruttF sim (VisF e1 k1) (VisF e2 k2) ->
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2).
  Proof.
    intros H. dependent destruction H. assumption.
  Qed.


  Ltac unfold_rutt :=
    (try match goal with [|- rutt_ _ _ _ _ _ _ _ ] => red end);
    (repeat match goal with [H: rutt_ _ _ _ _ _ _ _ |- _ ] => red in H end).

  Lemma fold_ruttF:
    forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
    ruttF (upaco2 rutt_ bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    rutt t1 t2.
  Proof.
    intros * eq -> ->; pfold; auto.
  Qed.
End RuttF.

Tactic Notation "fold_ruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | ruttF ?_REV ?_RANS ?_RR (upaco2 (rutt_ ?_REV ?_RANS ?_RR) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_ruttF in H; [| eauto | eauto]
  end.

#[global] Hint Resolve rutt_monot : paco.

Section ConstructionInversion.
Variables (E1 E2: Type -> Type).
Variables (R1 R2: Type).
Variable (REv: forall T1 T2, E1 T1 -> E2 T2 -> Prop).
Variable (RAns: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).
Variable (RR: R1 -> R2 -> Prop).

Lemma rutt_Ret r1 r2:
  RR r1 r2 ->
  @rutt E1 E2 R1 R2 REv RAns RR (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. pstep; constructor; auto. Qed.

Lemma rutt_inv_Ret r1 r2:
  rutt REv RAns RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma rutt_inv_Ret_l r1 t2:
  rutt REv RAns RR (Ret r1) t2 -> exists r2, t2 ≳ Ret r2 /\ RR r1 r2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot1; subst. exists r2. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot1) as [r2 [H1 H2]]. exists r2; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Ret_r t1 r2:
  rutt REv RAns RR t1 (Ret r2) -> exists r1, t1 ≳ Ret r1 /\ RR r1 r2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot2) as [r1 [H1 H2]]. exists r1; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Tau_l t1 t2 :
  rutt REv RAns RR (Tau t1) t2 -> rutt REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt1. punfold_reverse H.
  - red in IHruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma rutt_add_Tau_l t1 t2 :
  rutt REv RAns RR t1 t2 -> rutt REv RAns RR (Tau t1) t2.
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_Tau_r t1 t2 :
  rutt REv RAns RR t1 (Tau t2) -> rutt REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2; induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - constructor. eapply IHruttF; eauto.
Qed.

Lemma rutt_add_Tau_r t1 t2 :
  rutt REv RAns RR t1 t2 -> rutt REv RAns RR t1 (Tau t2).
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
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
  intros He Hk. pstep; constructor; auto.
  intros; left. apply Hk; auto.
Qed.

Lemma rutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  rutt REv RAns RR (Vis e1 k1) t2 ->
  exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> rutt REv RAns RR (k1 v1) (k2 v2)).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename B into U2.
    exists U2, e2, k2; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
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
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename A into U1.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - destruct (IHHrutt eq_refl) as (U1 & e1 & k1 & Ht0 & HAns).
    rewrite <- itree_eta in Ht0.
    exists U1, e1, k1; split; auto. now rewrite tau_eutt.
Qed.

Lemma rutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  rutt REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
  forall u1 u2, RAns U1 U2 e1 u1 e2 u2 -> rutt REv RAns RR (k1 u1) (k2 u2).
Proof.
  intros H u1 u2 Hans. punfold H.
  apply ruttF_inv_VisF with (v1 := u1) (v2 := u2) in H. pclearbot; auto.
  assumption.
Qed.
End ConstructionInversion.

Section euttge_trans_clo.

  Context {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (* Closing a relation over itrees under [euttge].
     Essentially the same closure as [eqit_trans_clo], but heterogeneous
     in the interface argument [E].
     We only define the closure under [euttge] as opposed to [eqit_trans_clo]
     capturing closure under [eq_itree] and [eutt] at the same time, since it's
     the only one we need.
   *)

  (* A transitivity functor *)
  Variant euttge_trans_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
                         (EQVl: euttge RR1 t1 t1')
                         (EQVr: euttge RR2 t2 t2')
                         (REL: r t1' t2')
                         (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
                         (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      euttge_trans_clo r t1 t2.
  Hint Constructors euttge_trans_clo : itree.

  Lemma euttge_trans_clo_mon r1 r2 t1 t2
        (IN : euttge_trans_clo r1 t1 t2)
        (LE : r1 <2= r2) :
    euttge_trans_clo r2 t1 t2.
  Proof.
    destruct IN; econstructor; eauto.
  Qed.

  Hint Resolve euttge_trans_clo_mon : paco.

End euttge_trans_clo.

(*replicate this proof for the models functor*)
(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 R1 R2 (REv : forall A B, E1 A -> E2 B -> Prop)
      (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop ) (RR : R1 -> R2 -> Prop) :
  wcompatible2 (rutt_ REv RAns RR) (euttge_trans_clo RR).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR. punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst; try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H1. pclearbot.
    apply gpaco2_clo.
    econstructor; eauto with itree.
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
Qed.

#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* The validity of the up-to [euttge] entails we can rewrite under [euttge]
   and hence also [eq_itree] during coinductive proofs of [rutt]
*)
#[global] Instance grutt_cong_eqit {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

Global Instance grutt_cong_euttge {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

(* Provide these explicitly since typeclasses eauto cannot infer them *)

#[global] Instance grutt_cong_eqit_eq {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  apply grutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance grutt_cong_euttge_eq {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  apply grutt_cong_euttge; now intros * ->.
Qed.
