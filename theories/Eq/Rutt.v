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

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
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

Inductive ruttF
          (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop)
          (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2), RR r1 r2 -> ruttF vclo sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2), sim m1 m2 -> ruttF vclo sim (TauF m1) (TauF m2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttF vclo sim (observe t1) ot2 -> ruttF vclo sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttF vclo sim ot1 (observe t2) -> ruttF vclo sim ot1 (TauF t2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> vclo sim (k1 a) (k2 b) : Prop) -> ruttF vclo sim (VisF e1 k1) (VisF e2 k2).
Hint Constructors ruttF.

Definition rutt_ (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop )
           (sim : itree E1 R1 -> itree E2 R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E2 R2) :=
  ruttF vclo sim (observe t1) (observe t2).
Hint Unfold rutt_.
Lemma rutt_monot (vclo : (itree E1 R1 -> itree E2 R2 -> Prop) -> itree E1 R1 -> itree E2 R2 -> Prop):
  (monotone2 vclo) -> monotone2 (rutt_ vclo).
Proof.
  intros. red in H. red. intros. red. red in IN. induction IN; eauto.
Qed.



Lemma rutt_id_monot : monotone2 (@id (itree E1 R1 -> itree E2 R2 -> Prop) ).
Proof. auto. Qed.



Definition rutt : itree E1 R1 -> itree E2 R2 -> Prop := paco2 (rutt_ id) bot2.

End RuttF.


Hint Resolve rutt_monot : paco.

Hint Resolve rutt_id_monot : paco.

Lemma rutt_inv_tauL {E1 E2 R1 R2 REv RAns RR} t1 t2 :
  @rutt E1 E2 R1 R2 REv RAns RR (Tau t1) t2 -> rutt REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt1. punfold_reverse H.
  - red in IHruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma rutt_add_tauL {E1 E2 R1 R2 REv RAns RR} t1 t2 :
  @rutt E1 E2 R1 R2 REv RAns RR t1 t2 -> rutt REv RAns RR (Tau t1) t2.
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_tauR {E1 E2 R1 R2 REv RAns RR} t1 t2 :
  @rutt E1 E2 R1 R2 REv RAns RR t1 (Tau t2) -> rutt REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2; induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - constructor. eapply IHruttF; eauto.
Qed.

Lemma rutt_add_tauR {E1 E2 R1 R2 REv RAns RR} t1 t2 :
  @rutt E1 E2 R1 R2 REv RAns RR t1 t2 -> rutt REv RAns RR t1 (Tau t2).
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_tauLR  {E1 E2 R1 R2 REv RAns RR} t1 t2 :
   @rutt E1 E2 R1 R2 REv RAns RR (Tau t1) (Tau t2) -> rutt REv RAns RR t1 t2.
Proof.
  intros; apply rutt_inv_tauR, rutt_inv_tauL; assumption.
Qed.

Section eqitC_rutt.
  Context {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  (* Question, is it a problem that I don't have the booleans, is that necessary?
     Would be simple to add but would necessitate some busy work *)

  (* A transitivity functor *)
  Variant eqit_trans_clo  (b1 b2 b1' b2' : bool)  (r : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' t1 t1')
      (EQVr: eqit RR2 b2 b2' t2 t2')
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      eqit_trans_clo b1 b2 b1' b2' r t1 t2.
  Hint Constructors eqit_trans_clo : core.
  (* sets directionality *)
  Definition eqitC_rutt b1 b2 := eqit_trans_clo b1 b2 false false.
  Hint Unfold eqitC_rutt : core.

  Lemma eqitC_rutt_mon b1 b2 r1 r2 t1 t2
    (IN : eqitC_rutt b1 b2 r1 t1 t2)
    (LE : r1 <2= r2) :
    eqitC_rutt b1 b2 r2 t1 t2.
  Proof.
    destruct IN; econstructor; eauto.
  Qed.

  Hint Resolve eqitC_rutt_mon : paco.

End eqitC_rutt.

(*replicate this proof for the models functor*)
Lemma eqitC_rutt_wcompat (b1 b2 : bool) E1 E2 R1 R2 (REv : forall A B, E1 A -> E2 B -> Prop)
      (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop ) (RR : R1 -> R2 -> Prop)
     (vclo: (itree E1 R1 -> itree E2 R2 -> Prop) -> (itree E1 R1 -> itree E2 R2 -> Prop) )
     (MON: monotone2 vclo)
      (CMP: compose (eqitC_rutt RR b1 b2) vclo <3= compose vclo (eqitC_rutt RR b1 b2)) :
  wcompatible2 (Rutt.rutt_ REv RAns RR vclo) (eqitC_rutt RR b1 b2).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply eqitC_rutt_mon; eauto. }
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
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H1. pclearbot. eapply MON.
    + eapply CMP. red. econstructor; eauto.
    + intros. apply gpaco2_clo; auto.
Qed.

Definition eqitC_rutt_wcompat' := eqitC_rutt_wcompat true true.

Hint Resolve (eqitC_rutt_wcompat') : paco.

Global Instance grutt_cong_eqit {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
      (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
    Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (Rutt.rutt_ REv RAns RS id) (eqitC_rutt RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
  try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

Global Instance grutt_cong_euttge {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
      (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
    Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (Rutt.rutt_ REv RAns RS id) (eqitC_rutt RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.
