
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
     Relations
     RelationClasses
     Lia.

From Paco Require Import paco.

From ITree Require Import
     Basics.GeneralWFO
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

Hint Resolve wfo_lt_le_lt wfo_le_lt_lt wfo_le_le_le wfo_add_lt_left wfo_add_lt_right wfo_add_le_left wfo_add_le_right wfo_add_monotone wfo_lt_le : wfo.
Hint Resolve wfo_add_proj_left wfo_add_proj_right : wfo_proj.
Hint Resolve wfo_le_refl : wfo_refl.

Definition _tmp_id_ T (e: T) := e.

Ltac unfold_eta :=
  repeat
  match goal with
  | |- context[@RetF ?a ?b ?c ?d] =>
    change (@RetF a b c d) with (observe (go ((@_tmp_id_ _ (@RetF)) a b c d)))
  | H: context[@RetF ?a ?b ?c ?d] |- _ =>
    change (@RetF a b c d) with (observe (go ((@_tmp_id_ _ (@RetF)) a b c d))) in H
  | |- context[@TauF ?a ?b ?c ?d] =>
    change (@TauF a b c d) with (observe (go ((@_tmp_id_ _ (@TauF)) a b c d)))
  | H: context[@TauF ?a ?b ?c ?d] |- _ =>
    change (@TauF a b c d) with (observe (go ((@_tmp_id_ _ (@TauF)) a b c d))) in H
  | |- context[@VisF ?a ?b ?c ?d ?e ?f] =>
    change (@VisF a b c d e f) with (observe (go ((@_tmp_id_ _ (@VisF)) a b c d e f)))
  | H: context[@VisF ?a ?b ?c ?d ?e ?f] |- _ =>
    change (@VisF a b c d e f) with (observe (go ((@_tmp_id_ _ (@VisF)) a b c d e f))) in H
  end;
  unfold _tmp_id_ in *.

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

Section eqit_Definition.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : Type -> Type}.
 
  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Variant eqitF (b1 b2: bool) {R1 R2} (RR: R1->R2->Prop) (sim : gwfo -> itree E R1 -> itree E R2 -> Prop) (o: gwfo) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
        (REL: RR r1 r2)
    : eqitF b1 b2 RR sim o (RetF r1) (RetF r2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, exists o', sim o' (k1 v) (k2 v))
    : eqitF b1 b2 RR sim o (VisF e k1) (VisF e k2)
  | EqTau m1 m2 o'
        (REL: sim o' m1 m2)
        (LEo: wfo_le o' o)
    : eqitF b1 b2 RR sim o (TauF m1) (TauF m2)
  | EqTauL t1 t2 o'
        (CHECK: b1)           
        (REL: sim o' t1 t2)          
        (LTo: wfo_lt o' o)
    : eqitF b1 b2 RR sim o (TauF t1) (observe t2)
  | EqTauR t1 t2 o'
        (CHECK: b2)
        (REL: sim o' t1 t2)           
        (LTo: wfo_lt o' o)
    : eqitF b1 b2 RR sim o (observe t1) (TauF t2)
  | EqNone t1 t2 o'
        (CHECK1: b1)
        (CHECK2: b2)
        (REL: sim o' t1 t2)           
        (LTo: wfo_lt o' o)
    : eqitF b1 b2 RR sim o (observe t1) (observe t2)
  .
  
  Definition eqit_ b1 b2
             (sim: forall {R1 R2},(R1->R2->Prop)-> gwfo -> itree E R1 -> itree E R2 -> Prop)
             R1 R2 (RR: R1->R2->Prop) o t1 t2 :=
    eqitF b1 b2 RR (sim RR) o (observe t1) (observe t2).

  Definition eqiti b1 b2 {R1 R2} RR o t1 t2 :=
    paco6 (eqit_ b1 b2) bot6 R1 R2 RR o t1 t2.

  Definition eqitz b1 b2 {R1 R2} RR t1 t2 := @eqiti b1 b2 R1 R2 RR wfo_zero t1 t2.

  Variant eqit b1 b2 {R1 R2} RR t1 t2 : Prop :=
  | eqit_exists o (REL: @eqiti b1 b2 R1 R2 RR o t1 t2)
  .

  (** Strong bisimulation on itrees. If [eq_itree RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)

  Definition eq_itree {R1 R2} := @eqit false false R1 R2.

  Definition eutt {R1 R2} := @eqit true true R1 R2.

  Definition euttge {R1 R2} := @eqit true false R1 R2.
  
End eqit_Definition.

Hint Constructors eqitF: core.
Hint Unfold eqit_: core.
Hint Unfold eqiti : core.
Hint Unfold eqitz : core.
Hint Constructors eqit: core.
Hint Unfold eq_itree: core.
Hint Unfold eutt: core.
Hint Unfold euttge: core.
Hint Unfold id: core.

Section eqit_Properties.

  Context {E : Type -> Type}.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono R1 R2 RR RR' b1 b2 o o' x0 x1 sim sim'
        (IN: @eqitF E b1 b2 R1 R2 RR sim o x0 x1)
        (LER: RR <2= RR')
        (LE: sim <3= sim')
        (LEo: wfo_le o o'):
    eqitF b1 b2 RR' sim' o' x0 x1.
  Proof.
    inv IN; eauto using wfo_lt_le_lt, wfo_le_le_le.
    econstructor. intros. destruct (REL v). eauto.
  Qed.

  Lemma eqit__mono b1 b2: monotone6 (@eqit_ E b1 b2).
  Proof.
    red; intros. eapply eqitF_mono; eauto using wfo_le_refl.
  Qed.

End eqit_Properties.

Hint Resolve eqit__mono : paco.

(* begin hide *)

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ _ _] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ _ _|- _ ] => red in H end).

Ltac fold_eqit :=
  (try match goal with [|- eqitF ?b1 ?b2 ?RR (?sim _ _ _) ?o (observe ?t1) (observe ?t2)]
                       => fold (eqit_ b1 b2 sim _ _ RR o t1 t2)
       end);
  (repeat match goal with [H: eqitF ?b1 ?b2 ?RR (?sim _ _ _) ?o (observe ?t1) (observe ?t2) |- _]
                          => fold (eqit_ b1 b2 sim _ _ RR o t1 t2) in H
          end).

Lemma fold_eqitF:
  forall {E R1 R2} (RR: R1 -> R2 -> Prop) b1 b2 (t1 : itree E R1) (t2 : itree E R2) o ot1 ot2,
    eqitF b1 b2 RR (upaco6 (eqit_ b1 b2) bot6 _ _ RR) o ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    eqit b1 b2 RR t1 t2.
Proof.
  intros * eq -> ->. eexists. pfold. eauto.
Qed.

Definition eqit_rel_flip {E}
           (r: forall R1 R2,(R1->R2->Prop)-> gwfo -> itree E R1 -> itree E R2 -> Prop)
           R1 R2 RR o t1 t2 :=
  r R2 R1 (flip RR) o t2 t1.

Lemma eqitF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 r:
  (fun o => flip (eqitF b2 b1 (flip RR) (fun o => flip (r o)) o)) <3= @eqitF E b1 b2 R1 R2 RR r.
Proof.
  intros. destruct PR; eauto.
Qed.

Lemma eqiti_r_flip E (r: forall R1 R2,(R1->R2->Prop)-> gwfo -> itree E R1 -> itree E R2 -> Prop) R1 R2 RR b1 b2
      (u : itree E R1) (v : itree E R2) o
      (REL: paco6 (eqit_ b2 b1) (eqit_rel_flip r) R2 R1 (flip RR) o v u)
  : paco6 (eqit_ b1 b2) r R1 R2 RR o u v.
Proof.
  intros. revert_until b2. pcofix self. pstep; intros. punfold REL.
  red. inv REL; econstructor; eauto; intros; edestruct REL0; eauto.
  destruct H1; eauto.
Qed.

Lemma eqiti_flip E R1 R2 RR b1 b2:
  forall (u : itree E R1) (v : itree E R2) o,
    eqiti b2 b1 (flip RR) o v u -> eqiti b1 b2 RR o u v.
Proof.
  eauto using eqiti_r_flip.
Qed.

Lemma eqit_flip E R1 R2 RR b1 b2:
  forall (u : itree E R1) (v : itree E R2),
    eqit b2 b1 (flip RR) v u -> eqit b1 b2 RR u v.
Proof.
  intros. destruct H. eauto using eqiti_flip.
Qed.

Lemma eqiti_mon E R1 R2 RR RR' (b1 b2 b1' b2': bool) o o' t1 t2
      (REL: @eqiti E b1 b2 R1 R2 RR o t1 t2)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LEo: wfo_le o o')
      (LERR: RR <2= RR'):
  eqiti b1' b2' RR' o' t1 t2.
Proof.
  intros. revert o o' LEo t1 t2 REL. pcofix self. intros. pstep. punfold REL.
  red. inv REL; pclearbot; econstructor; eauto using wfo_lt_le_lt, wfo_le_refl.
  intros. destruct (REL0 v). pclearbot. eauto 7 using wfo_le_refl.
Qed.

Lemma eqit_mon E R1 R2 RR RR' (b1 b2 b1' b2': bool) t1 t2
      (REL: @eqit E b1 b2 R1 R2 RR t1 t2)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <2= RR'):
  eqit b1' b2' RR' t1 t2.
Proof.
  intros. destruct REL. exists o.
  eapply eqiti_mon; eauto using wfo_le_refl.
Qed.

Hint Unfold flip: core.

Instance eqitF_Proper_R {E : Type -> Type} b1 b2 {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> (eq ==> eq_rel) ==> eq ==> eq_rel)
    (@eqitF E b1 b2 R1 R2).
Proof.
  repeat red. intros. subst. split; red; intros.
  - eapply eqitF_mono; intros; eauto using wfo_le_refl. eapply H; eauto. eapply H0; eauto.
  - eapply eqitF_mono; intros; eauto using wfo_le_refl. eapply H; eauto. eapply H0; eauto.
Qed.

Instance eqitF_Proper_R2 {E : Type -> Type} b1 b2 {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E b1 b2 R1 R2).
Proof.
  repeat red. intros. subst. split; intros.
  - eapply eqitF_mono; intros; eauto using wfo_le_refl. eapply H; eauto.
  - eapply eqitF_mono; intros; eauto using wfo_le_refl. eapply H; eauto.
Qed.
        
Instance eqit_Proper_R {E : Type -> Type} b1 b2 R1 R2
  : Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eqit E b1 b2 R1 R2).
Proof.
  unfold eq_rel. repeat red. intros. subst.
  destruct H. unfold subrelationH in *.
  eauto using eqit_mon.
Qed.
        
Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  unfold eutt. repeat red. intros. subst.
  destruct H. unfold subrelationH in *.
  eauto using eqit_mon.
Qed.


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

Hint Resolve cpn6_wcompat : core.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type}.

Global Instance Reflexive_eqitF b1 b2 {R: Type} (RR : R -> R -> Prop) sim
  : Reflexive RR -> (forall o, Reflexive (sim o)) ->
    forall o, Reflexive (@eqitF E b1 b2 _ _ RR sim o).
Proof.
  red; intros. red in H0. destruct x; eauto using wfo_le_refl.
  Grab Existential Variables. eauto.
Qed.

Global Instance Symmetric_eqitF b {R: Type} (RR : R -> R -> Prop) sim
  : Symmetric RR -> (forall o, Symmetric (sim o)) ->
    forall o, Symmetric (@eqitF E b b _ _ RR sim o).
Proof.
  red; intros. red in H0. dependent destruction H1; eauto.
  econstructor. intros. destruct (REL v). eauto.
Qed.

Global Instance Reflexive_eqit_ b1 b2 R (RR: R->R->Prop) (sim: forall R1 R2,(R1->R2->Prop)->_->_->_->Prop)
  : Reflexive RR ->
    (forall o, Reflexive (sim R R RR o)) ->
    forall o, Reflexive (@eqit_ E b1 b2 sim R R RR o).
Proof.
  red. intros. eapply Reflexive_eqitF; eauto.
Qed.

Global Instance Symmetric_eqit_ b R (RR: R->R->Prop) (sim: forall R1 R2,(R1->R2->Prop)->_->_->_->Prop)
  : Symmetric RR ->
    (forall o,  Symmetric (sim R R RR o)) ->
    forall o, Symmetric (@eqit_ E b b sim R R RR o).
Proof.
  red. intros. eapply Symmetric_eqitF; eauto.
Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen b1 b2 r rg R (RR:R->R->Prop) o
  : Reflexive RR ->
    Reflexive (gpaco6 (@eqit_ E b1 b2) (cpn6 (eqit_ b1 b2)) r rg R R RR o).
Proof.
  gcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto using wfo_le_refl with paco.
Qed.

Global Instance Reflexive_eqiti b1 b2 R (RR:R->R->Prop) o
  : Reflexive RR -> Reflexive (@eqiti E b1 b2 R R RR o).
Proof.
  ginit. intros. apply Reflexive_eqit_gen; eauto.
Qed.

Global Instance Reflexive_eqit b1 b2 R (RR:R->R->Prop)
  : Reflexive RR -> Reflexive (@eqit E b1 b2 R R RR).
Proof.
  econstructor. apply Reflexive_eqiti. eauto.
  Grab Existential Variables. eapply wfo_zero.
Qed.

Global Instance Symmetric_eqiti b R (RR:R->R->Prop) o
  : Symmetric RR -> Symmetric (@eqiti E b b R R RR o).
Proof.
  red; intros. apply eqiti_flip.
  eapply eqiti_mon; eauto using wfo_le_refl.
Qed.

Global Instance Symmetric_eqit b R (RR:R->R->Prop)
  : Symmetric RR -> Symmetric (@eqit E b b R R RR).
Proof.
  red. intros. destruct H0. exists o.
  apply Symmetric_eqiti; eauto.
Qed.

Global Instance eq_sub_euttge R RR
  : subrelation (@eq_itree E R R RR) (euttge RR).
Proof.
  red; intros. destruct H. exists o.
  ginit. revert_until E.
  gcofix CIH. intros.
  punfold REL. gstep.
  red in REL |- *.
  inv REL; pclearbot; eauto 7 with paco.
  econstructor. intros. destruct (REL0 v). pclearbot. eauto with paco.
Qed.

Global Instance euttge_sub_eutt R RR
  : subrelation (@euttge E R R RR) (eutt RR).
Proof.
  red; intros. destruct H. exists o.
  ginit. revert_until E.
  gcofix CIH. intros.
  punfold REL. gstep.
  red in REL |- *.
  inv REL; pclearbot; eauto 7 with paco.
  econstructor. intros. destruct (REL0 v). pclearbot. eauto with paco.
Qed.

Global Instance eq_sub_eutt R RR
  : subrelation (@eq_itree E R R RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. apply H.
Qed.

End eqit_gen.

Hint Resolve Reflexive_eqit Reflexive_eqiti Reflexive_eqit_gen : reflexivity.

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R: Type}.

Global Instance Reflexive_eqitF_eq b1 b2 sim
  : (forall o, Reflexive (sim o)) ->
    forall o, Reflexive (@eqitF E b1 b2 R R eq sim o).
Proof.
  apply Reflexive_eqitF; eauto.
Qed.

Global Instance Symmetric_eqitF_eq b sim
  : (forall o, Symmetric (sim o)) ->
    forall o, Symmetric (@eqitF E b b R R eq sim o).
Proof.
  apply Symmetric_eqitF; eauto.
Qed.

Global Instance Reflexive_eqit__eq b1 b2 (sim: forall R1 R2,(R1->R2->Prop)->_->_->_->_)
  : (forall o, Reflexive (sim R R eq o)) ->
    forall o, Reflexive (@eqit_ E b1 b2 sim R R eq o).
Proof. intros. eapply Reflexive_eqit_; eauto. Qed.

Global Instance Symmetric_eqit__eq b (sim: forall R1 R2,(R1->R2->Prop)->_->_->_->_)
  : (forall o, Symmetric (sim R R eq o)) ->
    forall o, Symmetric (@eqit_ E b b sim R R eq o).
Proof. apply Symmetric_eqit_; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

Global Instance Reflexive_eqit_gen_eq b1 b2 r rg
  : forall o, Reflexive (gpaco6 (@eqit_ E b1 b2) (cpn6 (eqit_ b1 b2)) r rg R R eq o).
Proof.
  intros. apply Reflexive_eqit_gen; eauto.
Qed.

Global Instance Reflexive_eqiti_eq b1 b2 o
  : Reflexive (@eqiti E b1 b2 R R eq o).
Proof.
  apply Reflexive_eqiti; eauto.
Qed.

Global Instance Reflexive_eqit_eq b1 b2
  : Reflexive (@eqit E b1 b2 R R eq).
Proof.
  apply Reflexive_eqit; eauto.
Qed.

Global Instance Symmetric_eqiti_eq b o
  : Symmetric (@eqiti E b b R R eq o).
Proof.
  apply Symmetric_eqiti; eauto.
Qed.

Global Instance Symmetric_eqit_eq b
  : Symmetric (@eqit E b b R R eq).
Proof.
  apply Symmetric_eqit; eauto.
Qed.

(** *** Congruence properties *)

Global Instance eqiti_observe b1 b2 o:
  Proper (eqiti b1 b2 eq o ==> going (eqiti b1 b2 eq o)) (@observe E R).
Proof.
  constructor. punfold H.
Qed.

Global Instance eqit_observe b1 b2:
  Proper (eqit b1 b2 eq ==> going (eqit b1 b2 eq)) (@observe E R).
Proof.
  constructor. destruct H. exists o. punfold REL.
Qed.

Global Instance eqiti_tauF b1 b2 o:
  Proper (eqiti b1 b2 eq o ==> going (eqiti b1 b2 eq o)) (@TauF E R _).
Proof.
  constructor. pstep. econstructor; eauto using wfo_le_refl.
Qed.

Global Instance eqit_tauF b1 b2:
  Proper (eqit b1 b2 eq ==> going (eqit b1 b2 eq)) (@TauF E R _).
Proof.
  constructor. destruct H. exists o. pstep. econstructor; eauto using wfo_le_refl.
Qed.

Global Instance eqiti_visF b1 b2 o {u} (e: E u):
  Proper (pointwise_relation _ (eqiti b1 b2 (@eq R) o) ==> going (eqiti b1 b2 eq o)) (VisF e).
Proof.
  econstructor. pstep.
  econstructor. intros. specialize (H v). eauto.
Qed.

Global Instance eqit_visF b1 b2 {u} (e: E u) :
  Proper (pointwise_relation _ (eqit b1 b2 (@eq R)) ==> going (eqit b1 b2 eq)) (VisF e).
Proof.
  econstructor. exists wfo_zero. pstep.
  econstructor. intros. destruct (H v). eauto.
Qed.

Global Instance observing_sub_eqiti b1 b2 o :
  subrelation (observing eq) (@eqiti E b1 b2 R R eq o).
Proof.
  repeat red; intros. pstep. red. rewrite H.
  apply Reflexive_eqitF; eauto.
  intros. left. apply Reflexive_eqiti. eauto.
Qed.

Global Instance observing_sub_eqit b1 b2 :
  subrelation (observing eq) (@eqit E b1 b2 R R eq).
Proof.
  exists wfo_zero. eapply observing_sub_eqiti. eauto.
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
  intros. destruct H. punfold REL. inv REL; try inv CHECK; try inv CHECK1; try inv CHECK2; eauto.
Qed.

Lemma eq_itree_inv_vis {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros. destruct H. punfold REL; inv REL; auto_inj_pair2; subst; try inv CHECK; try inv CHECK1; try inv CHECK2.
  eexists; split; eauto.
  intros. destruct (REL0 u); try contradiction; pclearbot; eauto.
Qed.

Lemma eq_itree_inv_tau {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; destruct H. punfold REL; inv REL; try inv CHECK; try inv CHECK1; try inv CHECK2; pclearbot; eauto.
Qed.

Lemma eqit_inv_ret {E R1 R2 RR} b1 b2 r1 r2 :
  @eqit E b1 b2 R1 R2 RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. destruct H as [? H].
  assert (WFo := wfo_wf _ o). induction WFo.
  punfold H. inv H; eauto.
  eapply H1; eauto.
  pclearbot. rewrite <-H3, <-H4. punfold REL.
Qed.

Lemma eqit_inv_vis {E R1 R2 RR} b1 b2 {u} (e1 e2: E u) (k1: u -> itree E R1) (k2: u -> itree E R2) :
  eqit b1 b2 RR (Vis e1 k1) (Vis e2 k2) -> e1 = e2 /\ (forall u, eqit b1 b2 RR (k1 u) (k2 u)).
Proof.
  intros. destruct H as [? H].
  assert (WFo := wfo_wf _ o). induction WFo.
  punfold H. repeat red in H. simpl in H.
  dependent destruction H.
  - split; eauto. intros y. destruct (REL y). pclearbot. eauto.
  - eapply H1; eauto.
    pclearbot. rewrite <-x1, <-x. punfold REL.
Qed.

Lemma eqiti_inv_tauL E b1 R1 R2 RR o o' t1 t2
      (REL: @eqiti E b1 true R1 R2 RR o (Tau t1) t2)
      (LT: wfo_lt o o')
  : eqiti b1 true RR o' t1 t2.
Proof.
  revert_until RR. pcofix CIH. intros.
  revert_until o. assert (WF := wfo_wf _ o). induction WF; intros.
  pfold. punfold REL. red in REL |- *. inv REL.
  - econstructor; eauto.
    pclearbot. left. eapply paco6_mon_bot; eauto.
    eapply eqiti_mon; eauto.
  - pclearbot. punfold REL0.
    eapply eqitF_mono; eauto using wfo_lt_le, wfo_le_le_le, upaco6_mon_bot.
  - econstructor; eauto.
    right. eapply CIH; eauto.
    pclearbot. punfold REL0. pfold. rewrite <- H2. eauto.
  - econstructor; eauto.
    right. eapply CIH; eauto.
    pclearbot. punfold REL0. pfold. rewrite <- H2. eauto.
Qed.

Lemma eqiti_inv_tauR E b2 R1 R2 RR o o' t1 t2
      (REL: @eqiti E true b2 R1 R2 RR o t1 (Tau t2))      
      (LT: wfo_lt o o')
  : eqiti true b2 RR o' t1 t2.
Proof.
  revert_until RR. pcofix CIH. intros.
  revert_until o. assert (WF := wfo_wf _ o). induction WF; intros.
  pfold. punfold REL. red in REL |- *. inv REL.
  - econstructor; eauto.
    pclearbot. left. eapply paco6_mon_bot; eauto.
    eapply eqiti_mon; eauto.
  - econstructor; eauto.
    right. eapply CIH; eauto.
    pclearbot. punfold REL0. pfold. rewrite <- H3. eauto.
  - pclearbot. punfold REL0.
    eapply eqitF_mono; eauto using wfo_lt_le, wfo_le_le_le, upaco6_mon_bot.
  - econstructor; eauto.
    right. eapply CIH; eauto.
    pclearbot. punfold REL0. pfold. rewrite <- H3. eauto.
Qed.

Lemma eqiti_inv_tauLR E b1 b2 R1 R2 RR o t1 t2
      (REL: @eqiti E b1 b2 R1 R2 RR o (Tau t1) (Tau t2))
  : eqiti b1 b2 RR o t1 t2.
Proof.
  revert_until o. assert (WF := wfo_wf _ o). induction WF as [o _ HYP]; intros.
  punfold REL. red in REL. inv REL; pclearbot; subst.
  - eauto using eqiti_mon.
  - destruct b1; inv CHECK.
    eapply eqiti_inv_tauR; eauto.
    punfold REL0. pfold. red. rewrite <-H. eauto.
  - destruct b2; inv CHECK.
    eapply eqiti_inv_tauL; eauto.
    punfold REL0. pfold. red. rewrite <-H0. eauto.
  - pstep. econstructor; eauto.
    left. eapply HYP; eauto.
    rewrite <-H,<-H0. pstep. punfold REL0.
Qed.

Lemma eqit_inv_ret_vis: forall {E X R1 R2 RR} b1 b2 (r: R1) (e: E X) k,
    @eqit E b1 b2 R1 R2 RR (Ret r) (Vis e k) -> False.
Proof.
  intros. destruct H as [? H].
  assert (WF := wfo_wf _ o). induction WF as [o _ HYP]; intros.
  punfold H; inv H.
  eapply HYP; eauto.
  rewrite <-H1, <-H2. pclearbot. pstep. punfold REL.
Qed.

Lemma eutt_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
Proof.
  intros. destruct H. eapply eqit_inv_ret_vis; eauto.
Qed.

Lemma eqitree_inv_ret_vis: forall {X Y E} (x: X) (e: E Y) k, Ret x ≅ Vis e k -> False.
Proof.
  intros. destruct H. eapply eqit_inv_ret_vis; eauto.
Qed.

Lemma eqit_inv_tau_vis: forall {E X R1 R2 RR} b2 (e: E X) k t,
    @eqit E false b2 R1 R2 RR (Tau t) (Vis e k) -> False.
Proof.
  intros. destruct H as [? H].
  punfold H; inv H.
  inv CHECK. inv CHECK1.
Qed.

Lemma eqit_inv_vis_tau: forall {E X R1 R2 RR} b1 (e: E X) k t,
    @eqit E b1 false R1 R2 RR (Vis e k) (Tau t) -> False.
Proof.
  intros. destruct H as [? H].
  punfold H; inv H.
  inv CHECK. inv CHECK2.
Qed.

Lemma euttge_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Vis e k ≳ Tau a -> False.
Proof.
  intros. destruct H. eapply eqit_inv_vis_tau; eauto.
Qed.

Lemma eqitree_inv_tau_vis: forall {E A B} (e: E A) (k : A -> itree E B) (a : itree E B), Tau a ≅ Vis e k -> False.
Proof.
  intros. destruct H. eapply eqit_inv_tau_vis; eauto.
Qed.

Lemma eqit_inv_ret_tau: forall {E R1 R2 RR} b1 (r: R1) t,
    @eqit E b1 false R1 R2 RR (Ret r) (Tau t) -> False.
Proof.
  intros. destruct H as [? H].
  punfold H; inv H.
  inv CHECK. inv CHECK2.
Qed.

Lemma eqit_inv_tau_ret: forall {E R1 R2 RR} b2 (r: R2) t,
    @eqit E false b2 R1 R2 RR (Tau t) (Ret r) -> False.
Proof.
  intros. destruct H as [? H].
  punfold H; inv H.
  inv CHECK. inv CHECK1.
Qed.

Lemma euttge_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≳ Tau a -> False.
Proof.
  intros. destruct H. eapply eqit_inv_ret_tau; eauto.
Qed.

Lemma eqitree_inv_ret_tau: forall {E A} (r : A) (a : itree E A),
    Ret r ≅ Tau a -> False.
Proof.
  intros. destruct H. eapply eqit_inv_ret_tau; eauto.
Qed.

Lemma eutt_inv_ret {E R} r1 r2 :
  (Ret r1: itree E R) ≈ (Ret r2) -> r1 = r2.
Proof.
  intros. destruct H. eapply eqit_inv_ret; eauto.
Qed.

Lemma eqitree_inv_ret {E R} r1 r2 :
  (Ret r1: itree E R) ≅ (Ret r2) -> r1 = r2.
Proof.
  intros. destruct H. eapply eqit_inv_ret; eauto.
Qed.

(** [eqit] is a congruence for [itree] constructors. *)

Lemma eqit_tauL {E R1 R2 RR} b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit true b2 RR t1 t2 -> eqit true b2 RR (Tau t1) t2.
Proof.
  intros. destruct H as [? H]. eexists. pstep. econstructor; eauto using wfo_add_one.
Qed.

Lemma eqit_tauR {E R1 R2 RR} b1 (t1 : itree E R1) (t2 : itree E R2) :
  eqit b1 true RR t1 t2 -> eqit b1 true RR t1 (Tau t2).
Proof.
  intros. destruct H as [? H]. eexists. pstep. econstructor; eauto using wfo_add_one.
Qed.

Lemma eqit_tau {E R1 R2 RR} b1 b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit b1 b2 RR (Tau t1) (Tau t2) <-> eqit b1 b2 RR t1 t2.
Proof.
  split; intros [].
  - eexists. eapply eqiti_inv_tauLR. eauto.
  - eexists. pstep. econstructor; eauto using wfo_le_refl.
Qed.

Lemma eqit_vis {E R1 R2 RR} b1 b2 {U} (e : E U)
      (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
      (forall u, eqit b1 b2 RR (k1 u) (k2 u))
  <-> eqit b1 b2 RR (Vis e k1) (Vis e k2).
Proof.
  split; intros.
  - exists wfo_zero. pstep. econstructor. intros. destruct (H v). eauto.
  - eapply eqit_inv_vis; eauto.
Qed.

Lemma eqit_ret {E R1 R2 RR} b1 b2 (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eqit E b1 b2 _ _ RR (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - exists wfo_zero. pstep. constructor; auto.
  - eapply eqit_inv_ret; eauto.
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
  exists wfo_zero. pstep.
  unfold_eqit. simpobs. simpl. subst. fold_eqit.
  pstep_reverse. eapply Reflexive_eqiti; eauto.
Qed.

(*************************)
(** *** Eqit Lower Order *)
(*************************)

Variant euttOrdF (euttOrd : Type) :=
| OBaseF
| OTauF (o : euttOrd)
| OStutterF (o : euttOrd)
.
Arguments OBaseF {euttOrd}.
Arguments OStutterF {euttOrd} o.
Arguments OTauF {euttOrd} o.

CoInductive euttOrd : Type := ord_go
{ ord_observe : euttOrdF euttOrd }.

Notation euttOrd' := (euttOrdF euttOrd).
Notation OBase := {| ord_observe := OBaseF |}.
Notation OTau o := {| ord_observe := OTauF o |}.
Notation OStutter o := {| ord_observe := OStutterF o |}.

Inductive euttOrd_le': euttOrd' -> euttOrd' -> Prop :=
| euttOrd_le_refl
    o
  : euttOrd_le' o o
| euttOrd_le_step
    o1 o2
    (REL: euttOrd_le' o1 (ord_observe o2))
  : euttOrd_le' o1 (OStutterF o2)
| euttOrd_le_tau
    o1 o2
    (REL: euttOrd_le' o1 (ord_observe o2))
  : euttOrd_le' o1 (OTauF o2)
.
Hint Constructors euttOrd_le'.

Definition euttOrd_le o1 o2 := euttOrd_le' (ord_observe o1) (ord_observe o2).
Hint Unfold euttOrd_le.

Inductive euttOrd_lt': euttOrd' -> euttOrd' -> Prop :=
| euttOrd_lt_step
    o1 o2
    (REL: euttOrd_le' o1 (ord_observe o2))
  : euttOrd_lt' o1 (OStutterF o2)
| euttOrd_tau
    o1 o2
    (REL: euttOrd_lt' o1 (ord_observe o2))
  : euttOrd_lt' o1 (OTauF o2)
.
Hint Constructors euttOrd_lt'.

Definition euttOrd_lt o1 o2 := euttOrd_lt' (ord_observe o1) (ord_observe o2).
Hint Unfold euttOrd_lt.

Lemma euttOrd_lt_le: forall i j, euttOrd_lt i j -> euttOrd_le i j.
Proof.
  unfold euttOrd_le, euttOrd_lt. intros i j.
  generalize (ord_observe i) as oi, (ord_observe j) as oj.
  intros. induction H; eauto.
Qed.

Lemma euttOrd_le_le_le: forall i j k, euttOrd_le i j -> euttOrd_le j k -> euttOrd_le i k.
Proof.
  unfold euttOrd_le. intros i j k.
  generalize (ord_observe i) as oi, (ord_observe j) as oj, (ord_observe k) as ok.
  intros. revert ok H0.
  induction H; eauto; intros.
  - remember (OStutterF o2) as o2' in *. induction H0; subst; eauto.
  - remember (OTauF o2) as o2' in *. induction H0; subst; eauto.
Qed.

Lemma euttOrd_lt_le_lt: forall i j k, euttOrd_lt i j -> euttOrd_le j k -> euttOrd_lt i k.
Proof.
  unfold euttOrd_le, euttOrd_lt. intros i j k.
  generalize (ord_observe i) as oi, (ord_observe j) as oj, (ord_observe k) as ok.
  intros. revert ok H0.
  induction H; eauto; intros.
  - remember (OStutterF o2) as o2' in *. induction H0; subst; eauto.
    econstructor. eapply (euttOrd_lt_le (ord_go _)). eauto.
  - remember (OTauF o2) as o2' in *. induction H0; subst; eauto.
    econstructor. eapply (euttOrd_lt_le (ord_go _)). eauto.
Qed.

Lemma euttOrd_le_lt_lt: forall i j k, euttOrd_le i j -> euttOrd_lt j k -> euttOrd_lt i k.
Proof.
  unfold euttOrd_le, euttOrd_lt. intros i j k.
  generalize (ord_observe i) as oi, (ord_observe j) as oj, (ord_observe k) as ok.
  intros. revert oi H.
  induction H0; eauto; intros.
  econstructor. eapply (euttOrd_le_le_le (ord_go _) (ord_go _)); eauto.
Qed.

Program Definition euttOrdWf : bwfo :=
  {| bwfo_set := sig (Acc euttOrd_lt);
     bwfo_le o1 o2 := euttOrd_le o1 o2;
     bwfo_lt o1 o2 := euttOrd_lt o1 o2;
  |}.
Next Obligation. eauto using euttOrd_lt_le. Qed.
Next Obligation. eauto using euttOrd_le_le_le. Qed.
Next Obligation. eauto using euttOrd_lt_le_lt. Qed.
Next Obligation. eauto using euttOrd_le_lt_lt. Qed.
Next Obligation.
  red; intros. destruct a as [o WFo].
  generalize WFo. induction WFo as [o' _ HYP]. intros.
  econstructor; intros. destruct y as [y WFy]. eauto.
Qed.

CoFixpoint eutt_ord {E R1 R2} (ot1: itree' E R1) (ot2: itree' E R2) : euttOrd :=
  match ot1, ot2 with
  | TauF t1', TauF t2' => OTau (eutt_ord (observe t1') (observe t2'))
  | TauF t1', _ => OStutter (eutt_ord (observe t1') ot2)
  | _, TauF t2' => OStutter (eutt_ord ot1 (observe t2'))
  | _, _ => OBase
  end.

Lemma eutt_ord_wf {E b1 b2 R1 R2 RR o t1 t2}
      (REL: @eqiti E b1 b2 R1 R2 RR o t1 t2):
  Acc euttOrd_lt (eutt_ord (observe t1) (observe t2)).
Proof.
  revert t1 t2 REL. assert (WF:= wfo_wf gwfo o).
  induction WF as [o ACC HYP]. intros.
  econstructor. intros. red in H.
  remember (ord_observe y) as oy.
  remember (ord_observe (eutt_ord (observe t1) (observe t2))) as ot.
  revert t1 t2 REL y Heqoy Heqot. induction H; intros.
  - punfold REL0. red in REL0. revert_until REL0.
    inv REL0; intros; subst; try (inv Heqot; fail); pclearbot.
    + assert (EQo2: o2 = eutt_ord (observe t0) (observe t3)).
      { destruct (observe t3); inv Heqot; eauto. }
      subst. econstructor. intros. eapply HYP; eauto using euttOrd_lt_le_lt.
    + assert (EQo2: o2 = eutt_ord (observe t0) (observe t3)).
      { destruct (observe t0); inv Heqot; eauto. }
      subst. econstructor. intros. eapply HYP; eauto using euttOrd_lt_le_lt.
    + econstructor; intros.
      eapply (HYP _ LTo _ _ REL1).
      eapply euttOrd_lt_le_lt; eauto.
      eapply euttOrd_le_le_le; eauto.
      red. rewrite <- Heqot. eauto.
  - subst. genobs t1 ot1. genobs t2 ot2.
    destruct ot1, ot2; inversion Heqot.
    eapply IHeuttOrd_lt'; [| |rewrite <- H1]; eauto.
    eapply eqiti_inv_tauLR.
    punfold REL. pfold. red. rewrite Heqot1, Heqot2. eauto.
Qed.

Lemma eqiti_lower_order {E b1 b2 R1 R2 RR o t1 t2}
      (REL: @eqiti E b1 b2 R1 R2 RR o t1 t2):
  exists so: euttOrdWf, eqiti b1 b2 RR (gwf_embed so) t1 t2.
Proof.
  exists (exist _ (eutt_ord (observe t1) (observe t2)) (eutt_ord_wf REL)).
  revert_until b2. pcofix CIH. intros.
  generalize (eutt_ord_wf REL) as WF.  
  revert_until o. assert (WFo := wfo_wf _ o). induction WFo as [o _ HYP]. intros.
  revert WF. punfold REL. pfold. red. inv REL; intros.
  - eauto.
  - econstructor. intros. specialize (REL0 v). destruct REL0. eauto.
  - pclearbot. econstructor; eauto.
    eapply gwf_embed_le_preserve. do 2 econstructor.
  - genobs t3 ot3. destruct ot3.
    + unfold_eta. eapply EqTauL; eauto.
      eapply gwf_embed_lt_preserve. do 2 econstructor.
    + econstructor. right. eapply CIH.
      eapply gwf_embed_le_preserve. do 2 econstructor.
    + unfold_eta. eapply EqTauL; eauto.
      eapply gwf_embed_lt_preserve. do 2 econstructor.
  - genobs t0 ot0. destruct ot0.
    + unfold_eta. eapply EqTauR; eauto.
      eapply gwf_embed_lt_preserve. do 2 econstructor.
    + econstructor. right. eapply CIH.
      eapply gwf_embed_le_preserve. do 2 econstructor.
    + unfold_eta. eapply EqTauR; eauto.
      eapply gwf_embed_lt_preserve. do 2 econstructor.
  - pclearbot. hexploit HYP; eauto. intros EQIT. punfold EQIT.
Grab Existential Variables.
  { pclearbot. simpl in *. rewrite Heqot0. punfold REL0. }
  { pclearbot. punfold REL0. red in REL0. rewrite <-Heqot0 in REL0.
    destruct b2; inversion CHECK. eauto using eqiti_inv_tauL. }
  { pclearbot. simpl in *. rewrite Heqot0. punfold REL0. }
  { pclearbot. simpl in *. rewrite Heqot3. punfold REL0. }
  { pclearbot. punfold REL0. red in REL0. rewrite <-Heqot3 in REL0.
    destruct b1; inversion CHECK. eauto using eqiti_inv_tauR. }
  { pclearbot. simpl in *. rewrite Heqot3. punfold REL0. }
  { pclearbot. eauto. }
  { pclearbot. eauto. }
Qed.

Lemma eqit_lower_order {E b1 b2 R1 R2 RR t1 t2}
      (REL: @eqit E b1 b2 R1 R2 RR t1 t2):
  exists so: euttOrdWf, eqiti b1 b2 RR (gwf_embed so) t1 t2.
Proof. destruct REL. eauto using eqiti_lower_order. Qed.

Lemma euttOrd_small n (so: euttOrdWf) :
  wfo_lt (gwf_embed so) (wfo_nat (S (S n))).
Proof.
  econstructor. simpl. nia.
Qed.

Lemma eq_itree_zero {E} b1 b2 R1 R2 RR t1 t2
      (REL: @eq_itree E R1 R2 RR t1 t2):
  eqiti b1 b2 RR wfo_zero t1 t2.
Proof.
  revert_until b2. pcofix CIH. intros.
  destruct REL. punfold REL. pstep. red.
  inv REL; try inv CHECK; try inv CHECK1; eauto.
  - econstructor; eauto.
    intros. destruct (REL0 v). pclearbot.
    eexists. left. eapply paco6_mon_bot; [|eauto].
    eapply eqiti_mon; eauto with wfo_refl; destruct b1, b2; eauto.
  - econstructor; eauto using wfo_non_negative.
    pclearbot. right. eauto.
Qed.

(********************************)
(** *** Eqit "Up-to" Principles *)
(********************************)

(* Bind Closure *)

Variant eqit_bind_rel {E} r s R1 R2 (RR:R1->R2->Prop) :
  gwfo -> itree E R1 -> itree E R2 -> Prop :=
| eqit_bind_split o o1 o2 U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
    (EQV: r U1 U2 RU o1 t1 t2 : Prop)
    (REL: forall u1 u2, RU u1 u2 -> s R1 R2 RR o2 (k1 u1) (k2 u2) : Prop)
    (LEo: wfo_le (wfo_add o1 o2) o)
: eqit_bind_rel r s R1 R2 RR o (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eqit_bind_rel: core.
Arguments eqit_bind_split {E r s R1 R2 RR}.

Definition eqit_bind_clo {E} r := @eqit_bind_rel E r r.
Hint Unfold eqit_bind_clo: core.

Lemma eqit_bind_rel_monotone {E} r r' s s' R1 R2 RR o o' x y
      (REL: @eqit_bind_rel E r s R1 R2 RR o x y)
      (LEr: r <6= r')
      (LEs: s <6= s')
      (LEo: wfo_le o o')
  : eqit_bind_rel r' s' R1 R2 RR o' x y.
Proof.
  dependent destruction REL.
  econstructor; eauto 7 using wfo_le_le_le.
Qed.

Lemma eqit_bind_clo_prespectful {E} b1 b2:
  prespectful6 (@eqit_ E b1 b2) eqit_bind_clo.
Proof.
  econstructor; repeat intro.
  - eapply eqit_bind_rel_monotone; eauto using wfo_le_refl.
  - red in PR. eapply eqit_bind_rel_monotone in PR; [|apply GF|intros; apply PR0|eauto using wfo_le_refl].
    pstep. red. inversion PR; subst.
    rewrite !unfold_bind_. inversion EQV.
    + specialize (REL _ _ REL0). apply GF in REL.
      eapply eqitF_mono; eauto using rclo6.
      eapply wfo_le_le_le, LEo; apply wfo_add_proj_right.
    + econstructor. intros. destruct (REL0 v). eauto 9 using wfo_le_refl.      
    + simpl. red in EQV.
      econstructor; [eauto 8 using wfo_le_refl, rclo6|].
      eapply wfo_le_le_le; [|eauto].
      eapply wfo_add_le_left; eauto.
    + rewrite <-unfold_bind_. econstructor; eauto 8 using wfo_le_refl. cycle 1.
      eapply wfo_lt_le_lt; eauto. eapply wfo_add_lt_left; eauto.
    + rewrite <-unfold_bind_. econstructor; eauto 8 using wfo_le_refl.
      eapply wfo_lt_le_lt; eauto. eapply wfo_add_lt_left; eauto.
    + rewrite <-!unfold_bind_. econstructor; eauto.
      * right. right. econstructor; eauto using wfo_le_refl.
      * eauto with wfo.
Qed.

Lemma eqit_clo_bind E b1 b2:
  @eqit_bind_clo E <7= gupaco6 (eqit_ b1 b2) (cpn6 (eqit_ b1 b2)).
Proof.
  intros. eapply prespect6_uclo; eauto using eqit_bind_clo_prespectful with paco.
Qed.

Arguments eqit_clo_bind : clear implicits.

(* Transitivity Closure *)

Inductive eqit_transL_clo {E} b b'
          (r: forall R1 R2,(R1->R2->Prop)-> gwfo -> itree E R1 -> itree E R2 -> Prop)
          R1 R2 (RR: R1->R2->Prop) o (t1: itree E R1) (t2: itree E R2) : Prop :=
| eqit_transL_clo_intro o' o1 R1' R1R1' R1'R2 (t1': itree E R1')
      (EQVl: @eqiti E b b' R1 R1' R1R1' o1 t1 t1')
      (REL: r R1' R2 R1'R2 o' t1' t2 : Prop)
      (LEo: wfo_le (wfo_add o' o1) o)
      (LERR: forall t1 t2 t1', R1R1' t1 t1' -> R1'R2 t1' t2 -> RR t1 t2)
  : eqit_transL_clo b b' r R1 R2 RR o t1 t2
.
Hint Constructors eqit_transL_clo: core.

Inductive eqit_transR_clo {E} b b'
          (r: forall R1 R2,(R1->R2->Prop)-> gwfo -> itree E R1 -> itree E R2 -> Prop)
          R1 R2 (RR: R1->R2->Prop) o (t1: itree E R1) (t2: itree E R2) : Prop :=
| eqit_transR_clo_intro o' o2 R2' R2R2' R1R2' (t2': itree E R2')
      (EQVr: @eqiti E b b' R2 R2' R2R2' o2 t2 t2')
      (REL: r R1 R2' R1R2' o' t1 t2' : Prop)
      (LERR2: forall t1 t2 t2', R2R2' t2 t2' -> R1R2' t1 t2' -> RR t1 t2)
      (LEo: wfo_le (wfo_add o' o2) o)      
  : eqit_transR_clo b b' r R1 R2 RR o t1 t2
.
Hint Constructors eqit_transR_clo: core.

Lemma eqit_transL_clo_monotone {E} b b' r r' R1 R2 RR o o' x y
      (REL: @eqit_transL_clo E b b' r R1 R2 RR o x y)
      (LEr: r <6= r')
      (LEo: wfo_le o o')
  : eqit_transL_clo b b' r' R1 R2 RR o' x y.
Proof.
  dependent destruction REL.
  econstructor; eauto 7 using wfo_le_le_le.
Qed.

Lemma eqit_transR_clo_monotone {E} b b' r r' R1 R2 RR o o' x y
      (REL: @eqit_transR_clo E b b' r R1 R2 RR o x y)
      (LEr: r <6= r')
      (LEo: wfo_le o o')
  : eqit_transR_clo b b' r' R1 R2 RR o' x y.
Proof.
  dependent destruction REL.
  econstructor; eauto 7 using wfo_le_le_le.
Qed.

Lemma eqit_transL_clo_prespectful {E} bL bR:
  prespectful6 (@eqit_ E bL bR) (@eqit_transL_clo E bL bR).
Proof.
  econstructor.
  { repeat intro; eapply eqit_transL_clo_monotone; eauto using wfo_le_refl. }

  intros ? ? ? ? R1 R2 RR o t1 t2 [].
  eapply paco6_mon; [|intros; right; apply PR].
  assert (GFl := GF _ _ _ _ _ _ REL).
  punfold EQVl. pstep. red in GFl, EQVl |- *.

  revert EQVl. inversion GFl; intros; subst.

  (* [Ret] t1' = Ret r1, t2 = Ret r2 *)
  { inversion EQVl; subst; eauto; pclearbot.
    (* [TauL] t1 = Tau t0 *)
    { unfold_eta. eapply EqTauL; eauto; cycle 1.
      { instantiate (1:= o'0). eauto with wfo wfo_proj. }
      punfold REL1. red in REL1. rewrite H3 in REL1. left. pstep. red.
      revert REL1. clear H2. revert t0.
      assert (WF := wfo_wf _ o'0). induction WF as [ord _ HYP]. intros.
      dependent destruction REL1.
      - rewrite <-x. econstructor. eauto.
      - rewrite <-x0. econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x in REL1.
        eapply HYP; eauto. eauto with wfo.
      - econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x, x0 in REL1. 
        eapply HYP; eauto. eauto with wfo.
    }
    (* [Stutter] t1 = t0 *)
    { unfold_eta. eapply EqNone; eauto; cycle 1.
      { instantiate (1:= o'0). eauto with wfo wfo_proj. }
      punfold REL1. red in REL1. rewrite H3 in REL1. left. pstep. red.
      revert REL1. clear H2. revert t0.
      assert (WF := wfo_wf _ o'0). induction WF as [ord _ HYP]. intros.
      dependent destruction REL1.
      - rewrite <-x. econstructor. eauto.
      - rewrite <-x0. econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x in REL1.
        eapply HYP; eauto. eauto with wfo.
      - econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x, x0 in REL1. 
        eapply HYP; eauto. eauto with wfo.
    }
  }
  
  (* [Vis] t1' = Vis e k1, t2 = Vis e k2 *)
  { dependent destruction EQVl; pclearbot. 
    (* [Vis] t1 = Vis e k0 *)
    { rewrite <-x. eapply EqVis; intros.
      destruct (REL0 v), (REL1 v); pclearbot.
      eexists. right. econstructor; eauto with wfo_refl.
    }
    (* [TauL] t1 = Tau t0 *)
    { rewrite <-x0. unfold_eta. econstructor; eauto; cycle 1.
      { instantiate (1:= o'0). eauto with wfo wfo_proj. }
      punfold REL1. red in REL1. rewrite x in REL1. left. pstep. red.
      revert REL1. clear x0. revert t0.
      assert (WF := wfo_wf _ o'0). induction WF as [ord _ HYP]. intros.
      dependent destruction REL1.
      - rewrite <-x. econstructor. intros.
        destruct (REL0 v). destruct (REL1 v). pclearbot. 
        eexists (wfo_add _ _).
        right. econstructor; eauto with wfo_refl.
      - rewrite <-x1. econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x in REL1.
        eapply HYP; eauto. eauto with wfo.
      - econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x, x1 in REL1.
        eapply HYP; eauto. eauto with wfo.
    }
    (* [Stutter] t1 = t0 *)
    { rewrite <-x0. unfold_eta. econstructor; eauto; cycle 1.
      { instantiate (1:= o'0). eauto with wfo wfo_proj. }
      punfold REL1. red in REL1. rewrite x in REL1. left. pstep. red.
      revert REL1. clear x0. revert t0.
      assert (WF := wfo_wf _ o'0). induction WF as [ord _ HYP]. intros.
      dependent destruction REL1.
      - rewrite <-x. econstructor. intros.
        destruct (REL0 v). destruct (REL1 v). pclearbot. 
        eexists (wfo_add _ _).
        right. econstructor; eauto with wfo_refl.
      - rewrite <-x1. econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x in REL1.
        eapply HYP; eauto. eauto with wfo.
      - econstructor; eauto. left. pstep.
        pclearbot. punfold REL1. red in REL1. rewrite x, x1 in REL1.
        eapply HYP; eauto. eauto with wfo.
    }
  }
  
  (* [Tau] t1' = Tau m1, t2 = Tau m2 *)
  { inversion EQVl; subst; eauto; pclearbot.
    (* [Tau] t1 = Tau m0 *)
    { econstructor; eauto 7 with wfo.
    }
    (* [TauL] t1 = Tau t0 *)
    { destruct bL; inv CHECK.
      hexploit eqiti_inv_tauR.
      { pstep. rewrite <-H3. punfold REL1. }
      { eauto. }
      intros RELt0m1.
      econstructor.
      - right. econstructor; eauto with wfo_refl.
      - eauto with wfo.
    }
    (* [TauR] t1 = Tau t0 *)
    { econstructor; eauto.
      - right. econstructor; eauto using wfo_le_refl.
      - eauto 8 with wfo.
    }
    (* [Stutter] t1 = Tau t0 *)
    { destruct bL, bR; inv CHECK1; inv CHECK2.
      unfold_eta. eapply EqNone; eauto with wfo.
      punfold REL1. red in REL1. rewrite H3 in REL1. left. pstep. red.
      remember (wfo_add o'1 o'0) as ord. clear H2. revert o'1 t0 LTo REL1 Heqord.
      assert (WF := wfo_wf _ ord). induction WF as [ord _ HYP]. intros.
      dependent destruction REL1; pclearbot.
      - rewrite <-x. econstructor.
        + right. econstructor; eauto with wfo_refl.
        + subst. eauto with wfo.
      - rewrite <-x0. econstructor.
        right. econstructor; try apply REL0; eauto with wfo_refl.
        + eapply eqiti_inv_tauR; eauto.
          pstep. red. rewrite <-x. punfold REL1.
        + subst. eauto with wfo_refl.
      - rewrite <-x. econstructor; eauto.
        + right. econstructor; eauto with wfo_refl.
        + subst. eauto with wfo.
      - rewrite <-x0. eapply EqNone; eauto.
        + left. pstep. punfold REL1. red in REL1. rewrite x in REL1.
          eapply HYP; try apply REL1; subst; eauto; eauto with wfo.
        + subst. eauto with wfo.
    }
  }
  
  (* [TauL] t1' = Tau t0, t2 = t3 *)
  { inversion EQVl; subst; eauto; pclearbot.
    (* [Tau] t1 = Tau m1 *)
    { econstructor; eauto.
      + right. econstructor; eauto with wfo_refl.
      + eauto with wfo.
    }
    (* [TauL] t1 = Tau t4 *)
    { destruct bL; inv CHECK.
      hexploit eqiti_inv_tauR.
      { pstep. rewrite <-H3. punfold REL1. }
      { eauto. }
      intros RELt0m1.
      econstructor; eauto.
      - right. econstructor; eauto with wfo_refl.
      - eauto with wfo.
    }
    (* [TauR] t1 = t4 *)
    { econstructor; eauto.
      - right. econstructor; eauto using wfo_le_refl.
      - eauto 8 with wfo.
    }
    (* [Stutter] t1 = t4 *)
    { destruct bL, bR; inv CHECK1; inv CHECK2.
      eapply EqNone; eauto.
      - right. econstructor; cycle 1; eauto with wfo_refl.
        eapply eqiti_inv_tauR; eauto.
        rewrite <-H3. pstep. punfold REL1.
      - eauto with wfo.
    }
  }

  (* [TauR] t1' = t0, t2 = Tau t3 *)
  { econstructor; eauto 7 with wfo wfo_refl.
  }
  
  (* [Stutter] ... *)
  { econstructor; eauto 7 with wfo wfo_refl.
  }
Qed.

Lemma eqit_transR_clo_prespectful {E} bL bR:
  prespectful6 (@eqit_ E bL bR) (@eqit_transR_clo E bR bL).
Proof.
  econstructor.
  { repeat intro; eapply eqit_transR_clo_monotone; eauto using wfo_le_refl. }

  intros ? ? ? ? R1 R2 RR o t1 t2 CLO.
  apply eqiti_r_flip.
  eapply paco6_mon.
  - eapply eqit_transL_clo_prespectful.
    + instantiate (1:= eqit_rel_flip r).
      instantiate (1:= eqit_rel_flip l).
      unfold eqit_rel_flip. eauto.
    + unfold eqit_rel_flip. intros.
      apply GF in PR. eauto using eqitF_flip.
    + destruct CLO. econstructor; eauto.
      * instantiate (1:= flip R1R2'). eauto.
      * eauto.
  - unfold eqit_rel_flip.
    intros. destruct PR; eauto.
    right. destruct H. econstructor; eauto.
Qed.

Lemma eqit_clo_transL E bL bR:
  @eqit_transL_clo E bL bR <7= gupaco6 (eqit_ bL bR) (cpn6 (eqit_ bL bR)).
Proof.
  intros. eapply prespect6_uclo; eauto using eqit_transL_clo_prespectful with paco.
Qed.

Lemma eqit_clo_transR E bL bR:
  @eqit_transR_clo E bR bL <7= gupaco6 (eqit_ bL bR) (cpn6 (eqit_ bL bR)).
Proof.
  intros. eapply prespect6_uclo; eauto using eqit_transR_clo_prespectful with paco.
Qed.

Arguments eqit_clo_transL : clear implicits.
Arguments eqit_clo_transR : clear implicits.

(** *** Bind properties *)

Lemma eutt_clo_bind {E U1 U2 UU R1 R2 RR} t1 t2 k1 k2
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> @eutt E R1 R2 RR (k1 u1) (k2 u2)):
  eutt RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  intros. destruct (eqit_lower_order EQT) as [so EQTso].
  eexists. ginit. guclo eqit_clo_bind.
  econstructor; eauto using wfo_le_refl with paco.
  intros. destruct (eqit_lower_order (EQK _ _ H)) as [so' RELso'].
  gfinal. right.
  eapply eqiti_mon; eauto using wfo_lt_le, (euttOrd_small 0).
Qed.

(** *** Transitivity properties *)

Lemma eqiti_trans {E} b1 b2 {R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) (RR: R1->R3->Prop) o1 o2 o t1 t2 t3
      (INL: eqiti b1 b2 RR1 o1 t1 t2)
      (INR: eqiti b1 b2 RR2 o2 t2 t3)
      (LEo: wfo_le (wfo_add o1 o2) o)
      (RRComp: forall x y z, RR1 x y -> RR2 y z -> RR x z)
  : @eqiti E b1 b2 _ _ RR o t1 t3.
Proof.
  ginit.
  guclo eqit_clo_transR. econstructor.
  - eapply eqiti_flip. instantiate (3:= flip RR2). eauto.
  - gfinal. eauto.
  - eauto.
  - eauto.
Qed.

Lemma eqit_trans {E} b1 b2 {R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) (RR: R1->R3->Prop) t1 t2 t3
      (INL: eqit b1 b2 RR1 t1 t2)
      (INR: eqit b1 b2 RR2 t2 t3)
      (RRComp: forall x y z, RR1 x y -> RR2 y z -> RR x z)
  : @eqit E b1 b2 _ _ RR t1 t3.
Proof.
  destruct INL, INR. eexists.
  eapply eqiti_trans; eauto with wfo_refl.
Qed.

Lemma eutt_trans {E} {R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) (RR: R1->R3->Prop) t1 t2 t3
      (INL: eutt RR1 t1 t2)
      (INR: eutt RR2 t2 t3)
      (RRComp: forall x y z, RR1 x y -> RR2 y z -> RR x z)
  : @eutt E _ _ RR t1 t3.
Proof.
  destruct INL, INR. eexists.
  eapply eqiti_trans; eauto with wfo_refl.
Qed.

Global Instance Transitive_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E b1 b2 _ _ RR).
Proof.
  red; intros. eapply eqit_mon; [eapply eqit_trans|..]; eauto.
Qed.

Global Instance Transitive_eqit_eq {E : Type -> Type} {R: Type} (b1 b2: bool):
  Transitive (@eqit E b1 b2 R R eq).
Proof.
  apply Transitive_eqit. repeat intro; subst; eauto.
Qed.

Global Instance Equivalence_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b: bool):
  Equivalence RR -> Equivalence (@eqit E b b R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance Equivalence_eqit_eq {E : Type -> Type} {R: Type} (b: bool):
  Equivalence (@eqit E false false R R eq).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance Transitive_eutt {E R RR} : Transitive RR -> Transitive (@eutt E R R RR).
Proof.
  red; intros. eapply eqit_mon; [eapply eqit_trans|..]; eauto.
Qed.

Global Instance Equivalence_eutt {E R RR} : Equivalence RR -> Equivalence (@eutt E R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance geuttgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2 r rg o
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco6 (@eqit_ E b1 b2) (cpn6 (eqit_ b1 b2)) r rg R1 R2 RS o).
Proof.
  repeat intro.
  guclo eqit_clo_transL. econstructor; eauto using eq_itree_zero, wfo_add_zero_r_le.
  guclo eqit_clo_transR. econstructor; eauto using eq_itree_zero, wfo_add_zero_r_le.
Qed.

Global Instance geuttgen_cong_eqit_eq {E R1 R2 RS} b1 b2 r rg o:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco6 (@eqit_ E b1 b2) (cpn6 (eqit_ b1 b2)) r rg R1 R2 RS o).
Proof.
  eapply geuttgen_cong_eqit; intros; subst; eauto.
Qed.

(*
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
         (gpaco2 (@eqit_ E true true R1 R2 RS id) (eqitC RS true true) r rg).
Proof.
  eapply geutt_cong_euttge; intros; subst; eauto.
Qed.
*)

Global Instance eqitgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit E b1 b2 R1 R2 RS).
Proof.
  repeat intro. destruct H1. eexists.
  ginit. eapply geuttgen_cong_eqit; eauto. gfinal. eauto.
Qed.

Global Instance eqitgen_cong_eqit_eq {E R1 R2 RS} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  repeat intro. destruct H1. eexists.
  ginit. intros. rewrite H, H0. gfinal. eauto.
Qed.

Global Instance euttge_cong_euttge {E R RS}
       (TRANS: Transitive RS):
  Proper (euttge RS ==> flip (euttge RS) ==> flip impl)
         (@eqit E true false R R RS).
Proof.
  repeat intro. do 2 (eapply eqit_mon; [eapply eqit_trans|..]; eauto).
Qed.

Global Instance euttge_cong_euttge_eq {E R}:
  Proper (euttge eq ==> flip (euttge eq) ==> flip impl)
         (@eqit E true false R R eq).
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
  eexists. ginit. gstep.
  constructor.
  intros; eexists. rewrite bind_ret_l.
  gfinal. right. eapply Reflexive_eqiti; eauto.
Grab Existential Variables. exact wfo_zero. exact wfo_zero.
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

(* Ltac auto_ctrans := *)
(*   intros; repeat (match goal with [H: rcompose _ _ _ _ |- _] => destruct H end); subst; eauto. *)
(* Ltac auto_ctrans_eq := try instantiate (1:=eq); auto_ctrans. *)

(** [eqit] is a congruence for [itree] constructors. *)

Lemma eutt_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≈ Tau t2 <-> t1 ≈ t2.
Proof.
  apply eqit_tau.
Qed.

Lemma eqitree_Tau {E R} (t1 t2 : itree E R):
  Tau t1 ≅ Tau t2 <-> t1 ≅ t2.
Proof.
  apply eqit_tau.
Qed.

(* Specialization of [eutt_clo_bind] to the recurrent case where [UU := eq]
   in order to avoid having to provide the relation manually everytime *)
Lemma eutt_eq_bind : forall E R U (t: itree E U) (k1 k2: U -> itree E R), (forall u, k1 u ≈ k2 u) -> ITree.bind t k1 ≈ ITree.bind t k2.
Proof.
  intros. eapply eutt_clo_bind; [reflexivity|].
  intros; subst. eauto.
Qed.

Lemma eqit_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit b1 b2 RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit b1 b2 RS (k1 r1) (k2 r2)) ->
  @eqit E b1 b2 _ _ RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. eexists.
  ginit. guclo eqit_clo_bind.
  eapply eqit_bind_split; intros; eauto with wfo_refl.
  - gfinal. right. destruct (eqit_lower_order H).
    eapply eqiti_mon; eauto using wfo_lt_le, euttOrd_small.
  - gfinal. right. destruct (eqit_lower_order (H0 _ _ H1)).
    eapply eqiti_mon; eauto using wfo_lt_le, euttOrd_small.
Grab Existential Variables. exact 0. exact 0.
Qed.

Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eq_itree E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)):
  eq_itree RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof.
  eapply eqit_bind'; eauto.
Qed.

Global Instance eqit_bind {E R S} b1 b2 :
  Proper (pointwise_relation _ (eqit b1 b2 eq) ==>
          eqit b1 b2 eq ==>
          eqit b1 b2 eq) (@ITree.bind' E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

Global Instance eqit_bind_ {E R S} b1 b2 k :
  Proper (going (eqit b1 b2 eq) ==>
          eqit b1 b2 eq) (@ITree._bind E R S k (@ITree.bind' E R S k)).
Proof.
  eexists. ginit. destruct H.
  rewrite (itree_eta' x), (itree_eta' y), <- !unfold_bind.
  guclo eqit_clo_bind. econstructor; eauto with wfo_refl; intros.
  - gfinal. right. destruct (eqit_lower_order e).
    eapply eqiti_mon; eauto using wfo_lt_le, euttOrd_small.
  - subst. apply reflexivity.
Grab Existential Variables. exact 0. exact wfo_zero.
Qed.

Lemma eqit_map {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      f1 f2 t1 t2 :
  (forall r1 r2, RR r1 r2 -> RS (f1 r1) (f2 r2)) ->
  @eqit E b1 b2 _ _ RR t1 t2 ->
  eqit b1 b2 RS (ITree.map f1 t1) (ITree.map f2 t2).
Proof.
  unfold ITree.map; intros.
  eapply eqit_bind'; eauto.
  intros. eexists wfo_zero. pstep. econstructor. eauto.
Qed.

Global Instance eqit_eq_map {E R S} b1 b2 :
  Proper (pointwise_relation _ eq ==>
          eqit b1 b2 eq ==>
          eqit b1 b2 eq) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  eexists wfo_zero. revert R s.
  ginit. gcofix CIH. intros.
  rewrite !unfold_bind. gstep. repeat red.
  genobs s os. destruct os; simpl; eauto using wfo_non_negative with paco.
Qed.

Lemma bind_ret_r' {E R} (u : itree E R) (f : R -> R) :
  (forall x, f x = x) ->
  (r <- u ;; Ret (f r)) ≅ u.
Proof.
  intro H. rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - hnf. intros. apply eqit_ret. auto.
  - reflexivity.
Qed.

----------------- Revised Up Here ------------------

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
      apply eqit_ret; auto.
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
      rewrite <- H0. apply eqit_vis.
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
      rewrite <- H0. apply eqit_tau. pclearbot. auto.
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
        apply eqit_tauL in H2. rewrite <- eqit_tau. auto.
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

