
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
From Stdlib Require Import
     Structures.Orders (* Hint Unfold is_true *)
     Program
     Setoid
     Morphisms
     Relations.

From Coinduction Require Import all.

(* important: Basics.Utils must come after Coinduction, as it 
re-implements several tactics. *)
From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.Paco2
     Eq.Shallow.


Local Open Scope itree_scope.
(* end hide *)

(* RTODO: remove these notes. they will be useful for now.

------------------------------------------------------------


The paco proofs, in large, rely on induction on eqitF in a hypothesis. they
derive this eqitF from eqit in a hypothesis, as eqit is defined as paco2 (eqit_)
(where eqit_ is defined by eqitF). using punfold, they transform 
eqit into eqitF b1 b2 vclo (upaco2 ...). 

In these same proofs using `coinduction`, we have an eqit in the hypothesis, 
but now it is defined as the gfp of eqit_. Since `coinduction` subsumes 
`paco`, we should be able to derive the same transformation as in `punfold`, 
but we need to find out how. This likely involves building a tactic that 
turns gfp b into b(gfp b). 

Having found this (gfp_fp), we want to build a rich tactic library, a la Ctrees, 
to work with step, step_in, and friends. This will allows us to do proofs 
that look like paco but do not require wcompat and are ammenable to 
enhanced relational properties.  

*)

(** ** Coinductive reasoning with Paco *)
(* RTODO: REWRITE THIS WITH POUS COINDUCTION *)

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

(* We coerce [b1] and [b2] in [eqitF] (below) from [bool] to [Prop]. This makes
it slightly easier to write and automate mechanized proofs about [eqit]: we have
hypotheses of simply [b1] rather than [b1 = true]. *)


Local Coercion is_true : bool >-> Sortclass.

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

  Inductive eqitF (b1 b2: bool) (sim : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqitF b1 b2 sim (RetF r1) (RetF r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqitF b1 b2 sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, sim (k1 v) (k2 v) : Prop):
      eqitF b1 b2 sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
        (CHECK: b1)
        (REL: eqitF b1 b2 sim (observe t1) ot2):
      eqitF b1 b2 sim (TauF t1) ot2
  | EqTauR ot1 t2
        (CHECK: b2)
        (REL: eqitF b1 b2 sim ot1 (observe t2)):
      eqitF b1 b2 sim ot1 (TauF t2)
  .
  Hint Constructors eqitF : itree.

  Definition eqit_ b1 b2 sim :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 sim (observe t1) (observe t2).
  Hint Unfold eqit_ : itree.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono b1 b2 : Proper (leq ==> leq) (eqit_ b1 b2).
  Proof.
    intros sim sim' Hsim x0 x1.
    unfold eqit_. intros IN.
    induction IN; constructor; auto.
    - apply Hsim; auto.
    - intros ?; apply Hsim; auto.
  Qed.

  Definition eqit_mon b1 b2 : mon (itree E R1 -> itree E R2 -> Prop) :=
    {| body := eqit_ b1 b2 ; Hbody := eqitF_mono b1 b2 |}.

  Definition eqit b1 b2 : itree E R1 -> itree E R2 -> Prop :=
    gfp (eqit_mon b1 b2).
  (** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. *)

  Definition eq_itree := eqit false false.

  Definition eutt := eqit true true.

  Definition euttge := eqit true false.

End eqit.

(* begin hide *)
#[global] Hint Constructors eqitF : itree.
#[global] Hint Unfold eqit_ : itree.
#[global] Hint Unfold eqit : itree.
#[global] Hint Unfold eq_itree : itree.
#[global] Hint Unfold eutt : itree.
#[global] Hint Unfold euttge : itree.

#[global]
Tactic Notation "coinduction"
  simple_intropattern(R)
  simple_intropattern(H) :=
  first
    [ coinduction R H
    | unfold eqit at -1; coinduction R H
    | unfold eqit; coinduction R H
    ].

Ltac down_ H :=
  repeat progress (
    cbn [eqit_mon body] in H;
    unfold eqit_ in H
  ).

Ltac down_goal :=
  repeat progress (
    cbn [eqit_mon body];
    unfold eqit_
  ).

Ltac down :=
  repeat progress (
    cbn [eqit_mon body] in *;
    unfold eqit_ in *
  ).

Tactic Notation "down" "in" hyp(H) := down_ H.
Tactic Notation "down" "in" "goal" := down_goal.

Ltac solve_eqitF := 
match goal with 
| [h1: _ = observe _ , h2: _ = observe _ |- _] => 
(* reduce to 'observe' form by stripping constructors and unfolding *)
try econstructor; down; 
(* replace 'observe' with actual constructor values *)
rewrite <- h1; rewrite <- h2; 
(* finish off *)
econstructor; eauto with itree 
end. 

Ltac taul := apply EqTauL; only 1: auto. 
Ltac taur := apply EqTauR; only 1: auto. 

(* Tour 1: *)
(* RTODO: rewrite with paco transformers. *)

Ltac pstep := step. 
Ltac pstep_reverse := backstep. 
Ltac pfold := step. 
Ltac punfold H := step in H.
Ltac paco2_fold := step.  
Ltac pclearbot := idtac. 

Lemma eqitF_inv_VisF_r {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    t1 X2 (e2 : E X2) (k2 : X2 -> _)
  : eqitF RR b1 b2 sim t1 (VisF e2 k2) ->
    (exists k1, t1 = VisF e2 k1 /\ forall v, sim (k1 v) (k2 v)) \/
    (b1 /\ exists t1', t1 = TauF t1' /\ eqitF RR b1 b2 sim (observe t1') (VisF e2 k2)).
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ _ t2 return
      match t2 return Prop with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - left; eauto.
  - destruct i0; eauto.
Qed.

Lemma eqitF_inv_VisF_weak {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    X1 (e1 : E X1) (k1 : X1 -> _) X2 (e2 : E X2) (k2 : X2 -> _)
  : eqitF RR b1 b2 sim (VisF e1 k1) (VisF e2 k2) ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ pweqeq sim p k1 k2.
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ t1 t2 return
      match t1, t2 return Prop with
      | VisF e1 k1, VisF e2 k2 => _
      | _, _ => True
      end with
    | EqVis _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - exists eq_refl; cbn; eauto.
  - destruct i; exact I.
Qed.

Lemma eqitF_inv_VisF {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 sim}
    X (e : E X) (k1 : X -> _) (k2 : X -> _)
  : eqitF RR b1 b2 sim (VisF e k1) (VisF e k2) ->
    forall x, sim (k1 x) (k2 x).
Proof.
  intros H. dependent destruction H. assumption.
Qed.

Lemma eqitF_VisF_gen {E R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 sim}
    {X1 X2} (p : X1 = X2) (e1 : E X1) (k1 : X1 -> _) (e2 : E X2) (k2 : X2 -> _)
  : eqeq E p e1 e2 -> pweqeq sim p k1 k2 ->
    eqitF RR b1 b2 sim (VisF e1 k1) (VisF e2 k2).
Proof.
  destruct p; intros <-; cbn; constructor; auto.
Qed.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ |- _ ] => red in H end).

#[global] Instance eqitF_Proper_R {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq_rel ==> eq_rel)
    (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; unfold subrelationH; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
    econstructor. apply H2. assumption.
    econstructor. intros. specialize (REL v). apply H2. auto.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
    econstructor. apply H2. assumption.
    econstructor. intros. specialize (REL v). apply H2. auto.
Qed.

#[global] Instance eqitF_Proper_R2 {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
Qed.

(* #[global] Instance eqitF_Proper_observe_l {E : Type -> Type} {R:Type} 
(sim : itree E R -> itree E R -> Prop)
:
  Proper (eq ==> eq ==> eq ==> sim ==> sim ==> iff)
          (fun RR b1 b2 t1 t2 => @eqitF E R R RR b1 b2 sim (observe t1) (observe t2)).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H; auto with itree.

    econstructor. apply H. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
Qed. *)

#[global] Instance eqitF_Proper_observe_l {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
          (fun RR b1 b2 sim t1 t2 => @eqitF E R1 R2 RR b1 b2 sim (observe t1) t2).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
Qed.
(* 
Lemma eqitF_observe_l_sim
{E : Type -> Type} {R: Type} (RR : R -> R -> Prop)
  b1 b2
  (sim : itree E R -> itree E R -> Prop)
  t1 t2 z :
  sim t1 t2 ->
  eqitF RR b1 b2 sim (observe t1) z ->
  eqitF RR b1 b2 sim (observe t2) z.
Proof.
  intros. 
  (* remember (observe t2) as t2'. *)
  dependent induction H0.  *)

  


#[global] Instance eqitF_Proper_observe_r {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
          (fun RR b1 b2 sim t1 t2 => @eqitF E R1 R2 RR b1 b2 sim t1 (observe t2)).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
Qed.

#[global] Instance eqitF_Proper_observe {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
          (fun RR b1 b2 sim t1 t2 => @eqitF E R1 R2 RR b1 b2 sim (observe t1) (observe t2)).
Proof.
  repeat red; intros; subst; eapply eqitF_Proper_observe_r; eauto. 
Qed.

#[global] Instance eqit_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> iff) (@eqit E R1 R2).
Proof with auto with itree.
  repeat red.
  intros. subst.
  split.
  (* assert forall, pull out vars *)
  - revert_until y1. coinduction R CIH. intros.  
  cbn; red. red in H0. step in H0. 
  hinduction H0 before CIH... 
  econstructor. now apply H. 
  - revert_until y1. coinduction R CIH. intros.  
  cbn; red. step in H0. 
  hinduction H0 before CIH... 
  econstructor; now apply H. 
Qed. 

#[global] Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  unfold eutt. repeat red.
  intros. split; intros; subst.
  - rewrite <- H. assumption.
  - rewrite H. assumption.
Qed.

(* proofs go this way. *)
Lemma eqit_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2:
  forall (u : itree E R1) (v : itree E R2),
    eqit (flip RR) b2 b1 v u -> eqit RR b1 b2 u v.
Proof.
  (* set up for coinduction. *)
  unfold eqit at -1. 
  (* do coinduction. *)
  coinduction c CIH. intros u v euv. 
  (* reduce the hypothesis and conclusion to the right form. *)
  step in euv. cbn in *. red in euv |- *.
  (* do induction and conclude trivially with constructors. *)
  induction euv; eauto with itree.
Qed.

Lemma eqit_mono {E R1 R2} RR RR' (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <= RR'):
  @eqit E R1 R2 RR b1 b2 <= eqit RR' b1' b2'.
Proof.
  unfold eqit at -1. repeat intro. 
  revert a a0 H. 
  coinduction c CIH; intros.  
  punfold H. down. induction H; pclearbot; eauto with itree.
  econstructor. now apply LERR.  
Qed.


Lemma eqitF_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 r:
  flip (eqitF (flip RR) b2 b1 (flip r)) <= @eqitF E R1 R2 RR b1 b2 r.
Proof.
  repeat intro; induction H; eauto with itree.
Qed.




#[global] Hint Unfold flip : itree.


(* end hide *)

(** A notation of [eq_itree eq]. You can write 

[≅] using [[\cong]]
[≈] using [[\approx]]
[≳] using [[\gtrsim]]
in tex-mode *)

Infix "≅" := (eq_itree eq) (at level 70) : type_scope.

Infix "≈" := (eutt eq) (at level 70) : type_scope.

Infix "≳" := (euttge eq) (at level 70) : type_scope.


(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).

#[global] Instance Reflexive_eqitF b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqitF RR b1 b2 sim).
Proof.
  red. destruct x; constructor; eauto with itree.
Qed.

#[global] Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqitF RR b b sim).
Proof.
  red. induction 3; constructor; subst; eauto.
Qed.



(* weak: eqitF is transitive under strong bisimilarity assumptions *)
#[global] Instance Transitive_eqitF_eqit (sim : itree E R -> itree E R -> Prop)
: Transitive RR -> Transitive sim -> Transitive (eqitF RR false false sim).
Proof.
  red. intros. revert H2. revert z. induction H1. 
  - intros. dependent induction H2; subst. 
    + econstructor. etransitivity; eauto. 
    + taur.
      eapply IHeqitF; eauto. 
  - intros. 
    dependent induction H2; subst.  
    + econstructor; etransitivity; eauto. 
    (* impossible: eqitF RR false false sim (observe m2) z 
       because one boolean must be true for this assumption to hold.
    *)
    + easy. 
    + taur. eapply IHeqitF; eauto. 
  - intros. 
    dependent induction H2. 
    + econstructor.
      etransitivity; eauto. 
    + taur. 
      eapply IHeqitF; eauto. 
  - intros. taul. apply IHeqitF, H2.  
  - intros. apply IHeqitF.
     (* see above note on why this is impossible *)
    easy. 
Qed. 

(* Tour extra: *)
(* RTODO: ask yannick exactly what's going on, then document *)
  (* 
  "eutt is NOT valid up to eutt" and this is supposedly equivalent to 
  transitivity, but we did prove things are transitive... what's going on?
  *)

  (* eutt is still transitive, but for different reasons *)
  
(* check out line 796 in orig file *)

(* strongest: holds for all instances of eqit *)
#[global] Instance Reflexive_eqit_ b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqit_ RR b1 b2 sim).
Proof. repeat red. intros. reflexivity. Qed.

(* weak: holds only with eqit or eutt *)
#[global] Instance Symmetric_eqit_ b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqit_ RR b b sim).
Proof. repeat red; symmetry; auto. Qed.

(* weak: holds only for strong bisimilarity *)
#[global] Instance Transitive_eqit_eqit (sim : itree E R -> itree E R -> Prop)
: Transitive RR -> Transitive sim -> Transitive (eqit_ RR false false sim).
Proof. repeat red; etransitivity; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. unfold eqit. 
  (* strengthen bisimulation: elem c x x holds for all x.  *)
  revert x. coinduction c CIH. intro. step.
  now repeat apply Reflexive_eqit_.
Qed.


#[global] Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E _ _ RR b b).
Proof.
  intros.
  (* Yannick: why unfold only at 2? gfp in assumption causes problems or? *)
  unfold Symmetric. unfold eqit at 2.  
  (* generally poor error message: wants a fix. *)
  coinduction c CIH. 
  assert (Symmetric (elem c)). 
  { apply Symmetric_chain. red; intros.
  now apply Symmetric_eqit_. 
  }
  
  intros.
  apply Symmetric_eqit_; auto.
  unfold eqit_. 
  step in H1.
  induction H1; eauto with itree.  
Qed. 


#[global] Instance eq_sub_euttge:
  subrelation (@eq_itree E _ _ RR) (euttge RR).
Proof.
  red. 
  unfold euttge, eqit. 
  coinduction c CIH. intros.  
  step in H. 
  step; down. 
  (* these proofs get to do hinduction. *)
  hinduction H before CIH; subst; eauto with itree. 
  - step in REL.
    cbn in REL. down. 
    dependent induction REL; solve_eqitF.  
  - econstructor. 
    intro. specialize (REL v). step in REL. 
    cbn in REL; down.
    dependent induction REL; solve_eqitF.     
Qed.

#[global] Instance euttge_sub_eutt:
  subrelation (@euttge E _ _ RR) (eutt RR).
Proof.
  unfold subrelation, eutt, eqit.
  coinduction c CIH. 
  intros. step. 
  unfold euttge, eqit in H; down; step in H. 
  hinduction H before CIH; subst; eauto with itree.
  - step in REL; cbn in REL; down. 
    econstructor. 
    dependent induction REL; try solve_eqitF.  
      down. 
      rewrite <- x. taul. 
      apply IHREL; eauto.  
  - econstructor. intros.  
    specialize (REL v). step in REL. 
    cbn in REL; down. 
    (* key step: IH must work for ANY tree, not just a continuation-built one. *)
    (* this is so we can strip a Tau off the left side and still use our IH. *)
    remember (k1 v).
    dependent induction REL; try solve_eqitF. 
    + rewrite <- x. taul. eapply IHREL; eauto. 
Qed. 

#[global] Instance eq_sub_eutt:
  subrelation (@eq_itree E _ _ RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. apply H.
Qed.

End eqit_gen.

#[global] Hint Resolve Reflexive_eqit : reflexivity.

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (@eqit E R R eq).

#[global] Instance Reflexive_eqitF_eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq b1 b2 sim).
Proof.
  apply Reflexive_eqitF; eauto.
Qed.

#[global] Instance Symmetric_eqitF_eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b sim).
Proof.
  apply Symmetric_eqitF; eauto. 
Qed.

#[global] Instance Reflexive_eqit__eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqit_ eq b1 b2 sim).
Proof. apply Reflexive_eqit_; eauto. Qed.

#[global] Instance Symmetric_eqit__eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqit_ eq b b sim).
Proof. apply Symmetric_eqit_; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit_eq b1 b2 : Reflexive (eqit b1 b2).
Proof.
  apply Reflexive_eqit; eauto.
Qed.

#[global] Instance Symmetric_eqit_eq b : Symmetric (eqit b b).
Proof.
  apply Symmetric_eqit; eauto.
Qed.

(** *** Congruence properties *)
Hint Extern 1 => step : itree. 
#[global] Instance eqit_observe b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@observe E R).
Proof.
  constructor; step in H; auto with itree.  
Qed. 

#[global] Instance eqit_tauF b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@TauF E R _).
Proof.
  constructor; step. econstructor. eauto.
Qed.

#[global] Instance eqit_VisF b1 b2 {u} (e: E u) :
  Proper (pointwise_relation _ (eqit b1 b2) ==> going (eqit b1 b2)) (VisF e).
Proof.
  constructor; red in H. unfold eqit in *. pstep; econstructor; auto with itree.
Qed.

#[global] Instance observing_sub_eqit l r :
  subrelation (observing eq) (eqit l r).
Proof.
  repeat red; intros.
  pstep. cbn. unfold eqit_. rewrite (observing_observe H). apply Reflexive_eqitF; eauto.
Qed.

#[global] Instance observing_sub_elem (c : Chain (eqit_mon eq false false)) (l r : itree E R) :
  subrelation (@observing E R R eq) (elem c).
Proof.
  repeat intro.
  inv H. step. down. rewrite observing_observe. 
  apply (gfp_bchain c). reflexivity. 
Qed.

(* Add Parametric Morphism (c : Chain (eqit_mon eq false false)) : 
  (@eqit_mon E R R eq false false (elem c))
  with signature (@eq_itree E R R eq ==> eq_itree eq ==> flip impl)
  as elem_eq_itree_proper. 
Proof. 
  red; intros.
  step in H. step in H0.
  down. genobs x otx. genobs x0 otx0.  
  dependent induction H1.
  - simpobs. inv H; inv H0; try easy. now constructor. 
  - simpobs. inv H; inv H0; try easy. constructor. 
    apply observing_sub_elem; eauto. Search elem.   *)

(** ** Eta-expansion *)

Lemma itree_eta_ (t : itree E R) : t ≅ go (_observe t).
Proof. apply observing_sub_eqit. econstructor. reflexivity. Qed.

Lemma itree_eta (t : itree E R) : t ≅ go (observe t).
Proof. apply itree_eta_. Qed.

Lemma itree_eta' (ot : itree' E R) : ot = observe (go ot).
Proof. reflexivity. Qed.

End eqit_eq.

(** *** One-sided inversion *)

Lemma eqitree_inv_Ret_r {E R} (t : itree E R) r :
  t ≅ (Ret r) -> observe t = RetF r.
Proof.
  intros; punfold H; inv H; try inv CHECK; eauto.
Qed.

Lemma eqitree_inv_Vis_r {E R U} (t : itree E R) (e : E U) (k : U -> _) :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ forall u, k' u ≅ k u.
Proof.
  intros; punfold H; apply eqitF_inv_VisF_r in H.
  destruct H as [ [? [-> ?]] | [] ]; [ | discriminate ].
  pclearbot. eexists; split; eauto.
Qed.

Lemma eqitree_inv_Tau_r {E R} (t t' : itree E R) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
Qed.

Lemma eqit_inv_Ret {E R1 R2 RR} b1 b2 r1 r2 :
  @eqit E R1 R2 RR b1 b2 (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

(* Axiom-free, weaker version of [eqit_inv_vis] *)
Lemma eqit_inv_Vis_weak {E R1 R2 RR} b1 b2
  {u1 u2} (e1 : E u1) (e2 : E u2) (k1: u1 -> itree E R1) (k2: u2 -> itree E R2) :
  eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2) ->
  exists p, eqeq E p e1 e2 /\ pweqeq (eqit RR b1 b2) p k1 k2.
Proof.
  intros. punfold H; apply eqitF_inv_VisF_weak in H.
  destruct H as [ p []]. exists p; split; auto.
Qed.

(* This assumes UIP. *)
Lemma eqit_inv_Vis {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 U (e : E U)
    (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : eqit RR b1 b2 (Vis e k1) (Vis e k2) ->
    forall u, eqit RR b1 b2 (k1 u) (k2 u).
Proof.
  intros H x; punfold H; apply eqitF_inv_VisF with (x := x) in H; pclearbot; auto.
Qed.

(* Tour 2: *)
(* This proof was quite simplified by tactics *)
Lemma eqit_inv_Tau_l {E R1 R2 RR} b1 t1 t2 :
  @eqit E R1 R2 RR b1 true (Tau t1) t2 -> eqit RR b1 true t1 t2.
Proof.
  intros.
  step in H. down. 
  (* RTODO: report this bug (rm down) *)
  dependent induction H. 
  - step in REL. step.
    down.
    simpobs. 
    taur. assumption. 
  - now step. 
  - step. down. simpobs. taur. 
    backstep. 
    now apply IHeqitF. 
Qed. 

Lemma eqit_inv_Tau_r {E R1 R2 RR} b2 t1 t2 :
  @eqit E R1 R2 RR true b2 t1 (Tau t2) -> eqit RR true b2 t1 t2.
Proof.
  intros.
  step in H. down. 
  dependent induction H. 
  - step.
    down.
    simpobs. 
    taul. 
    step in REL.
    assumption. 
  - step. down. simpobs. taul. 
    backstep. 
    now apply IHeqitF.
  - now step.  
Qed. 

(* this proof is much shorter and nicer than before. *)
Lemma eqit_inv_Tau {E R1 R2 RR} b1 b2 t1 t2 :
  @eqit E R1 R2 RR b1 b2 (Tau t1) (Tau t2) -> eqit RR b1 b2 t1 t2.
Proof with eauto with itree.
  intros.
  step in H; down. 
  dependent induction H. 
  - step. down. now step in REL.  
  - inv H; step; down; simpobs. 
    + taul. now step in REL.  
    + taul. backstep. now apply IHeqitF. 
    + assumption. 
  - inv H; step; down; simpobs. 
    + taur. now step in REL. 
    + assumption. 
    + taur. backstep. now apply IHeqitF. 
Qed.

Section eqit_inv.

Context {E : Type -> Type} {R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 : bool}.
Context {sim : itree E R1 -> itree E R2 -> Prop}.

Notation eqit__ t1_ t2_ :=
  match _observe t1_, _observe t2_ with
  | RetF r1, RetF r2 => RR r1 r2
  | VisF e1 k1, VisF e2 k2 =>
    exists p, eqeq E p e1 e2 /\ pweqeq (eqit RR b1 b2) p k1 k2
  | RetF _, VisF _ _ | VisF _ _, RetF _ => False
  | TauF t1, TauF t2 => eqit RR b1 b2 t1 t2
  | TauF t1, _ =>
    if b1 then eqit RR b1 b2 t1 t2_
    else False
  | _, TauF t2 =>
    if b2 then eqit RR b1 b2 t1_ t2
    else False
  end.


Lemma eqit_inv t1 t2 : eqit RR b1 b2 t1 t2 -> eqit__ t1 t2.
Proof.
  intros H; punfold H; down. 
  genobs t1 ot1; genobs t2 ot2. 
  inv H; unfold observe in *; simpobs; auto. 
  - exists eq_refl; cbn; eauto.
  - rewrite CHECK in *. 
    flatten_goal.  
    1,3: step; down; unfold observe; simpobs; assumption. 
    1: apply eqit_inv_Tau_r; now step.
  - rewrite CHECK in *. flatten_goal. 
    1,3: step; down; unfold observe; simpobs; assumption. 
    1: apply eqit_inv_Tau_l; now step.
Qed.

End eqit_inv.

Lemma eutt_inv_Ret {E R} r1 r2 :
  (Ret r1: itree E R) ≈ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_Ret; eauto.
Qed.

Lemma eqitree_inv_Ret {E R} r1 r2 :
  (Ret r1: itree E R) ≅ (Ret r2) -> r1 = r2.
Proof.
  intros; eapply eqit_inv_Ret; eauto.
Qed.

Lemma eqit_Tau_l {E R1 R2 RR} b2 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR true b2 t1 t2 -> eqit RR true b2 (Tau t1) t2.
Proof.
  intros. pstep. econstructor; eauto. punfold H. now down. 
Qed.

Lemma eqit_Tau_r {E R1 R2 RR} b1 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR b1 true t1 t2 -> eqit RR b1 true t1 (Tau t2).
Proof.
  intros. pstep. econstructor; eauto. punfold H. now down. 
Qed.

Lemma tau_euttge {E R} (t: itree E R) :
  Tau t ≳ t.
Proof.
  apply eqit_Tau_l. reflexivity.
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
#[global] Hint Constructors rcompose : itree.

Lemma trans_rcompose {R} RR (TRANS: Transitive RR):
  forall x y : R, rcompose RR RR x y -> RR x y.
Proof.
  intros. destruct H; eauto.
Qed.

(* core proof: transitivity of eqit *)
Lemma eqit_trans {E R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) b1 b2 t1 t2 t3
      (INL: eqit RR1 b1 b2 t1 t2)
      (INR: eqit RR2 b1 b2 t2 t3):
  @eqit E _ _ (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  unfold eqit. revert_until b2. 
  (* we'll need the coinductive reasoning later: elements of the chain 
  are transitive w.r.t. eqit. *)
  coinduction c CIH. intros. 
  punfold INL. punfold INR. down. genobs t3 ot3.
  (* we begin with induction on t1 ~ t2. 
  in each case, we perform induction on t2 ~ t3.  *)
  hinduction INL before CIH; intros; subst; clear t1 t2.
  (* Ret, straightforward *)
  - remember (RetF r2) as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with itree.
  - genobs t3 ot3. 
  (* need something more: t3 is either a τ node, or it isn't. *)
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }
    destruct DEC as [EQ | EQ].
    (* τ - τ case: strip both. *)
    + destruct EQ as [m3 ?]; subst; simpobs. 
      econstructor.
      eapply CIH; eauto.
      apply eqit_inv_Tau.
      now step.    
    (* τ - ̸τ : we do further case analysis. *)
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      taul. 
      pclearbot. punfold REL. down. 
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
    (* now we can handle each subcase with another layer of induction *)
      * remember (RetF r1) as ot.
        hinduction REL0 before CIH; intros; inv Heqot; eauto with paco itree.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
        econstructor. intros.
        apply (CIH _ _ _ (REL v) (REL0 v)). 
      * eapply IHREL0; eauto. pstep_reverse.
        destruct b1; inv CHECK0.
        apply eqit_inv_Tau_r. now step. 
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
    econstructor. intros.
    apply (CIH _ _ _ (REL0 v) (REL v)). 
  - eauto with itree.
  - remember (TauF t0) as ot.
    genobs t3 ot3. 
    hinduction INR before CIH; intros; try inversion Heqot; subst.
    + eapply IHINL.
      now instantiate (1:=(Tau m2)).
      pclearbot. punfold REL. eauto with itree.
    + now eapply IHINL.
    + taur. eapply IHINR; eauto. 
Qed.

#[global] Instance Transitive_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). 
  eapply eqit_mono, eqit_trans; eauto.
  repeat intro. now apply TRANS.
Qed.

#[global] Instance Transitive_eqit_eq {E : Type -> Type} {R: Type} (b1 b2: bool):
  Transitive (@eqit E R R eq b1 b2).
Proof.
  apply Transitive_eqit. repeat intro; subst; eauto.
Qed.

#[global] Instance Equivalence_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b: bool):
  Equivalence RR -> Equivalence (@eqit E R R RR b b).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Equivalence_eqit_eq {E : Type -> Type} {R: Type} (b: bool):
  Equivalence (@eqit E R R eq false false).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance Transitive_eutt {E R RR} : Transitive RR -> Transitive (@eutt E R R RR).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). eapply eqit_mono, eqit_trans; eauto.
  repeat intro. now apply TRANS. 
Qed.

#[global] Instance Equivalence_eutt {E R RR} : Equivalence RR -> Equivalence (@eutt E R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

(* #[global] Instance geuttgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2 
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit_ E R1 R2 RS b1 b2 (eqit RS b1 b2)).
Proof.
  repeat intro.
  eapply eqit_trans. 
  eapply eqit_mon. repeat intro.     
  guclo eqit_clo_trans. econstructor; cycle -3; eauto.
  - eapply eqit_mono, H; eauto; discriminate.
  - eapply eqit_mono, H0; eauto; discriminate.
Qed. *)

(* #[global] Instance geuttgen_cong_eqit_eq {E R1 R2 RS} b1 b2 r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  eapply geuttgen_cong_eqit; intros; subst; eauto.
Qed.

#[global] Instance geuttge_cong_euttge {E R1 R2 RR1 RR2 RS} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true false id) (eqitC RS true false) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. eauto with itree.
Qed.

#[global] Instance geuttge_cong_euttge_eq {E R1 R2 RS} r rg:
  Proper (euttge eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true false id) (eqitC RS true false) r rg).
Proof.
  eapply geuttge_cong_euttge; intros; subst; eauto.
Qed.

#[global] Instance geutt_cong_euttge {E R1 R2 RR1 RR2 RS} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. eauto with itree.
Qed.

#[global] Instance geutt_cong_euttge_eq {E R1 R2 RS} r rg:
  Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS true true id) (eqitC RS true true) r rg).
Proof.
  eapply geutt_cong_euttge; intros; subst; eauto.
Qed. *)

(* Tour extra 2: *)
(* RTODO: Ask ^ about above this one: are they important, or just 
  important for this one? If latter, they are not needed. *)


(* Tour 3: Show this proof. (Q): *)

(* Noe's note: add morphism *)
Add Parametric Morphism {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) : 
         (@eqit E R1 R2 RS b1 b2) 
         with signature (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         as eqitgen_cong_eqit. 
Proof. 
repeat intro; unfold flip, eq_itree in *. 

  (* Given *)
  (* LERR1: ∀ x x' y. RR1 x x' -> RS x' y -> RS x y *)
  (* LERR2: ∀ x y y'. RR2 y y' -> RS x y' -> RS x y, *)
  (* Prove the diagram commutes *)
  
  (* 
   y -(eqit RS b1 b2) → y0 
   ↑                    ↑
   ≅RR1                ≅RR2
   |                    | 
   x -(?eqit RS b1 b2)→ x0
  *)

  (* Problem: this diagram does not have a path from x to x0. *)
  (* Solution: flip ≅RR2, as both boolean flags are false to 
    begin with this is a "symmetry" on trees only. *)

(* 
   y -(eqit RS b1 b2) → y0 
   ↑                    |
   ≅RR1                ≅(flip RR2)
   |                    ↓ 
   x -(?eqit RS b1 b2)→ x0

(* This diagram has a clear path (lifting with eqit_mono), 
  and LERR1 and LERR2 get us the correlaries we need to arrive there: namely: *)
*)
(*  by LERR1, Ret nodes of x and Ret nodes of y0 are related by RS. 
    by LERR2, Ret nodes of x0 and Ret nodes of y are related by RS. 
    RR1 ∘ RS <= RS 
    (flip RR2) ∘ RS <= RS 
    so RS is closed under left composition by RR1
    and right composition by flip RR2.
  *)
  (* We use a mix of foreward and backward reasoning. *)
  
  idtac. 
  (* build arrows and strengthen *)
  assert (rcompose RR1 RS <= RS) by (intros ? ? [? ?]; eauto). 
  assert (rcompose RS (flip RR2) <= RS) by (intros ? ? [? ?]; eauto).
  assert (eqit RR1 b1 b2 x y) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR1); easy).
  assert (eqit RR2 b1 b2 x0 y0) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR2); try easy).  

  (* first diagonal *)
  specialize (eqit_trans _ _ _ _ _ _ _ H4 H1) as Hdiag_weak. 
  assert (eqit RS b1 b2 x y0) as Hdiag by 
  (eapply eqit_mono with (RR:=(rcompose RR1 RS)); eauto).
  
  (* reverse the final arrow *)
  apply eqit_flip in H0.
  
  (* backward reasoning, straightforward *)
  eapply eqit_mono with (RR:=(rcompose RS (flip RR2))); eauto. 
  eapply eqit_trans; eauto. 
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=(flip RR2)); easy. 
Qed. 

(* #[global] Instance geuttgen_cong_eqit_eq {E R1 R2 RS} b1 b2 r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  eapply geuttgen_cong_eqit; intros; subst; eauto.
Qed. *)


(* #[global] Instance eqitgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  repeat intro; unfold flip, eq_itree in *. 

  (* Given *)
  (* LERR1: ∀ x x' y. RR1 x x' -> RS x' y -> RS x y *)
  (* LERR2: ∀ x y y'. RR2 y y' -> RS x y' -> RS x y, *)
  (* Prove the diagram commutes *)
  
  (* 
   y -(eqit RS b1 b2) → y0 
   ↑                    ↑
   ≅RR1                ≅RR2
   |                    | 
   x -(?eqit RS b1 b2)→ x0
  *)

  (* Problem: this diagram does not have a path from x to x0. *)
  (* Solution: flip ≅RR2, as both boolean flags are false to 
    begin with this is a "symmetry" on trees only. *)

(* 
   y -(eqit RS b1 b2) → y0 
   ↑                    |
   ≅RR1                ≅(flip RR2)
   |                    ↓ 
   x -(?eqit RS b1 b2)→ x0

(* This diagram has a clear path (lifting with eqit_mono), 
  and LERR1 and LERR2 get us the correlaries we need to arrive there: namely: *)
*)
(*  by LERR1, Ret nodes of x and Ret nodes of y0 are related by RS. 
    by LERR2, Ret nodes of x0 and Ret nodes of y are related by RS. 
    RR1 ∘ RS <= RS 
    (flip RR2) ∘ RS <= RS 
    so RS is closed under left composition by RR1
    and right composition by flip RR2.
  *)
  (* We use a mix of foreward and backward reasoning. *)
  
  idtac. 
  (* build arrows and strengthen *)
  assert (rcompose RR1 RS <= RS) by (intros ? ? [? ?]; eauto). 
  assert (rcompose RS (flip RR2) <= RS) by (intros ? ? [? ?]; eauto).
  assert (eqit RR1 b1 b2 x y) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR1); easy).
  assert (eqit RR2 b1 b2 x0 y0) by 
  (eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR2); try easy).  

  (* first diagonal *)
  specialize (eqit_trans _ _ _ _ _ _ _ H4 H1) as Hdiag_weak. 
  assert (eqit RS b1 b2 x y0) as Hdiag by 
  (eapply eqit_mono with (RR:=(rcompose RR1 RS)); eauto).
  
  (* reverse the final arrow *)
  apply eqit_flip in H0.
  
  (* backward reasoning, straightforward *)
  eapply eqit_mono with (RR:=(rcompose RS (flip RR2))); eauto. 
  eapply eqit_trans; eauto. 
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=(flip RR2)); easy. 
Qed.  *)

(* 
Short version of the proof using only backward reasoning: 
  eapply eqit_mono with (b1:=b1) (b2:=b2) (RR:=(rcompose RS (flip RR2))); 
  try intros ? ? [? ?]; eauto.
  eapply eqit_trans; eauto.   
  eapply eqit_mono with (RR:=rcompose RR1 RS); try intros ? ? [? ?]; eauto.
  eapply eqit_trans; eauto. 
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR1); easy. 
  apply eqit_flip in H0. 
  now eapply eqit_mono with (b1:=false) (b2:=false) (RR:=(flip RR2)). 
  *)


(* Graveyard *)

  (* apply eqit_flip in H5 as Hflip. 
  apply eqit_flip in Hdiag1 as HdiagR. 
  
  specialize (eqit_trans _ _ _ _ _ _ _ HdiagR) as Hfinal. 
   


  replace RS with (rcompose RR1 RS).
  eapply eqit_trans. 
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR1); try easy; eauto.  
  replace RS with (rcompose RS RR2).
  eapply eqit_trans. 
  eauto.
  eapply eqit_mono with (b1:=false) (b2:=false) (RR:=RR2); try easy; eauto.   
  - 
  (* seems true, proving requires a different shape of goal *)
  apply functional_extensionality. intro. 
  apply functional_extensionality. intro. 
  
   
  (* Fail symmetry.  *)
  (* without flip, *)
  (* RR2 is not symmetric, so we fail here. *)
(* Abort.  *)
(* other attempt: with induction, gets deep and a bit nasty *) 
  step in H. 
  step in H0. 
  step in H1.
  (* step.  *)
  coinduction c CIH. 
  
  down.
  revert H0.
  revert CIH.  
  revert x0. revert H. revert x. 

  (* the dependent induction is not quite right *)
  dependent induction H1; intros. 
  - simpobs. 
  inv H; try easy. 
  inv H0; try easy. 
  constructor; eauto. 
  - simpobs. 
  dependent induction H; try easy. 
  dependent induction H0; try easy. 
  simpobs.
  constructor.
  Search elem.
  (* this feels true *)
  shelve. 
  - simpobs. 
    inv H; try easy. 
    inv H0; try easy.
    repeat lazymatch goal with | H : existT _ _ _ = _ |- _ => dependent destruction H end.
    constructor.
    intros v. 
    apply (b_chain c), (gfp_bchain c).
     (* diagram chase again, feels true but how to prove? *)
    shelve. 
  - eapply IHeqitF; eauto. 
  shelve. 
  (* poor induction's fault *)

  - simpobs. inv H0; try easy. taur. eapply IHeqitF; eauto.
  2: now backstep.
   (* also induction's fault *)
  shelve.   
Abort.  *)

#[global] Instance eqitgen_cong_eqit_eq {E R1 R2 RS} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  repeat intro.
  eapply @eqitgen_cong_eqit with (RR1:=eq) (RR2:=eq); intros; subst; eauto. 
Qed.

#[global] Instance eqitgen_cong_eqit_eq' {E R1 R2 RS} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  repeat intro.
  (* unfold eq_itree in H0. 
  assert (forall x x' y, (@eq R1 x x': Prop) -> (RS x' y: Prop) -> RS x y) as LERR. 
  intros. congruence.   *)
  (* Ask during meeting: why failing? *)
  rewrite H0. 
  rewrite H. 
  eapply @eqitgen_cong_eqit with (RR1:=eq) (RR2:=eq); intros; subst; eauto. 
Qed.

#[global] Instance euttge_cong_euttge {E R RS}
       (TRANS: Transitive RS):
  Proper (euttge RS ==> flip (euttge RS) ==> flip impl)
         (@eqit E R R RS true false).
Proof.
  repeat intro. assert (HYP := trans_rcompose RS TRANS).
  (* needed a bit of repair *)
  do 2 (eapply eqit_mono with (RR:=rcompose RS RS); repeat intro; eauto; eapply eqit_trans; eauto).
Qed.

#[global] Instance euttge_cong_euttge_eq {E R}:
  Proper (euttge eq ==> flip (euttge eq) ==> flip impl)
         (@eqit E R R eq true false).
Proof.
  eapply euttge_cong_euttge; eauto using eq_trans.
Qed.


(* Auxiliary results on [itree]s. *)

Lemma tau_eutt_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR (Tau t) s <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. 2 : { apply H. }
    red. apply eqit_Tau_r. reflexivity.
  - red. red. pstep. econstructor. auto. now punfold H. 
Qed.

Lemma tau_eqit_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eqit RR true false t s -> eqit RR true false (Tau t) s.
Proof.
  intros.
  red. pstep. econstructor. auto. now punfold H. 
Qed.

Lemma tau_eutt_RR_r : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR t (Tau s) <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. apply H.
    red. apply eqit_Tau_l. reflexivity.
  - red. red. pstep. econstructor. auto. now punfold H.
Qed.

Lemma eutt_inv_Ret_l {E R} (r1: R) (t2: itree E R):
  (Ret r1) ≈ t2 -> t2 ≳ (Ret r1).
Proof.
  intros Heutt. step in Heutt. down. 
  rewrite itree_eta. remember (RetF r1) as ot1.
  dependent induction Heutt; intros; try discriminate.
  - inv x. reflexivity.
  - inv x. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
Qed.

Lemma eutt_inv_Ret_r {E R} (t1: itree E R) (r2: R):
  t1 ≈ (Ret r2) -> t1 ≳ (Ret r2).
Proof.
  intros Heutt. step in Heutt. down. 
  rewrite itree_eta. remember (RetF r2) as ot2.
  dependent induction Heutt; intros; try discriminate.
  - inv x. reflexivity.
  - inv x. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
Qed.

(** ** Equations for core combinators *)

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => ITree.bind (ke x) k)
  | TauF t => Tau (ITree.bind t k)
  end.

Lemma unfold_bind {E R S} (t : itree E R) (k : R -> itree E S)
  : ITree.bind t k ≅ bind_ t k.
Proof.
  apply observing_sub_eqit; constructor; reflexivity.
Qed.

Lemma bind_ret_l {E R S} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k ≅ (k r).
Proof. apply observing_sub_eqit, bind_ret_. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≅ Tau (ITree.bind t k).
Proof. apply (unfold_bind (Tau t) k). Qed.

Lemma bind_vis {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k ≅ Vis e (fun x => ITree.bind (ek x) k).
Proof. apply (unfold_bind (Vis e ek) k). Qed.

Lemma bind_trigger {E R} U (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k ≅ Vis e (fun x => k x).
Proof.
  rewrite unfold_bind; cbn.
  pstep.
  constructor.
  intros. apply bind_ret_l.
Qed.

Lemma unfold_iter {E A B} (f : A -> itree E (A + B)) (x : A) :
  (ITree.iter f x) ≅ ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite unfold_aloop_. reflexivity.
Qed.

Lemma unfold_forever {E R S} (t : itree E R)
  : @ITree.forever E R S t ≅ ITree.bind t (fun _ => Tau (ITree.forever t)).
Proof.
  rewrite itree_eta, (itree_eta (ITree.bind _ _)).
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
  - step in H. step. down. 
    (* remember (TauF t1) as ot1. remember (TauF t2) as ot2. *)
    move H before RR. revert_until H. 
    dependent induction H; intros.  
    + now backstep. 
    + inv H. 
      * taul. eapply IHeqitF; eauto. 
      * taul. eapply IHeqitF; eauto. 
      * assumption. 
    + inv H. 
      * taur. eapply IHeqitF; eauto. 
      * assumption. 
      * taur. eapply IHeqitF; eauto. 
  - step. now constructor.   
Qed. 

Lemma eqit_Vis_gen b1 b2 {U1 U2} (p : U1 = U2) (e1 : E U1) (e2 : E U2)
      (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2)
  : eqeq E p e1 e2 -> pweqeq (eqit RR b1 b2) p k1 k2 ->
    eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2).
Proof.
  destruct p; cbn. intros <- H. pstep. econstructor. apply H.
Qed.

Lemma eqit_Vis b1 b2 {U} (e : E U)
    (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : (forall u, eqit RR b1 b2 (k1 u) (k2 u)) ->
    eqit RR b1 b2 (Vis e k1) (Vis e k2).
Proof.
  apply eqit_Vis_gen with (p := eq_refl); constructor.
Qed.

Lemma eqit_Ret b1 b2 (r1 : R1) (r2 : R2) :
  RR r1 r2 <-> @eqit E _ _ RR b1 b2 (Ret r1) (Ret r2).
Proof.
  split; intros H.
  - pstep. constructor; auto.
  - punfold H. inversion H; subst; auto.
Qed.

(** *** "Up-to" principles for coinduction. *)

Inductive eqit_bind_clo b1 b2 (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: eqit RU b1 b2 t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eqit_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eqit_bind_clo : itree.

(* This should actually probably be an instance relation... *)


(* Ask about lattices: there's an implicit lattice of relations here, 
but should we make it explicit? *)
(* Definition paco_body {X} (f : mon X) r := (fun y => f (cup r y)).  *)

(* monotonicity of paco_body, omitted *)

(* Definition paco {X} (f : mon X) r := gfp paco_body. *)

(* Q: best way we want to define this? *)
Lemma eqit_clo_bind {RS} b1 b2 : 
  eqit_bind_clo b1 b2 (gfp (eqit_mon RS b1 b2)) <= @eqit_mon E  _ _ RS b1 b2 (gfp (eqit_mon RS b1 b2)).
Proof.
  repeat intro.
  inv H. 
  backstep.
  revert EQV. 
  revert t1 t2.  
  coinduction c CIH.  
  intros. 
  step in EQV.  
  down in EQV. 
  dependent induction EQV.
  apply REL in REL0 as Hgfpk. step in Hgfpk. 
  all: down. 
  1-3: rewrite 2observe_bind; simpobs.
  (* ret *)
  apply (gfp_bchain c).
  apply REL.  
  assumption.
  (* taus *)
  constructor.
  apply CIH. assumption. 
  (* vis *)
  constructor. 
  intro. 
  apply CIH. 
  apply REL0. 
  (* taul *)
  Search ITree.bind. 
  rewrite observe_bind. 
  simpobs. 
  taul. 
  eapply IHEQV; eauto.  
  setoid_rewrite observe_bind at 2. 
  simpobs. 
  taur. 
  eapply IHEQV; eauto. 
Qed. 


(* Lemma eqit_clo_bind b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo):
  eqit_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
Proof.
  intros rr. pcofix CIH. intros. destruct PR.
  guclo eqit_clo_trans. econstructor; auto_ctrans_eq.
  1,2: rewrite unfold_bind; reflexivity.
  punfold EQV. unfold_eqit.
  hinduction EQV before CIH; intros; pclearbot; cbn;
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
  - guclo eqit_clo_trans. econstructor; auto_ctrans_eq.
    1,2: reflexivity.
    eauto with paco.
  - gstep. econstructor. eauto 7 with paco itree.
  - gstep. econstructor. intros. red in CMP. unfold id in ID. apply ID. eauto 7 with paco itree.
  - destruct b1; try discriminate.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
  - destruct b2; try discriminate.
    guclo eqit_clo_trans. econstructor; auto_ctrans_eq; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
Qed. *)

Lemma eutt_clo_bind {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
Abort. 

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
#[global] Hint Constructors eqit_bind_clo : itree.


Lemma eqit_bind' {E R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) b1 b2
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit RR b1 b2 t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit RS b1 b2 (k1 r1) (k2 r2)) ->
  @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros.
  step. 
  eapply eqit_clo_bind; eauto. 
  econstructor; eauto. 
Qed.

Lemma eq_itree_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eq_itree E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eq_itree RR (k1 u1) (k2 u2)):
  eq_itree RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  eapply eqit_bind'; eauto.
Qed.

#[global] Instance eqit_subst {E R S} b1 b2 :
  Proper (pointwise_relation _ (eqit eq b1 b2) ==> eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.subst E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

#[global] Instance eqit_bind {E R S} b1 b2 :
  Proper (eqit eq b1 b2 ==> pointwise_relation _ (eqit eq b1 b2) ==>
          eqit eq b1 b2) (@ITree.bind E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed.

(* #[global] Instance eqit_bind {E R S} b1 b2 :
  Proper (eqitF eq b1 b2 ==> pointwise_relation _ (eqitF eq b1 b2) ==>
          eqitF eq b1 b2) (@ITree.bind E R S).
Proof.
  repeat intro; eapply eqit_bind'; eauto.
  intros; subst; auto.
Qed. *)


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

#[global] Instance eqit_eq_map {E R S} b1 b2 :
  Proper (pointwise_relation _ eq ==>
          eqit eq b1 b2 ==>
          eqit eq b1 b2) (@ITree.map E R S).
Proof.
  repeat intro; eapply eqit_map; eauto.
  intros; subst; auto.
Qed.

Add Parametric Morphism {E R1}:
        (eqit_ eq false false (gfp (eqit_mon eq false false)))
         with signature (@eq_itree E R1 _ eq ==> eq_itree eq ==> flip impl)
         as eqitF_cong_eqit. 
Proof. 
  red; intros. 
  backstep. rewrite H. rewrite H0. now step. 
Qed. 


(* We just need elem to respect eta *)
(* Add Parametric Morphism {E R1} (c : Chain (eqit_mon eq false false)):
        (elem c)
         with signature (@eq_itree E R1 _ eq ==> eq_itree eq ==> flip impl)
         as elem_cong_eqit.  *)
(* Add Parametric Morphism {E R1} (c : Chain (eqit_mon eq false false)):
        (eqit_ eq false false (elem c))
         with signature (@eq_itree E R1 _ eq ==> eq_itree eq ==> flip impl)
         as elem_cong_eqit. 
Proof. 
  red; intros. 
  step in H. 
  step in H0. 
  down. 
  dependent induction H1. 
  - simpobs. inv H0; try easy. inv H; try easy. simpobs. 
    now constructor.  
  - simpobs. dependent induction H0; try easy. dependent induction H; try easy. simpobs. 
    constructor. 
    eapply (sub_gfp_Chain).
    rewrite REL0. 
    rewrite REL1.
    eapply (leq_gfp (eqit_mon eq false false)).
    instantiate (1:=(elem c)).
    repeat intro. 
    Search elem. 
    Search gfp.  
      
  
Qed.  *)

(* Add Parametric Morphism {E R1} c :
         (@elem _ _ (@eqit_mon E _ _ eq false false) c) 
         with signature (eq_itree (@eq R1) ==> eq_itree eq ==> flip impl)
         as elem_cong_eqit. 
Proof. 
  red; intros. 
  eapply (gfp_chain c).
  rewrite H.
  rewrite H0.
 
  step. 
  step in H. step in H0. down. 
  dependent induction H. 
  - dependent induction H0. 
    + simpobs. constructor.    *)
      
(* need a monotone function that lifts elements by Taus *)

(* Lemma elem_tau_inv {E R1 R2 RS} b1 b2 c t1 t2 : 
  @elem _ _ (@eqit_mon E R1 R2 RS b1 b2) c (Tau t1) (Tau t2) -> 
  @elem _ _ (@eqit_mon E R1 R2 RS b1 b2) c t1 t2. 
Proof. 
  intro. 
  Search elem. 
  eapply (compat_chain c).  
  instantiate (1:=(fun t1 t2 => (Tau t1) (Tau t2))). *)

(* Genuine try: prove eta expansion is compatible with b.  *)
(* Add Parametric Morphism (c : Chain (eqit_mon eq false false)) : 
  (@eqit_mon E R R eq false false (elem c))
  with signature (@eq_itree E R R eq ==> eq_itree eq ==> flip impl)
  as elem_eq_itree_proper. 
Proof. 
  red; intros.
  step in H. step in H0.
  down. genobs x otx. genobs x0 otx0.  
  dependent induction H1.
  - simpobs. inv H; inv H0; try easy. now constructor. 
  - simpobs. inv H; inv H0; try easy. constructor. 
    apply observing_sub_elem; eauto. Search elem.   *)

(* Monotone eta expansion *)

Program Definition eta_expand {E R} (s : itree E R -> itree E R -> Prop) (t1 t2 : itree E R) : Prop.
Proof. 
  apply s. 
  exact {| _observe := observe t1 |}. 
  exact {| _observe := observe t2 |}. 
Defined. 


#[global] Instance trans_elem_eq_itree_mon {E R} (c : Chain (@eqit_mon E R R eq false false)) : 
  Transitive (elem c).
Proof.
  apply Transitive_chain.
  intros R' HR'.
  apply Transitive_eqit_eqit.
  - congruence. 
  - exact HR'.
Qed.

Add Parametric Morphism {E R} (c : Chain (@eqit_mon E R R eq false false)) :
  (elem c)
  with signature (observing eq ==> observing eq ==> flip impl)
  as elem_observing_proper. 
Proof. 
  intros x y Hxy x' y' Hx'y' Helem.
  symmetry in Hx'y'.  
  eapply observing_sub_elem in Hxy; eauto.
  eapply observing_sub_elem in Hx'y'; eauto.
  do 2 (etransitivity; eauto).  
Qed.   

(* This lemma requires a bit of cleverness: 
[elem c], where [c] is [Chain (eqit_mon eq false false)], 
is respected by [observing eq]. Such respectfulness 
in turn reqires transitivity of [elem c] and the fact that 
[observing eq] is a subrelation of [elem c]. Lots of work, 
but worth it! 
*)
Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  unfold eq_itree. intros.
   (* we need to eta-expland first, but we have to be able 
   to reduce later. *)
  rewrite (itree_eta_ (ITree.bind _ _)), (itree_eta s).
  (* need strong CIH *)
  revert s. 
  coinduction c CIH. 
  intros.
  (* with eta-reduction in place, we can reduce to base comparisons. *)
  desobs s H; down; cbn; simpobs; constructor; intros.
  (* Ret case is easy *)
  reflexivity. 
  (* the others are more tricky but mostly identical: *)
  (* 1. we need only show the two sides are identical under observe. *)
  all: eapply elem_observing_proper.
  (* we know they are under the CIH... *)
  all: try eapply CIH.
  (* so the rest is just 'fancy reflexivity. *)
  all: constructor; reflexivity. 
Qed. 

Lemma bind_ret_r' {E R} (u : itree E R) (f : R -> R) :
  (forall x, f x = x) ->
  ITree.bind u (fun r => Ret (f r)) ≅ u.
Proof.
  intro H. rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - reflexivity.
  - hnf. intros. apply eqit_Ret. auto.
Qed.

Ltac fold_subst := 
  repeat match goal with 
  |- context[ITree.subst ?k ?s] => 
    replace (ITree.subst k s)
    with (ITree.bind s k)
    by reflexivity
  end. 

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  unfold eq_itree. intros. 
  lazymatch goal with
  | [ |- _ (ITree.bind ?t1 _) ?t2 ] => rewrite (itree_eta_ t1), (itree_eta_ t2); cbn
  end.
  lazymatch goal with
  | [ |- _ ?t0 _ ] => rewrite (itree_eta_ t0); cbn
  end.
  revert s k h. 
  coinduction c CIH.
  intros.
  desobs s H; down; cbn; simpobs. 
  1: apply (gfp_bchain c). reflexivity. 
  all: constructor; intros; eapply elem_observing_proper.
  all: try eapply CIH.
  all: constructor. 
  all: fold_subst. 
  all: repeat rewrite observe_bind.
  all: reflexivity.
Qed.


Lemma map_map {E R S T}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) ≅ ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k ≅ ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E X Y Z} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
  (ITree.map f (ITree.bind t k)) ≅ ITree.bind t (fun x => ITree.map f (k x)).
Proof.
  intros. unfold ITree.map. apply bind_bind.
Qed.

Lemma map_ret {E A B} (f : A -> B) (a : A) :
    @ITree.map E _ _ f (Ret a) ≅ Ret (f a).
Proof.
  intros. unfold ITree.map.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma map_tau {E A B} (f : A -> B) (t : itree E A) :
    @ITree.map E _ _ f (Tau t) ≅ Tau (ITree.map f t).
Proof.
  intros.
  unfold ITree.map.
  rewrite bind_tau; reflexivity.
Qed.

#[global] Hint Rewrite @bind_ret_l : itree.
#[global] Hint Rewrite @bind_ret_r : itree.
#[global] Hint Rewrite @bind_tau : itree.
#[global] Hint Rewrite @bind_vis : itree.
#[global] Hint Rewrite @bind_map : itree.
#[global] Hint Rewrite @map_ret : itree.
#[global] Hint Rewrite @map_tau : itree.
#[global] Hint Rewrite @bind_bind : itree.

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


Ltac force_left_in H :=
  match type of H with _ ?x _ => rewrite (itree_eta x) in H; cbn in H end.

Ltac force_right_in H :=
  match type of H with _ _ ?x => rewrite (itree_eta x) in H; cbn in H end.

Ltac tau_steps_left_in H :=
  repeat (force_left_in H; rewrite tau_eutt in H); force_left_in H.

Ltac tau_steps_right_in H :=
  repeat (force_right_in H; rewrite tau_eutt in H); force_right_in H.

Ltac tau_steps_in H :=
  tau_steps_left_in H;
  tau_steps_right_in H.

Lemma eqit_inv_bind_ret:
  forall {E X R1 R2 RR} b1 b2
    (ma : itree E X) (kb : X -> itree E R1) (b: R2),
    @eqit E R1 R2 RR b1 b2 (ITree.bind ma kb) (Ret b) ->
    exists a, @eqit E X X eq b1 b2 ma (Ret a) /\
         @eqit E R1 R2 RR b1 b2 (kb a) (Ret b).
Proof.
  intros.
  step in H. down. 
  remember (observe (ITree.bind ma kb)) as otl.
  remember (RetF b) as tr.
  revert ma kb Heqotl b Heqtr.
  dependent induction H; try solve [intros; subst; discriminate].
  - intros.
    rewrite Heqtr. 
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    exists r. split.
    * rewrite itree_eta, Ema. reflexivity.
    * rewrite itree_eta_. unfold _observe. rewrite <- Heqotl.
    rewrite Heqtr in x. inv x.
    pfold; constructor; auto.
  - intros. subst.
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + exists r. split.
      * rewrite itree_eta, Ema. reflexivity.
      * pfold. down. unfold observe at 1; unfold _observe. rewrite <- Heqotl. constructor; auto.
      + inv Heqotl. specialize (IHeqitF _ eq_refl eq_refl _ _ eq_refl _ eq_refl).
      edestruct IHeqitF as (a & ? & ?); exists a.
      split; auto.
      pfold; down; rewrite Ema. constructor; auto.
      now punfold H0.
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

Ltac inv_eq_VisF H :=
  lazymatch type of H with
  | (VisF _ _ = @VisF _ _ _ ?X ?e ?k) =>
    refine
      match H in _ = w return
        match w with
        | VisF e k => _
        | _ => False
        end
      with eq_refl => _
      end; try clear H X e k
  end.

Lemma eqit_inv_bind_vis :
  forall {A B C E X RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxc : X -> itree E C),
    eqit RR b1 b2 (ITree.bind ma kab) (Vis e kxc) ->
    (exists (kxa : X -> itree E A), (eqit eq b1 b2 ma (Vis e kxa)) /\
                              forall (x:X), eqit RR b1 b2 (ITree.bind (kxa x) kab) (kxc x)) \/
    (exists (a : A), eqit eq b1 b2 ma (Ret a) /\ eqit RR b1 b2 (kab a) (Vis e kxc)).
Proof.
  intros. punfold H. unfold eqit_ in H. down. 
  remember (observe (ITree.bind ma kab)) as tl.
  remember (VisF e kxc) as tr.
  revert ma kab Heqtl kxc Heqtr.
  dependent induction H; try solve [intros; subst; discriminate].
  - intros. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right. exists r. split.
      * pfold; down. rewrite Ema. constructor. auto.
      * pfold; down. unfold observe at 1; unfold _observe. rewrite <- Heqtl.
        simpobs. constructor; auto.
    + left.
      symmetry in Heqtl.
      revert x. revert k2 REL Heqtr. inv_eq_VisF Heqtl. intros.
      rewrite Heqtr in x. 
      cbn in x. 
      inv_eq_VisF x.
      exists k. split.
      * pfold; down. rewrite Ema. constructor. down. reflexivity.
      * pclearbot. auto.
  - intros. subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn: Ema; try discriminate.
    + right; exists r; split.
      * rewrite itree_eta, Ema; reflexivity.
      * pfold. down. unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl eq_refl _ _ eq_refl _ eq_refl).
      destruct IHeqitF as [(k0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists k0. split; auto.
        pfold; down; rewrite Ema; constructor; now punfold H0. 
      * exists a. split; auto.
        pfold; down; rewrite Ema; constructor; now punfold H0.
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
  intros. punfold H. down. 
  remember (observe (ITree.bind ma kab)) as tl.
  remember (TauF tc) as tr.
  revert ma kab Heqtl Heqtr.
  dependent induction H; intros; try solve [subst; discriminate].
  - inv Heqtr. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * pfold; down; rewrite Ema; constructor; auto.
      * step; down; rewrite <- x; unfold observe, _observe; rewrite <- Heqtl; now constructor.
    + left; exists t; split.
      * pfold; down; rewrite Ema; constructor; apply reflexivity.
      * inv Heqtl. inv x. assumption.
  - subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * pfold; down; rewrite Ema; constructor; auto.
      * pfold; down; unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor 4; auto.
    + inv Heqtl. specialize (IHeqitF _ eq_refl eq_refl _ _ eq_refl eq_refl).
      destruct IHeqitF as [(t0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists t0. split; auto.
        pfold; down; rewrite Ema; constructor 4; now punfold H0.
      * exists a. split; auto.
        pfold; down; rewrite Ema; constructor; now punfold H0.
  - inv Heqtr.
    left; exists ma; split.
    + pfold; constructor; auto. 
    + inv x; pfold; assumption.
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
  down. 
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
  down.
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
  down.
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
  down.
  remember (observe (Vis e k)) as x.
  remember (observe (ITree.spin)) as sp.
  revert Heqx Heqsp.
  induction H; intros EQ1 EQ2; try (now inv EQ1 || now inv EQ2).
  - apply IHeqitF; auto.
    inv EQ2.
    reflexivity.
Qed.
