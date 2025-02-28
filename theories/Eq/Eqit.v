
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
     Structures.Orders (* Hint Unfold is_true *)
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.Paco2
     Eq.Shallow.

Local Open Scope itree_scope.

(* TODO: Send to paco *)
#[global] Instance Symmetric_bot2 (A : Type) : @Symmetric A bot2.
Proof. auto. Qed.

#[global] Instance Transitive_bot2 (A : Type) : @Transitive A bot2.
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
  Hint Constructors eqitF : itree.

  Definition eqit_ b1 b2 vclo sim :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => eqitF b1 b2 vclo sim (observe t1) (observe t2).
  Hint Unfold eqit_ : itree.

  (** [eqitF] and [eqit_] are both monotone. *)

  Lemma eqitF_mono b1 b2 x0 x1 vclo vclo' sim sim'
        (IN: eqitF b1 b2 vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    eqitF b1 b2 vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto with itree.
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
#[global] Hint Constructors eqitF : itree.
#[global] Hint Unfold eqit_ : itree.
#[global] Hint Resolve eqit__mono : paco.
#[global] Hint Resolve eqit_idclo_mono : paco.
#[global] Hint Unfold eqit : itree.
#[global] Hint Unfold eq_itree : itree.
#[global] Hint Unfold eutt : itree.
#[global] Hint Unfold euttge : itree.
#[global] Hint Unfold id : itree.

Lemma eqitF_inv_VisF_r {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 vclo sim}
    t1 X2 (e2 : E X2) (k2 : X2 -> _)
  : eqitF RR b1 b2 vclo sim t1 (VisF e2 k2) ->
    (exists k1, t1 = VisF e2 k1 /\ forall v, vclo sim (k1 v) (k2 v)) \/
    (b1 /\ exists t1', t1 = TauF t1' /\ eqitF RR b1 b2 vclo sim (observe t1') (VisF e2 k2)).
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ _ _ t2 return
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

Lemma eqitF_inv_VisF_weak {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 vclo sim}
    X1 (e1 : E X1) (k1 : X1 -> _) X2 (e2 : E X2) (k2 : X2 -> _)
  : eqitF RR b1 b2 vclo sim (VisF e1 k1) (VisF e2 k2) ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ pweqeq (vclo sim) p k1 k2.
Proof.
  refine (fun H =>
    match H in eqitF _ _ _ _ _ t1 t2 return
      match t1, t2 return Prop with
      | VisF e1 k1, VisF e2 k2 => _
      | _, _ => True
      end with
    | EqVis _ _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - exists eq_refl; cbn; eauto.
  - destruct i; exact I.
Qed.

Lemma eqitF_inv_VisF {E R1 R2} (RR : R1 -> R2 -> Prop) {b1 b2 vclo sim}
    X (e : E X) (k1 : X -> _) (k2 : X -> _)
  : eqitF RR b1 b2 vclo sim (VisF e k1) (VisF e k2) ->
    forall x, vclo sim (k1 x) (k2 x).
Proof.
  intros H. dependent destruction H. assumption.
Qed.

Lemma eqitF_VisF_gen {E R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 vclo sim}
    {X1 X2} (p : X1 = X2) (e1 : E X1) (k1 : X1 -> _) (e2 : E X2) (k2 : X2 -> _)
  : eqeq E p e1 e2 -> pweqeq (vclo sim) p k1 k2 ->
    eqitF RR b1 b2 vclo sim (VisF e1 k1) (VisF e2 k2).
Proof.
  destruct p; intros <-; cbn; constructor; auto.
Qed.

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

(* Tactic to fold eqitF automatically by expanding observe if needed *)
Tactic Notation "fold_eqitF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | eqitF ?_RR ?_B1 ?_B2 id (upaco2 (eqit_ ?_RR ?_B1 ?_B2 id) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => change _OT1 with (observe (go _OT1)) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => change _OT2 with (observe (go _OT2)) in H
      end;
      eapply fold_eqitF in H; [| eauto | eauto]
  end.

#[global] Instance eqitF_Proper_R {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> (eq_rel ==> eq_rel) ==> eq_rel ==> eq_rel)
    (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; unfold subrelationH; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
Qed.

#[global] Instance eqitF_Proper_R2 {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
  - induction H0; auto with itree.
    econstructor. apply H. assumption.
Qed.

#[global] Instance eqit_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> iff) (@eqit E R1 R2).
Proof with auto with itree.
  repeat red.
  intros. subst.
  split.
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H0. red in H0. red.
     hinduction H0 before CIH; intros...
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL...
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL...
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H0. red in H0. red.
     hinduction H0 before CIH; intros...
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL...
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL...
Qed.

#[global] Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
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
  intros. induction PR; eauto with itree.
Qed.

Lemma eqit_flip {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2:
  forall (u : itree E R1) (v : itree E R2),
    eqit (flip RR) b2 b1 v u -> eqit RR b1 b2 u v.
Proof.
  pcofix self; pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco itree.
Qed.

Lemma eqit_mon {E R1 R2} RR RR' (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2')
      (LERR: RR <2= RR'):
  @eqit E R1 R2 RR b1 b2 <2= eqit RR' b1' b2'.
Proof.
  pcofix self. pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco itree.
Qed.

#[global] Hint Unfold flip : itree.

(* end hide *)

(** A notation of [eq_itree eq]. You can write [≅] using [[\cong]] in
    tex-mode *)

Infix "≅" := (eq_itree eq) (at level 70) : type_scope.

Infix "≈" := (eutt eq) (at level 70) : type_scope.

Infix "≳" := (euttge eq) (at level 70) : type_scope.

(* TODO: Find a way to not clobber the export [type_scope]? *)

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
Hint Constructors eqit_trans_clo : itree.

Definition eqitC b1 b2 := eqit_trans_clo b1 b2 false false.
Hint Unfold eqitC : itree.

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
Proof with eauto with paco itree.
  econstructor; [ eauto with paco itree | ].
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; [ | eauto with itree ].
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy...
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; [ | eauto with itree ].
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with itree ].
    pclearbot. econstructor. gclo.
    econstructor; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try discriminate Heqx; [ inv_Vis | eauto with itree ].
    remember (VisF e k3) as y.
    hinduction EQVr before r; intros; try discriminate Heqy; [ inv_Vis | eauto with itree ].
    econstructor. intros. pclearbot.
    eapply MON.
    + apply CMP. econstructor...
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; [ | eauto with itree ].
    pclearbot. punfold REL...
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with itree ].
    pclearbot. punfold REL...
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
  intros. destruct PR. destruct REL; eauto with itree.
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

#[global] Hint Unfold eqitC : itree.
#[global] Hint Resolve eqitC_mon : paco.
#[global] Hint Resolve eqitC_wcompat : paco.
#[global] Hint Resolve eqit_idclo_compat : paco.
#[global] Hint Resolve eqitC_dist : paco.
Arguments eqit_clo_trans : clear implicits.
#[global] Hint Constructors eqit_trans_clo : itree.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).

#[global] Instance Reflexive_eqitF b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqitF RR b1 b2 id sim).
Proof.
  red. destruct x; constructor; eauto with itree.
Qed.

#[global] Instance Symmetric_eqitF b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqitF RR b b id sim).
Proof.
  red. induction 3; constructor; subst; eauto.
  intros. apply H0. apply (REL v).
Qed.

#[global] Instance Reflexive_eqit_ b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqit_ RR b1 b2 id sim).
Proof. repeat red. intros. reflexivity. Qed.

#[global] Instance Symmetric_eqit_ b (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqit_ RR b b id sim).
Proof. repeat red; symmetry; auto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit_gen b1 b2 (r rg: itree E R -> itree E R -> Prop) :
  Reflexive RR -> Reflexive (gpaco2 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) r rg).
Proof.
  pcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto with paco itree.
Qed.

#[global] Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. ginit. apply Reflexive_eqit_gen; eauto.
Qed.

#[global] Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E _ _ RR b b).
Proof.
  red; intros. apply eqit_flip.
  eapply eqit_mon, H0; eauto.
Qed.

#[global] Instance eq_sub_euttge:
  subrelation (@eq_itree E _ _ RR) (euttge RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; auto 7 with paco itree.
Qed.

#[global] Instance euttge_sub_eutt:
  subrelation (@euttge E _ _ RR) (eutt RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; pclearbot; auto 7 with paco itree.
Qed.

#[global] Instance eq_sub_eutt:
  subrelation (@eq_itree E _ _ RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. apply H.
Qed.

End eqit_gen.

#[global] Hint Resolve Reflexive_eqit Reflexive_eqit_gen : reflexivity.

Section eqit_eq.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R : Type}.

Local Notation eqit := (@eqit E R R eq).

#[global] Instance Reflexive_eqitF_eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF eq b1 b2 id sim).
Proof.
  apply Reflexive_eqitF; eauto.
Qed.

#[global] Instance Symmetric_eqitF_eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqitF eq b b id sim).
Proof.
  apply Symmetric_eqitF; eauto.
Qed.

#[global] Instance Reflexive_eqit__eq b1 b2 (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqit_ eq b1 b2 id sim).
Proof. apply Reflexive_eqit_; eauto. Qed.

#[global] Instance Symmetric_eqit__eq b (sim : itree E R -> itree E R -> Prop)
: Symmetric sim -> Symmetric (eqit_ eq b b id sim).
Proof. apply Symmetric_eqit_; eauto. Qed.

(** *** [eqit] is an equivalence relation *)

#[global] Instance Reflexive_eqit_gen_eq b1 b2 (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gpaco2 (eqit_ eq b1 b2 id) (eqitC eq b1 b2) r rg).
Proof.
  apply Reflexive_eqit_gen; eauto.
Qed.

#[global] Instance Reflexive_eqit_eq b1 b2 : Reflexive (eqit b1 b2).
Proof.
  apply Reflexive_eqit; eauto.
Qed.

#[global] Instance Symmetric_eqit_eq b : Symmetric (eqit b b).
Proof.
  apply Symmetric_eqit; eauto.
Qed.

(** *** Congruence properties *)

#[global] Instance eqit_observe b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@observe E R).
Proof.
  constructor; punfold H; auto with itree.
Qed.

#[global] Instance eqit_tauF b1 b2:
  Proper (eqit b1 b2 ==> going (eqit b1 b2)) (@TauF E R _).
Proof.
  constructor; pstep. econstructor. eauto.
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
  pstep. red. rewrite (observing_observe H). apply Reflexive_eqitF; eauto. left. apply reflexivity.
Qed.

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
  revert H0; apply pweqeq_mon; intros; pclearbot; auto.
Qed.

(* This assumes UIP. *)
Lemma eqit_inv_Vis {E R1 R2} (RR : R1 -> R2 -> Prop) b1 b2 U (e : E U)
    (k1 : U -> itree E R1) (k2 : U -> itree E R2)
  : eqit RR b1 b2 (Vis e k1) (Vis e k2) ->
    forall u, eqit RR b1 b2 (k1 u) (k2 u).
Proof.
  intros H x; punfold H; apply eqitF_inv_VisF with (x := x) in H; pclearbot; auto.
Qed.

Lemma eqit_inv_Tau_l {E R1 R2 RR} b1 t1 t2 :
  @eqit E R1 R2 RR b1 true (Tau t1) t2 -> eqit RR b1 true t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before b1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt1. punfold_reverse H.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma eqit_inv_Tau_r {E R1 R2 RR} b2 t1 t2 :
  @eqit E R1 R2 RR true b2 t1 (Tau t2) -> eqit RR true b2 t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t2) as tt2. genobs t1 ot1.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt2. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - red in IHeqitF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqtt2. punfold_reverse H.
Qed.

Lemma eqit_inv_Tau {E R1 R2 RR} b1 b2 t1 t2 :
  @eqit E R1 R2 RR b1 b2 (Tau t1) (Tau t2) -> eqit RR b1 b2 t1 t2.
Proof with eauto with itree.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. remember (TauF t2) as tt2.
  hinduction H before b2; intros; try discriminate.
  - inv Heqtt1. inv Heqtt2. pclearbot. eauto.
  - inv Heqtt1. inv H.
    + pclearbot. punfold REL. pstep. red. simpobs...
    + pstep. red. simpobs. econstructor; eauto. pstep_reverse. apply IHeqitF; eauto.
    + eauto with itree.
  - inv Heqtt2. inv H.
    + pclearbot. punfold REL. pstep. red. simpobs...
    + eauto with itree.
    + pstep. red. simpobs. econstructor; auto. pstep_reverse. apply IHeqitF; eauto.
Qed.

Section eqit_inv.

Context {E : Type -> Type} {R1 R2} {RR : R1 -> R2 -> Prop} {b1 b2 : bool}.
Context {vclo : (itree E R1 -> itree E R2 -> Prop) -> (itree E R1 -> itree E R2 -> Prop)}.
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
  intros H; punfold H; red in H.
  genobs t1 ot1; genobs t2 ot2; revert t1 t2 Heqot1 Heqot2; unfold observe, _observe.
  destruct H; pclearbot; intros * E1 E2; rewrite <- E1, <- E2; cbn; auto.
  - exists eq_refl; cbn; eauto.
  - rewrite CHECK in *. destruct ot2.
    1,3: pfold; red; unfold observe, _observe; rewrite <- E2; assumption.
    1: apply eqit_inv_Tau_r; pfold; red; unfold observe, _observe; assumption.
  - rewrite CHECK in *. destruct ot1.
    1,3: pfold; red; unfold observe, _observe; rewrite <- E1; assumption.
    1: apply eqit_inv_Tau_l; pfold; red; unfold observe, _observe; assumption.
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
  intros. pstep. econstructor; eauto. punfold H.
Qed.

Lemma eqit_Tau_r {E R1 R2 RR} b1 (t1 : itree E R1) (t2 : itree E R2) :
  eqit RR b1 true t1 t2 -> eqit RR b1 true t1 (Tau t2).
Proof.
  intros. pstep. econstructor; eauto. punfold H.
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

Lemma eqit_trans {E R1 R2 R3} (RR1: R1->R2->Prop) (RR2: R2->R3->Prop) b1 b2 t1 t2 t3
      (INL: eqit RR1 b1 b2 t1 t2)
      (INR: eqit RR2 b1 b2 t2 t3):
  @eqit E _ _ (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  revert_until b2. pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - remember (RetF r2) as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with paco itree.
  - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply eqit_inv_Tau. eauto with itree.
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      pclearbot. punfold REL. red in REL.
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * remember (RetF r1) as ot.
        hinduction REL0 before CIH; intros; inv Heqot; eauto with paco itree.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
        econstructor. intros. right.
        destruct (REL v), (REL0 v); try contradiction. eauto.
      * eapply IHREL0; eauto. pstep_reverse.
        destruct b1; inv CHECK0.
        apply eqit_inv_Tau_r. eauto with itree.
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; try discriminate; [ inv_Vis | eauto with itree ].
    econstructor. intros.
    destruct (REL v), (REL0 v); try contradiction; eauto with itree.
  - eauto with itree.
  - remember (TauF t0) as ot.
    hinduction INR before CIH; intros; try inversion Heqot; subst.
    2,3: eauto 3 with itree.
    eapply IHINL. pclearbot. punfold REL. eauto with itree.
Qed.

#[global] Instance Transitive_eqit {E : Type -> Type} {R: Type} (RR : R -> R -> Prop) (b1 b2: bool):
  Transitive RR -> Transitive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. assert (TRANS := trans_rcompose RR). eapply eqit_mon, eqit_trans; eauto.
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
  red; intros. assert (TRANS := trans_rcompose RR). eapply eqit_mon, eqit_trans; eauto.
Qed.

#[global] Instance Equivalence_eutt {E R RR} : Equivalence RR -> Equivalence (@eutt E R R RR).
Proof.
  constructor; try typeclasses eauto.
Qed.

#[global] Instance geuttgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2 r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@eqit_ E R1 R2 RS b1 b2 id) (eqitC RS b1 b2) r rg).
Proof.
  repeat intro. guclo eqit_clo_trans. econstructor; cycle -3; eauto.
  - eapply eqit_mon, H; eauto; discriminate.
  - eapply eqit_mon, H0; eauto; discriminate.
Qed.

#[global] Instance geuttgen_cong_eqit_eq {E R1 R2 RS} b1 b2 r rg:
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
Qed.

#[global] Instance eqitgen_cong_eqit {E R1 R2 RR1 RR2 RS} b1 b2
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y):
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  ginit. intros. eapply geuttgen_cong_eqit; eauto. gfinal. eauto.
Qed.

#[global] Instance eqitgen_cong_eqit_eq {E R1 R2 RS} b1 b2:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@eqit E R1 R2 RS b1 b2).
Proof.
  ginit. intros. rewrite H1, H0. gfinal. eauto.
Qed.

#[global] Instance euttge_cong_euttge {E R RS}
       (TRANS: Transitive RS):
  Proper (euttge RS ==> flip (euttge RS) ==> flip impl)
         (@eqit E R R RS true false).
Proof.
  repeat intro. assert (HYP := trans_rcompose RS TRANS).
  do 2 (eapply eqit_mon, eqit_trans; eauto).
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
  - red. red. pstep. econstructor. auto. punfold H.
Qed.

Lemma tau_eqit_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eqit RR true false t s -> eqit RR true false (Tau t) s.
Proof.
  intros.
  red. pstep. econstructor. auto. punfold H.
Qed.

Lemma tau_eutt_RR_r : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR t (Tau s) <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. apply H.
    red. apply eqit_Tau_l. reflexivity.
  - red. red. pstep. econstructor. auto. punfold H.
Qed.

Lemma eutt_inv_Ret_l {E R} (r1: R) (t2: itree E R):
  (Ret r1) ≈ t2 -> t2 ≳ (Ret r1).
Proof.
  intros Heutt. punfold Heutt; red in Heutt; cbn in Heutt.
  rewrite itree_eta. remember (RetF r1) as ot1.
  induction Heutt; intros; try discriminate.
  - inv Heqot1. reflexivity.
  - inv Heqot1. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
Qed.

Lemma eutt_inv_Ret_r {E R} (t1: itree E R) (r2: R):
  t1 ≈ (Ret r2) -> t1 ≳ (Ret r2).
Proof.
  intros Heutt. punfold Heutt; red in Heutt; cbn in Heutt.
  rewrite itree_eta. remember (RetF r2) as ot2.
  induction Heutt; intros; try discriminate.
  - inv Heqot2. reflexivity.
  - inv Heqot2. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
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
  intros; red. left. apply bind_ret_l.
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
  - punfold H. red in H. simpl in *. pstep. red.
    remember (TauF t1) as ot1. remember (TauF t2) as ot2.
    hinduction H before RR; intros; subst; try inv Heqot1; try inv Heqot2; eauto.
    + pclearbot. punfold REL.
    + inv H; eauto with itree.
    + inv H; eauto with itree.
  - pstep. constructor; auto.
Qed.

Lemma eqit_Vis_gen b1 b2 {U1 U2} (p : U1 = U2) (e1 : E U1) (e2 : E U2)
      (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2)
  : eqeq E p e1 e2 -> pweqeq (eqit RR b1 b2) p k1 k2 ->
    eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2).
Proof.
  destruct p; cbn. intros <- H. pstep. econstructor. left. apply H.
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

Lemma eqit_clo_bind b1 b2 vclo
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
Qed.

Lemma eutt_clo_bind {U1 U2 UU} t1 t2 k1 k2
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
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
#[global] Hint Constructors eqit_bind_clo : itree.

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

Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) ≅ s.
Proof.
  ginit. pcofix CIH. intros.
  rewrite (itree_eta_ (ITree.bind _ _)), (itree_eta s). cbn.
  destruct (observe s); cbn; gstep; constructor; eauto with paco itree.
Qed.

Lemma bind_ret_r' {E R} (u : itree E R) (f : R -> R) :
  (forall x, f x = x) ->
  ITree.bind u (fun r => Ret (f r)) ≅ u.
Proof.
  intro H. rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - reflexivity.
  - hnf. intros. apply eqit_Ret. auto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h ≅ ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  ginit. pcofix CIH. intros.
  lazymatch goal with
  | [ |- _ (ITree.bind ?t1 _) ?t2 ] => rewrite (itree_eta_ t1), (itree_eta_ t2); cbn
  end.
  lazymatch goal with
  | [ |- _ ?t0 _ ] => rewrite (itree_eta_ t0); cbn
  end.
  destruct (observe s); cbn.
  1: apply reflexivity.
  all: gstep; constructor; eauto with paco itree.
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
  punfold H.
  unfold eqit_ in *.
  cbn in *.
  remember (observe (ITree.bind ma kb)) as otl.
  remember (RetF b) as tr.
  revert ma kb Heqotl b Heqtr.
  induction H; try discriminate.
  - intros; subst.
    inv Heqtr.
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    exists r. split.
    * rewrite itree_eta, Ema. reflexivity.
    * rewrite itree_eta_. unfold _observe. rewrite <- Heqotl. pfold; constructor; auto.
  - intros. subst.
    unfold observe, _observe in Heqotl; cbn in Heqotl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + exists r. split.
      * rewrite itree_eta, Ema. reflexivity.
      * pfold. red. unfold observe at 1; unfold _observe. rewrite <- Heqotl. constructor; auto.
    + inv Heqotl. specialize (IHeqitF _ _ eq_refl _ eq_refl).
      destruct IHeqitF as (a & ? & ?); exists a.
      split; auto.
      pfold; red; rewrite Ema. constructor; auto.
      punfold H0.
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
  intros. punfold H. unfold eqit_ in H. cbn in *.
  remember (observe (ITree.bind ma kab)) as tl.
  remember (VisF e kxc) as tr.
  revert ma kab Heqtl kxc Heqtr.
  induction H; try discriminate.
  - intros. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right. exists r. split.
      * pfold; red. rewrite Ema. constructor. auto.
      * pfold; red. unfold observe at 1; unfold _observe. rewrite <- Heqtl.
        constructor; auto.
    + left.
      symmetry in Heqtl.
      revert k2 REL Heqtr. inv_eq_VisF Heqtl. intros.
      inv_eq_VisF Heqtr.
      exists k. split.
      * pfold; red. rewrite Ema. constructor. red. left. apply reflexivity.
      * pclearbot. auto.
  - intros. subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn: Ema; try discriminate.
    + right; exists r; split.
      * rewrite itree_eta, Ema; reflexivity.
      * pfold. red. unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl _ eq_refl).
      destruct IHeqitF as [(k0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists k0. split; auto.
        pfold; red; rewrite Ema; constructor; punfold H0.
      * exists a. split; auto.
        pfold; red; rewrite Ema; constructor; punfold H0.
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
  intros. punfold H. unfold eqit_ in H. cbn in H.
  remember (observe (ITree.bind ma kab)) as tl.
  remember (TauF tc) as tr.
  revert ma kab Heqtl Heqtr.
  induction H; try discriminate; intros.
  - inv Heqtr. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * pfold; red; rewrite Ema; constructor; auto.
      * pfold; red; unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor; auto.
    + left; exists t; split.
      * pfold; red; rewrite Ema; constructor; left; apply reflexivity.
      * inv Heqtl. pclearbot. assumption.
  - subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right; exists r; split.
      * pfold; red; rewrite Ema; constructor; auto.
      * pfold; red; unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor 4; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl eq_refl).
      destruct IHeqitF as [(t0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists t0. split; auto.
        pfold; red; rewrite Ema; constructor 4; punfold H0.
      * exists a. split; auto.
        pfold; red; rewrite Ema; constructor; punfold H0.
  - inv Heqtr.
    left; exists ma; split.
    + pfold; constructor; auto. apply Reflexive_eqitF_eq. intros ?; left; apply reflexivity.
    + pfold; assumption.
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
