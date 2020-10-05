(** Well-founded orders. *)

Require Import Arith Relations Max NPeano Program Wellfounded List Lia.
From Paco Require Import paco.
Import ListNotations.

Set Implicit Arguments.
Global Set Bullet Behavior "Strict Subproofs".

Ltac ginduction H :=
  move H at top; revert_until H; induction H.

(** * Additions to the Relations library. *)

Notation rtc := (clos_refl_trans _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt_step rt_refl t_step.

Lemma tc_well_founded: forall A R
    (WF: @well_founded A R),
  well_founded (tc R).
Proof. clear.
  red; intros; induction a using (well_founded_ind WF); econstructor; intros.
  apply clos_trans_tn1_iff in H0; induction H0; eauto.
  apply IHclos_trans_n1; specialize (H y0 H0); inversion H; eauto.
Qed.

Lemma rtc_mon: forall X (R R': X -> X -> Prop) a b
    (IN: rtc R a b)
    (LE: R <2= R'),
  rtc R' a b.
Proof.
  intros; induction IN; [econstructor 1|econstructor 2|econstructor 3]; eauto.
Qed.

Lemma tc_mon: forall X (R R': X -> X -> Prop) a b
    (IN: tc R a b)
    (LE: R <2= R'),
  tc R' a b.
Proof.
  intros; induction IN; [econstructor 1|econstructor 2]; eauto.
Qed.

Lemma tc_rtc: forall X r (a b: X)
    (TC: tc r a b),
  rtc r a b.
Proof.
  intros; induction TC; eauto using rt_trans.
Qed.

Lemma rtc_tc: forall X r (a b: X)
    (RTC: rtc r a b),
  a = b \/ tc r a b.
Proof.
  intros; induction RTC; eauto.
  destruct IHRTC1, IHRTC2; subst; eauto.
  right; econstructor 2; eauto.
Qed.

Lemma tc_rtc_tc: forall X r (a b c: X)
    (TC: tc r a b)
    (RTC: rtc r b c),
  tc r a c.
Proof.
  intros; induction RTC; eauto using t_trans, t_step.
Qed.

Lemma rtc_tc_tc: forall X r (a b c: X)
    (RTC: rtc r a b)
    (TC: tc r b c),
  tc r a c.
Proof.
  intros; induction RTC; eauto using t_trans, t_step.
Qed.

Lemma tc_first: forall X r (a c: X)
    (CT: tc r a c),
  exists b, r a b /\ rtc r b c.
Proof.
  intros. induction CT; eauto using rt_refl; clear IHCT2.
  destruct IHCT1 as [? []].
  eauto using rt_step, tc_rtc, rtc_tc_tc.
Qed.

Lemma tc_last: forall X r (a c: X)
    (CT: tc r a c),
  exists b, rtc r a b /\ r b c.
Proof.
  intros; induction CT; eauto using rt_refl; clear IHCT1.
  destruct IHCT2 as [? []].
  eauto using rt_step, tc_rtc, tc_rtc_tc.
Qed.

(** * Definitions. *)

(** **
  Wellfounded Order
 *)

Structure bwfo :=
  { bwfo_set :> Type;
    bwfo_lt : bwfo_set -> bwfo_set -> Prop;
    bwfo_le : bwfo_set -> bwfo_set -> Prop;

    bwfo_le_refl: forall i, bwfo_le i i;
    bwfo_lt_le: forall i j, bwfo_lt i j -> bwfo_le i j;
    bwfo_le_le_le: forall i j k, bwfo_le i j -> bwfo_le j k -> bwfo_le i k;
    bwfo_lt_le_lt: forall i j k, bwfo_lt i j -> bwfo_le j k -> bwfo_lt i k;
    bwfo_le_lt_lt: forall i j k, bwfo_le i j -> bwfo_lt j k -> bwfo_lt i k;

    bwfo_wf : well_founded bwfo_lt;
}.
Arguments bwfo_lt {_} _ _.
Arguments bwfo_le {_} _ _.

(** **
  Non-trival Non-negative Well-founded Ordered Monoids
 *)

Structure awfo :=
{ wfo_set :> Type;

  wfo_zero : wfo_set;
  wfo_add  : wfo_set -> wfo_set -> wfo_set;

  wfo_lt : wfo_set -> wfo_set -> Prop;
  wfo_le  : wfo_set -> wfo_set -> Prop;

(* Monoid *)

  wfo_add_zero_l_le: forall i, wfo_le (wfo_add wfo_zero i) i;
  wfo_add_zero_l_ge: forall i, wfo_le i (wfo_add wfo_zero i);
  wfo_add_zero_r_le: forall i, wfo_le (wfo_add i wfo_zero) i;
  wfo_add_zero_r_ge: forall i, wfo_le i (wfo_add i wfo_zero);

  wfo_add_assoc_le: forall i j k, wfo_le (wfo_add i (wfo_add j k)) (wfo_add (wfo_add i j) k);
  wfo_add_assoc_ge: forall i j k, wfo_le (wfo_add (wfo_add i j) k) (wfo_add i (wfo_add j k));

(* Order *)

  wfo_le_refl: forall i, wfo_le i i;
  wfo_lt_le: forall i j, wfo_lt i j -> wfo_le i j;
  wfo_le_le_le: forall i j k, wfo_le i j -> wfo_le j k -> wfo_le i k;
  wfo_lt_le_lt: forall i j k, wfo_lt i j -> wfo_le j k -> wfo_lt i k;
  wfo_le_lt_lt: forall i j k, wfo_le i j -> wfo_lt j k -> wfo_lt i k;

  wfo_add_le_left: forall i i' j (LE: wfo_le i i'), wfo_le (wfo_add i j) (wfo_add i' j);
  wfo_add_le_right: forall i j j' (LE: wfo_le j j'), wfo_le (wfo_add i j) (wfo_add i j');
  wfo_add_lt_left: forall i i' j (LT: wfo_lt i i'), wfo_lt (wfo_add i j) (wfo_add i' j);
  wfo_add_lt_right: forall i j j' (LT: wfo_lt j j'), wfo_lt (wfo_add i j) (wfo_add i j');

(* Well-founded *)
  wfo_wf : well_founded wfo_lt;

(* Positive *)
  wfo_non_negative: forall i, wfo_le wfo_zero i;

(* Non-trivial *)
  wfo_one  : wfo_set;
  wfo_non_trivial : wfo_lt wfo_zero wfo_one;
}.

Arguments wfo_lt {_} _ _.
Arguments wfo_le {_} _ _.
Arguments wfo_zero {_}.
Arguments wfo_one {_}.
Arguments wfo_add {_} _ _.

(* **
  Symmetric Product of Algebraic Wellfounded Orders
 *)

Definition symprod_lt (a b : awfo) (x y: a * b) :=
  (wfo_lt (fst x) (fst y) /\ wfo_le (snd x) (snd y)) \/
  (wfo_le (fst x) (fst y) /\ wfo_lt (snd x) (snd y)).

Definition symprod_le (a b : awfo) (x y: a * b) :=
  wfo_le (fst x) (fst y) /\ wfo_le (snd x) (snd y).

Program Definition awfo_symprod (a b : awfo) : awfo :=
  {| wfo_lt   := symprod_lt a b;
     wfo_le   := symprod_le a b;
     wfo_zero := (wfo_zero, wfo_zero);
     wfo_one  := (wfo_zero, wfo_one);
     wfo_add  := fun i j => (wfo_add (fst i) (fst j), wfo_add (snd i) (snd j));
  |}.
Next Obligation. red. eauto using wfo_add_zero_l_le. Qed.
Next Obligation. red. eauto using wfo_add_zero_l_ge. Qed.
Next Obligation. red. eauto using wfo_add_zero_r_le. Qed.
Next Obligation. red. eauto using wfo_add_zero_r_ge. Qed.
Next Obligation. red. eauto using wfo_add_assoc_le. Qed.
Next Obligation. red. eauto using wfo_add_assoc_ge. Qed.
Next Obligation. split; simpl; eauto using wfo_le_refl. Qed.
Next Obligation.
  destruct H as [[]|[]]; split; simpl in *; eauto using wfo_lt_le, wfo_le_le_le.
Qed.
Next Obligation.
  destruct H, H0; split; simpl in *; eauto using wfo_le_le_le.
Qed.
Next Obligation.
  destruct H, H, H0; [left|right]; split; simpl in *; eauto using wfo_lt_le_lt, wfo_le_le_le.
Qed.
Next Obligation.
  destruct H, H0, H0; [left|right]; split; simpl in *; eauto using wfo_le_lt_lt, wfo_le_le_le.
Qed.
Next Obligation.
  destruct LE; split; simpl in *; eauto using wfo_add_le_left.
Qed.
Next Obligation.
  destruct LE; split; simpl in *; eauto using wfo_add_le_right.
Qed.
Next Obligation.
  destruct LT, H; [left|right]; split; simpl in *; eauto using wfo_add_lt_left, wfo_add_le_left.
Qed.
Next Obligation.
  destruct LT, H; [left|right]; split; simpl in *; eauto using wfo_add_lt_right, wfo_add_le_right.
Qed.
Next Obligation.
  intros [u v].
  assert (WFu := wfo_wf _ u). revert v.
  induction WFu as [u _ HYPu].
  econstructor; intros [u' v'] LT'.
  destruct LT', H; simpl in *.
  - eapply HYPu in H; eauto.
  - clear v H0.
    assert (WFv' := wfo_wf _ v'). revert u' H.
    induction WFv' as [v' _ HYPv'].
    econstructor; intros [u'' v''] LT''.
    destruct LT'', H0; simpl in *.
    + eapply HYPu; eauto using wfo_lt_le_lt.
    + eapply HYPv'; eauto using wfo_le_le_le.
Qed.
Next Obligation. split; simpl; eauto using wfo_non_negative. Qed.
Next Obligation.
  right. simpl. split; eauto using wfo_non_trivial, wfo_le_refl.
Qed.

(* **
  Lexicographic Product of Algebraic Wellfounded Orders
 *)

Definition lexprod_lt (a b : awfo) (x y: a * b) :=
  wfo_lt (fst x) (fst y) \/
  (wfo_le (fst x) (fst y) /\ wfo_lt (snd x) (snd y)).

Definition lexprod_le (a b : awfo) (x y: a * b) :=
  wfo_lt (fst x) (fst y) \/
  (wfo_le (fst x) (fst y) /\ wfo_le (snd x) (snd y)).

Program Definition awfo_lexprod (a b : awfo) : awfo :=
  {| wfo_lt   := lexprod_lt a b;
     wfo_le   := lexprod_le a b;
     wfo_zero := (wfo_zero, wfo_zero);
     wfo_one := (wfo_zero, wfo_one);
     wfo_add  := fun i j => (wfo_add (fst i) (fst j), wfo_add (snd i) (snd j));
  |}.
Next Obligation. red. eauto using wfo_add_zero_l_le. Qed.
Next Obligation. red. eauto using wfo_add_zero_l_ge. Qed.
Next Obligation. red. eauto using wfo_add_zero_r_le. Qed.
Next Obligation. red. eauto using wfo_add_zero_r_ge. Qed.
Next Obligation. red. eauto using wfo_add_assoc_le. Qed.
Next Obligation. red. eauto using wfo_add_assoc_ge. Qed.
Next Obligation. right. split; simpl; eauto using wfo_le_refl. Qed.
Next Obligation.
  destruct H as [|[]]; [left|right]; simpl in *; eauto using wfo_lt_le.
Qed.
Next Obligation.
  destruct H as [|[]], H0 as [|[]]; [..|right]; try left; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le.
Qed.
Next Obligation.
  destruct H as [|[]], H0 as [|[]]; [..|right]; try left; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le.
Qed.
Next Obligation.
  destruct H as [|[]], H0 as [|[]]; [..|right]; try left; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le.
Qed.
Next Obligation.
  destruct LE as [|[]]; [left|right]; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le, wfo_add_lt_left, wfo_add_le_left.
Qed.
Next Obligation.
  destruct LE as [|[]]; [left|right]; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le, wfo_add_lt_right, wfo_add_le_right.
Qed.
Next Obligation.
  destruct LT as [|[]]; [left|right]; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le, wfo_add_lt_left, wfo_add_le_left.
Qed.
Next Obligation.
  destruct LT as [|[]]; [left|right]; simpl in *; eauto using wfo_lt_le, wfo_lt_le_lt, wfo_le_lt_lt, wfo_le_le_le, wfo_add_lt_right, wfo_add_le_right.
Qed.
Next Obligation.
  intros [u v].
  assert (WFu := wfo_wf _ u). revert v.
  induction WFu as [u _ HYPu].
  econstructor; intros [u' v'] LT'.
  destruct LT' as [|[]]; simpl in *.
  - eapply HYPu in H; eauto.
  - clear v H0.
    assert (WFv' := wfo_wf _ v'). revert u' H.
    induction WFv' as [v' _ HYPv'].
    econstructor; intros [u'' v''] LT''.
    destruct LT'' as [|[]]; simpl in *.
    + eapply HYPu; eauto using wfo_lt_le_lt.
    + eapply HYPv'; eauto using wfo_le_le_le.
Qed.
Next Obligation. right. split; simpl; eauto using wfo_non_negative. Qed.
Next Obligation.
  right. simpl. eauto using wfo_non_trivial, wfo_le_refl.
Qed.

(* **
  Simple Properties about Orders
 *)

Lemma wfo_lt_neq: forall a i, ~ @wfo_lt a i i.
Proof.
  intros. assert (WF := wfo_wf a i). red.
  induction WF. eauto.
Qed.

Lemma wfo_add_monotone: forall (a: awfo) (i i' j j': a)
    (LEi: wfo_le i i')
    (LEj: wfo_le j j'),
  wfo_le (wfo_add i j) (wfo_add i' j').
Proof.
  eauto using wfo_le_le_le, wfo_add_le_left, wfo_add_le_right.
Qed.

Lemma wfo_add_proj_left: forall a i j, @wfo_le a i (wfo_add i j).
Proof.
  eauto using wfo_le_le_le, wfo_add_zero_r_ge, wfo_add_le_right, wfo_non_negative.
Qed.

Lemma wfo_add_proj_right: forall a i j, @wfo_le a j (wfo_add i j).
Proof.
  eauto using wfo_le_le_le, wfo_add_zero_l_ge, wfo_add_le_left, wfo_non_negative.
Qed.

Lemma wfo_add_one: forall (a: awfo) (i: a), wfo_lt i (wfo_add wfo_one i).
Proof.
  eauto using wfo_le_lt_lt, wfo_add_proj_right, wfo_add_lt_left, wfo_non_trivial.
Qed.

(** [wfo_le_n n o o'] means that [o'] can be decreased at least [n] times
    before reaching [o].
*)
Inductive wfo_le_n {o: awfo} : nat -> o -> o -> Prop :=
| wfo_le_n_Z i j (LE: wfo_le i j)
  : wfo_le_n O i j
| wfo_le_n_S n i j k (GLE: wfo_le_n n i j) (LT: wfo_lt j k)
  : wfo_le_n (S n) i k
.
Hint Constructors wfo_le_n.

Lemma wfo_le_n_lt: forall o n (i i': wfo_set o)
    (LE: wfo_le_n (S n) i i'),
  wfo_lt i i'.
Proof.
  induction n; intros; inversion LE; subst.
  - inversion GLE; subst. eauto using wfo_le_lt_lt.
  - apply IHn in GLE. eauto using wfo_lt_le, wfo_lt_le_lt.
Qed.

(* TODO rename (D) *)
Lemma wfo_le_n_S': forall o n (i i': wfo_set o)
    (LE: wfo_le_n (S n) i i'),
  exists j : wfo_set o,
    wfo_lt i j /\
    wfo_le_n n j i'.
Proof.
  induction n; intros; inversion LE; subst.
  - inversion GLE. subst. eauto using wfo_le_lt_lt, wfo_le_refl.
  - edestruct IHn; eauto.
    destruct H. eauto.
Qed.

Lemma wfo_le_n_S'': forall o n (i i': wfo_set o)
    (LE: wfo_le_n (S n) i i'),
  wfo_le_n n i i'.
Proof.
  intros; inversion LE; inversion GLE; subst; eauto using wfo_lt_le, wfo_le_le_le, wfo_lt_le_lt.
Qed.

Lemma wfo_le_n_wfo_le: forall o n (i i' i'': wfo_set o)
    (GLE: wfo_le_n n i i')
    (LE: wfo_le i' i''),
  wfo_le_n n i i''.
Proof.
  intros; dependent destruction GLE; [econstructor 1|econstructor 2]; eauto using wfo_le_le_le, wfo_lt_le_lt.
Qed.

Lemma wfo_le_n_anti: forall o m n (i i': wfo_set o)
    (GLE: wfo_le_n m i i')
    (LE: n <= m),
  wfo_le_n n i i'.
Proof.
  intros; ginduction LE; eauto.
  intros; apply IHLE; auto using wfo_le_n_S''.
Qed.

(* TODO rename *)
Lemma wfo_le_n_S_rev: forall o (i j: wfo_set o) n k
    (LT: wfo_lt i j)
    (GLE: wfo_le_n n j k),
  wfo_le_n (S n) i k.
Proof.
  intros; ginduction GLE; intros; eauto.
  econstructor; eauto using wfo_lt_le_lt, wfo_le_refl.
Qed.

Lemma wfo_le_n_plus: forall o n na nb (i i': wfo_set o)
    (GLE: wfo_le_n n i i')
    (E: n = na + nb),
  exists ii,
    wfo_le_n na i ii /\
    wfo_le_n nb ii i'.
Proof.
  intros; ginduction na; simpl; intros; subst.
  - exists i; eauto using wfo_le_refl.
  - apply wfo_le_n_S' in GLE. destruct GLE as [? [? LE]].
    eapply IHna in LE; eauto.
    destruct LE as [ii []].
    exists ii; eauto; split; eauto using wfo_le_n_S_rev.
Qed.

(* **
  wfo_nat
*)

Fixpoint wfo_nat {o : awfo} (n: nat) : wfo_set o :=
  match n with
  | 0 => wfo_zero
  | S n' => wfo_add wfo_one (wfo_nat n')
  end.

Lemma wfo_le_n_add: forall o n (i: wfo_set o),
  wfo_le_n n i (wfo_add (wfo_nat n) i).
Proof.
  induction n; eauto using wfo_add_lt_left, wfo_add_one, wfo_le_refl, wfo_add_proj_right.
Qed.

Lemma wfo_nat_le_mon: forall o n m
    (LE: n <= m),
  @wfo_le o (wfo_nat n) (wfo_nat m).
Proof.
  intros. induction LE; eauto using wfo_le_le_le, wfo_add_proj_right, wfo_le_refl.
Qed.

Lemma wfo_nat_lt_mon: forall o n m
    (LE: n < m),
  @wfo_lt o (wfo_nat n) (wfo_nat m).
Proof.
  intros; induction LE; eauto using wfo_lt_le_lt, wfo_lt_le, wfo_add_one.
Qed.


(* **
  General Wellfounded Order in NtNnWfPoMonoid
 *)

(* GWF List *)

Definition gwfL_set : Type := list (sigT bwfo_set).

Definition gwfLel (o: bwfo) (x: o) :=
  existT _ o x.

Program Definition unit_wfo : bwfo :=
  {| bwfo_set := unit;
     bwfo_lt _ _ := False;
     bwfo_le _ _ := True;
  |}.
Next Obligation. econstructor; intros. contradiction. Qed.

Definition gwfL_one : gwfL_set :=
  [ gwfLel unit_wfo tt ].

Inductive gwfL_lex (b: bool) : gwfL_set -> gwfL_set -> Prop :=
| gwfL_lex_nil
    (CHECK: is_true b)
  : gwfL_lex b [] []
| gwfL_lex_lt
    o x y i j
    (LT: bwfo_lt x y)
    (LEN: length i = length j)
  : gwfL_lex b (gwfLel o x :: i) (gwfLel o y :: j)
| gwfL_lex_step
    o x y i j
    (LE: bwfo_le x y)
    (CMP: gwfL_lex b i j)
  : gwfL_lex b (gwfLel o x :: i) (gwfLel o y :: j)
.
Hint Constructors gwfL_lex.

Variant gwfL_cmp b : gwfL_set -> gwfL_set -> Prop :=
| gwfL_cmp_lt
    o1 o2
    (LEN: length o1 < length o2)
  : gwfL_cmp b o1 o2
| gwfL_cmp_lex
    i j
    (CMP: gwfL_lex b i j)
  : gwfL_cmp b i j
.
Hint Constructors gwfL_cmp.

Lemma gwfL_lex_length b o1 o2
      (LT: gwfL_lex b o1 o2)
  : length o1 = length o2.
Proof.
  intros. induction LT; simpl; nia.
Qed.

Lemma gwfL_cmp_length b o1 o2
      (CMP: gwfL_cmp b o1 o2)
  : length o1 <= length o2.
Proof.
  destruct CMP.
  - nia.
  - erewrite gwfL_lex_length; eauto.
Qed.

Lemma gwfL_lex_refl: forall i, gwfL_lex true i i.
Proof.
  induction i; eauto.
  destruct a. eapply gwfL_lex_step; eauto using bwfo_le_refl.
Qed.

Lemma gwfL_le_refl: forall i, gwfL_cmp true i i.
Proof.
  intros. apply gwfL_cmp_lex. eauto using gwfL_lex_refl.
Qed.

Lemma gwfL_lex_lt_le: forall i j, gwfL_lex false i j -> gwfL_lex true i j.
Proof.
  intros. induction H; eauto.
Qed.

Lemma gwfL_lt_le: forall i j, gwfL_cmp false i j -> gwfL_cmp true i j.
Proof.
  intros. destruct H; eauto using gwfL_lex_lt_le.
Qed.

Lemma gwfL_lex_trans b1 b2 b3 i j k
      (COND: is_true (b1 && b2) -> is_true b3)
      (CMP1: gwfL_lex b1 i j)
      (CMP2: gwfL_lex b2 j k)
  : gwfL_lex b3 i k.
Proof.
  ginduction CMP2; intros.
  - inversion CMP1; subst. destruct b1, b2, b3; eauto.
  - dependent destruction CMP1.
    + eapply gwfL_lex_lt; eauto using bwfo_le_lt_lt, bwfo_lt_le.
      nia.
    + eapply gwfL_lex_lt; eauto using bwfo_le_lt_lt.
      apply gwfL_lex_length in CMP1. nia.
  - dependent destruction CMP1.
    + eapply gwfL_lex_lt; eauto using bwfo_lt_le_lt.
      apply gwfL_lex_length in CMP2. nia.
    + eapply gwfL_lex_step; eauto using bwfo_le_le_le.
Qed.

Lemma gwfL_cmp_trans b1 b2 b3 i j k
      (CMP1: gwfL_cmp b1 i j)
      (CMP2: gwfL_cmp b2 j k)
      (COND: is_true (b1 && b2) -> is_true b3)
  : gwfL_cmp b3 i k.
Proof.
  assert (LE1 := gwfL_cmp_length CMP1).
  assert (LE2 := gwfL_cmp_length CMP2).
  destruct CMP1, CMP2; eauto using gwfL_lex_trans; apply gwfL_cmp_lt; nia.
Qed.

Lemma gwfL_add_cmp_left b: forall i i' j (LE: gwfL_cmp b i i'), gwfL_cmp b (i ++ j) (i' ++ j).
Proof.
  intros. inversion LE; subst.
  - apply gwfL_cmp_lt. rewrite !app_length. nia.
  - apply gwfL_cmp_lex.
    induction CMP; simpl.
    + destruct b; inversion CHECK. eauto using gwfL_lex_refl.
    + apply gwfL_lex_lt; eauto.
      rewrite !app_length. nia.
    + apply gwfL_lex_step; eauto.
Qed.

Lemma gwfL_add_cmp_right b: forall i j j' (LE: gwfL_cmp b j j'), gwfL_cmp b (i ++ j) (i ++ j').
Proof.
  intros. inversion LE; subst.
  - apply gwfL_cmp_lt. rewrite !app_length. nia.
  - apply gwfL_cmp_lex.
    ginduction CMP; simpl; intros.
    + destruct b; inversion CHECK. eauto using gwfL_lex_refl.
    + induction i0; simpl; eauto.
      destruct a; eauto using bwfo_le_refl.
    + induction i0; simpl; eauto.
      destruct a; eauto using bwfo_le_refl.
Qed.

Lemma gwfL_acc_le: forall i j (WF: Acc (gwfL_cmp false) i) (LE: gwfL_cmp true j i),
    Acc (gwfL_cmp false) j.
Proof.
  econstructor. intros. eapply WF. eauto using gwfL_cmp_trans.
Qed.

Lemma gwfL_lt_bottom: forall i, gwfL_cmp false i [] -> False.
Proof.
  intros. inversion H; subst.
  - inversion LEN.
  - inversion CMP. inversion CHECK.
Qed.

Lemma gwfL_wf: well_founded (gwfL_cmp false).
Proof.
  cut (forall n i (LEon: length i <= n), Acc (gwfL_cmp false) i).
  { red; eauto. }

  induction n; intros.
  { destruct i; inversion LEon.
    econstructor. intros. exfalso. eauto using gwfL_lt_bottom. }
  destruct i.
  { econstructor. intros. exfalso. eauto using gwfL_lt_bottom. }

  destruct s as [o x]. revert i LEon. simpl.
  assert (WFx := bwfo_wf _ x).
  induction WFx as [x _ HYPx].
  econstructor. intros j LTj.
  dependent destruction LTj.
  { simpl in *. eapply IHn. nia. }
  dependent destruction CMP.
  { eapply HYPx; eauto. nia. }

  assert (WF: Acc (gwfL_cmp false) i0).
  { apply gwfL_lex_length in CMP. eapply IHn. nia. }
  revert x0 LE. induction WF as [j _ HYPj].
  econstructor. intros k LTk.
  assert (LEN := gwfL_lex_length CMP).
  dependent destruction LTk.
  { simpl in *. eapply IHn. nia. }
  dependent destruction CMP0.
  { eapply HYPx; eauto using bwfo_lt_le_lt. nia. }
  eapply HYPj; eauto using bwfo_le_le_le.
  eapply gwfL_lex_trans; eauto; eauto.
Qed.

Program Definition gwfLo : awfo :=
  {| wfo_set     := gwfL_set;
     wfo_le x y  := gwfL_cmp true x y;
     wfo_lt x y  := gwfL_cmp false x y;
     wfo_zero    := nil;
     wfo_one     := gwfL_one;
     wfo_add x y := x ++ y;
  |}.
Next Obligation. eauto using gwfL_le_refl. Qed.
Next Obligation. eauto using gwfL_le_refl. Qed.
Next Obligation. rewrite app_nil_r. eauto using gwfL_le_refl. Qed.
Next Obligation. rewrite app_nil_r. eauto using gwfL_le_refl. Qed.
Next Obligation. rewrite app_assoc. eauto using gwfL_le_refl. Qed.
Next Obligation. rewrite app_assoc. eauto using gwfL_le_refl. Qed.
Next Obligation. eauto using gwfL_le_refl. Qed.
Next Obligation. eauto using gwfL_lt_le. Qed.
Next Obligation. eauto using gwfL_cmp_trans. Qed.
Next Obligation. eauto using gwfL_cmp_trans. Qed.
Next Obligation. eauto using gwfL_cmp_trans. Qed.
Next Obligation. eauto using gwfL_add_cmp_left. Qed.
Next Obligation. eauto using gwfL_add_cmp_right. Qed.
Next Obligation. eauto using gwfL_add_cmp_left. Qed.
Next Obligation. eauto using gwfL_add_cmp_right. Qed.
Next Obligation. eauto using gwfL_wf. Qed.
Next Obligation. destruct i; eauto. econstructor. simpl. nia. Qed.

(* **
   embedding and properties
 *)

Definition gwfL_embed {o: bwfo} (a: o) : gwfLo :=
  [ gwfLel o a ].

Lemma gwfL_embed_le_preserve (o: bwfo) (a b: o)
      (LT: bwfo_le a b):
  wfo_le (gwfL_embed a) (gwfL_embed b).
Proof.
  repeat red. unfold gwfL_embed. eauto.
Qed.

Lemma gwfL_embed_lt_preserve (o: bwfo) (a b: o)
      (LT: bwfo_lt a b):
  wfo_lt (gwfL_embed a) (gwfL_embed b).
Proof.
  repeat red. unfold gwfL_embed. eauto.
Qed.

Lemma gwfL_embed_le_reflect (o: bwfo) (a b: o)
    (LT: wfo_le (gwfL_embed a) (gwfL_embed b)):
  bwfo_le a b.
Proof.
  repeat red in LT. unfold gwfL_embed in *. dependent destruction LT; eauto.
  - simpl in *. nia.
  - dependent destruction CMP; eauto using bwfo_lt_le.
Qed.

Lemma gwfL_embed_lt_reflect (o: bwfo) (a b: o)
    (LT: wfo_lt (gwfL_embed a) (gwfL_embed b)):
  bwfo_lt a b.
Proof.
  repeat red in LT. unfold gwfL_embed in *. dependent destruction LT; eauto.
  - simpl in *. nia.
  - dependent destruction CMP; eauto.
    inversion CMP. inversion CHECK.
Qed.

(* GWF *)

Definition gwfo := awfo_lexprod gwfLo gwfLo.

Definition gwf_embed {o: bwfo} (a: o) : gwfo :=
  (wfo_zero, gwfL_embed a).

Lemma gwf_embed_le_preserve (o: bwfo) (a b: o)
      (LT: bwfo_le a b):
  wfo_le (gwf_embed a) (gwf_embed b).
Proof.
  econstructor 2. simpl. split; eauto.
  eapply gwfL_embed_le_preserve; eauto.
Qed.

Lemma gwf_embed_lt_preserve (o: bwfo) (a b: o)
      (LT: bwfo_lt a b):
  wfo_lt (gwf_embed a) (gwf_embed b).
Proof.
  econstructor 2. simpl. split; eauto.
  eapply gwfL_embed_lt_preserve; eauto.
Qed.

Lemma gwf_embed_le_reflect (o: bwfo) (a b: o)
    (LT: wfo_le (gwf_embed a) (gwf_embed b)):
  bwfo_le a b.
Proof.
  eapply gwfL_embed_le_reflect.
  inversion LT.
  - simpl in *. exfalso. eauto using gwfL_lt_bottom.
  - destruct H. eauto.
Qed.

Lemma gwf_embed_lt_reflect (o: bwfo) (a b: o)
    (LT: wfo_lt (gwf_embed a) (gwf_embed b)):
  bwfo_lt a b.
Proof.
  eapply gwfL_embed_lt_reflect.
  inversion LT.
  - simpl in *. exfalso. eauto using gwfL_lt_bottom.
  - destruct H. eauto.
Qed.

