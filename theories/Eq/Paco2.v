(** Redefinition of [pcofix] and [pcofix] without using the [JMeq_eq] axiom.
Both tactics are now called [pcofix]. The same core is reused to define [ecofix]
in [Eq.UpToTaus]. *)

From Paco Require Import paco.

Ltac debug_goal :=
  match goal with
  | [ |- ?G ] => idtac G
  end.

(* A variant of [paco2_acc] that is more convenient to use in the [pcofix] tactic. *)
Lemma paco2_accF
  : forall {T0 : Type} {T1 : forall a : T0, Type}
      (gf : rel2 T0 T1 -> rel2 T0 T1) (r : rel2 T0 T1)
      (X : Type)
      (f0 : X -> T0) (f1 : forall x : X, T1 (f0 x)),
      (forall rr : rel2 T0 T1,
        (forall a0 a1, r a0 a1 -> rr a0 a1) ->
        (forall x, rr (f0 x) (f1 x)) ->
        forall x : X, paco2 gf rr (f0 x) (f1 x)) ->
      forall x : X, paco2 gf r (f0 x) (f1 x).
Proof.
  intros.
  apply paco2_acc with
    (l := fun a0 (a1 : T1 a0) => exists x, existT _ (f0 x) (f1 x) = existT _ a0 a1); [ | eauto ].
  intros. change (paco2 gf rr (projT1 (existT _ _ x1)) (projT2 (existT _ _ x1))).
  destruct PR as [? <-].
  eauto.
Qed.

Lemma gpaco2_accF
  : forall {T0 : Type} {T1 : forall a : T0, Type}
      (gf : rel2 T0 T1 -> rel2 T0 T1),
      monotone2 gf ->
    forall (clo : rel2 T0 T1 -> rel2 T0 T1) (r rg : rel2 T0 T1)
      (X : Type)
      (f0 : X -> T0) (f1 : forall x : X, T1 (f0 x))
      (OBG : forall rr : rel2 T0 T1,
        (forall x y, rg x y -> rr x y) ->
        (forall x, rr (f0 x) (f1 x)) ->
        forall x : X, gpaco2 gf clo r rr (f0 x) (f1 x)),
      forall x : X, gpaco2 gf clo r rg (f0 x) (f1 x).
Proof.
  intros.
  apply gpaco2_cofix with
    (l := fun a0 (a1 : T1 a0) => exists x, existT _ (f0 x) (f1 x) = existT _ a0 a1); [ eauto | | eauto ].
  intros. change (gpaco2 gf clo r rr (projT1 (existT _ _ x1)) (projT2 (existT _ _ x1))).
  destruct PR as [? <-].
  eauto.
Qed.

Ltac apply_paco_acc self unpack_goal unpack_hyp :=
  let unpack _tt :=
    let r := fresh "r" in
    let self_ := fresh "_tmp_" self in
    let self := fresh self in
    intros r self_ self;
    let self1 := fresh self in
    rename self_ into self1;
    unpack_goal tt;
    unpack_hyp self in
  lazymatch goal with
  | [ |- forall _, paco2 ?gf ?r0 _ _ ] => apply paco2_accF; unpack tt
  | [ |- forall _, gpaco2 ?gf ?clo _ _ _ _ ] => apply gpaco2_accF; [ eauto with paco | unpack tt ]
  (* TODO: other arities *)
  | _ => fail "paco not found at the head of the goal"
  end.

Lemma curry_sig {A : Type} {P : A -> Type} {Q : forall (a : A) (b : P a), Prop}
  : (forall x : sigT P, Q (projT1 x) (projT2 x)) -> forall (a : A) (p : P a), Q a p.
Proof.
  exact (fun H a p => H (existT _ a p)).
Qed.

(* [pcofix self]: Apply coinduction to a goal with [paco] at the head of the conclusion
   (possibly after unfolding definitions).
   The parameter [self] is the name of the coinduction hypothesis. *)

(* Internal definition of [pcofix_]:
Example initial goal:
<<
===========
forall (x : X) (y : Y), hyp x y -> paco2 gf bot2 (f0 x y) (f1 x y)
>>
   1. [pcofix_] first recursively introduces all hypotheses [H], being careful to
      preserve existing names, and at the same time builds up continuations
      to process the goal once we reach the conclusion. This technique has the
      benefit that the name of each hypothesis is available, so it does
      not need to be guessed repeatedly.
Goal after step 1:
<<
x : X
y : Y
H : hyp x y
===========
paco2 gf bot2 (f0 x y) (f1 x y)
>>
   2. Having reached the conclusion, we use the [pack_goal0] continuation to
      regeneralize the hypotheses we introduced into a single sigma type
      (a chain of [{_ & _}]/[sigT]),
Goal after step 2:
<<
===========
forall (u : {x : X & {y : Y & {_ : hyp x y & unit}}}),
  paco2 gf bot2 (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
>>
   3. We can now apply [paco2_accF] (depending on the arity of paco)
Goal after step 3:
<<
r : rel2 T0 T1
_pacotmp_SELF: forall (u : _), r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
==========
forall (u : {x : X & {y : Y & {_ : hyp x y & unit}}}),
  paco2 gf r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
>>
   4. We decompose the tuple in the goal using the [unpack_goal0] continuation
      (basically the reverse of [pack_goal0]) and [revert_tmp0].
Goal after step 4:
<<
r : rel2 T0 T1
_pacotmp_SELF: forall (u : _), r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
==========
forall x y, hyp x y -> paco2 gf r (f0 x y) (f1 x y)
>>
   5. We decompose the tuple in the coinduction hypothesis
Goal after step 5:
<<
r : rel2 T0 T1
SELF: forall x y, hyp x y -> r (f0 x y) (f1 x y)
==========
forall x y, hyp x y -> paco2 gf r (f0 x y) (f1 x y)
>>
tODO: Currently this step does not preserve variable names,
so the actual hypothesis looks more like this:
<<
SELF: forall x0 x1, hyp x0 x1 -> r (f0 x0 x1) (f1 x0 x1)
>>
*)
Ltac pcofix_ apply_paco_acc0 pack_goal0 unpack_goal0 revert_tmp0 unpack_hyp0 :=
  hnf;
  lazymatch goal with
  | [ |- forall H : ?X, _ ] =>
    (* 1. *)
    let H := fresh H in
    intros H;
    let pack_goal := (revert H; apply curry_sig; pack_goal0) in
    let unpack_goal H0 := ltac:(unpack_goal0 H0; destruct H0 as [H H0]; cbn [projT1 projT2]) in
    let revert_tmp := revert H; revert_tmp0 in
    let unpack_hyp tmp_self :=
      intros H;
      let tmp := fresh tmp_self in
      rename tmp_self into tmp;
      assert (tmp_self := fun TMP => tmp (existT _ H TMP));
      clear tmp;
      unpack_hyp0 tmp_self in
    pcofix_ apply_paco_acc0 pack_goal unpack_goal revert_tmp unpack_hyp
  | _ =>
    let (* 4 *) unpack_goal _tt :=
      let tmp_H0 := fresh "_pacotmp_" in
      intros tmp_H0; unpack_goal0 tmp_H0; clear tmp_H0;
      revert_tmp0 in
    let (* 5 *) unpack_hyp HYP :=
      let tmp_prop := fresh HYP "_prop_" in
      let tmp_hyp := fresh HYP "_v_" in
      evar (tmp_prop : Prop); assert (tmp_hyp : tmp_prop); subst tmp_prop;
        [ unpack_hyp0 HYP; cbn in HYP; exact (HYP tt)
        | clear HYP ];
      try rename tmp_hyp into HYP in
    (* 2. pack_goal *) assert (tmp_H0 := tt); revert tmp_H0; pack_goal0;
    (* 3. paco_acc *) apply_paco_acc0 unpack_goal unpack_hyp
  end.

Ltac pcofix_with apply_paco_acc0 :=
  let pack_goal0 := idtac in
  let unpack_goal0 _ := idtac in
  let revert_tmp0 := idtac in
  let unpack_hyp0 _ := idtac in
  pcofix_ apply_paco_acc0 pack_goal0 unpack_goal0 revert_tmp0 unpack_hyp0.

Tactic Notation "pcofix" ident(self) :=
  pcofix_with ltac:(apply_paco_acc self).
