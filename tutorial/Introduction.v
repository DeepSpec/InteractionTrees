(** * Introduction to interaction trees *)

(** This file gives and example of defining recursive functions
    using ITrees. It demonstrates
    - [rec]
    - equational reasoning using [≈] ([\approx])
*)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Arith
     Setoid
     RelationClasses
     Program
     Morphisms
     Lia.

From ExtLib Require Import
     Monad.

From ITree Require Import
     Simple.

Import ITreeNotations.
Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** In this file, we won't use external effects, so we will use this
    empty effect type [void1]. *)
Definition E := void1.

(** ** Factorial *)

(** This is the Coq specification -- the usual mathematical definition. *)
Fixpoint factorial_spec (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * factorial_spec m
  end.

(** The generic [rec] interface of the library's [Interp] module can
    be used to define a single recursive function.  The more general
    [mrec] (from which [rec] is defined) allows multiple, mutually
    recursive definitions.

    The argument of [rec] is an interaction tree with an effect
    [callE A B] to represent "recursive calls", with input [A]
    and output [B]. The function [call : A -> itree _ B] can be used
    to make such calls.

    In this case, since [factorial : nat -> nat], we use
    [callE nat nat].
 *)
Definition fact_body (x : nat) : itree (callE nat nat +' E) nat :=
  match x with
  | 0 => Ret 1
  | S m =>
    y <- call m ;;  (* Recursively compute [y := m!] *)
    Ret (x * y)
  end.

(** The factorial function itself is defined as an itree by "tying
    the knot" using [rec].
 *)
Definition factorial (n : nat) : itree E nat :=
  rec fact_body n.

(** Contrary to definitions by [Fixpoint], there are no restrictions
    on the arguments of recursive calls: [rec] may thus produce
    diverging computations, and Coq will not naively reduce
    [factorial 5].

    Of course, we can force the computation with fuel, e.g.,
    using [burn]...
 *)
Compute (burn 100 (factorial 5)).

(** ... or with tactics, such as [tau_steps], which removes
    all taus from the left-hand side of an [≈] equation. *)
Example fact_5 : factorial 5 ≈ Ret 120.
Proof.
  tau_steps.
  reflexivity.
Qed.

(** An equivalent definition with a [rec-fix] notation looking like
    [fix], where the recursive call can be given a more specific name.
 *)
Definition factorial' : nat -> itree E nat :=
  rec-fix fact x :=
    match x with
    | 0 => Ret 1
    | S m => y <- fact m ;; Ret (x * y)
    end.

(** These two definitions are definitionally equal. *)
Lemma factorial_same : factorial = factorial'.
Proof. reflexivity. Qed.

(** We can prove that the ITrees version [factorial] is "equivalent"
    to the [factorial_spec] version.  The proof goes by induction on
    [n] and uses only rewriting -- no coinduction necessary.

    Here, we detail each step of rewriting to illustrate the use of
    the equational theory, which is mostly applications of the monad
    laws and the properties of [rec].

    In this proof, we do all of the rewriting steps explicitly.
 *)
Lemma factorial_correct : forall n,
    factorial n ≈ Ret (factorial_spec n).
Proof.
  intros n.
  unfold factorial.
  induction n as [ | n' IH ].
  - (* n = 0 *)
    rewrite rec_as_interp. simpl.
    rewrite interp_ret.
    reflexivity.
  - (* n = S n' *)
    rewrite rec_as_interp. simpl.
    rewrite interp_bind.
    rewrite interp_recursive_call.
    rewrite IH.                   (* Induction hypothesis *)
    rewrite bind_ret.
    rewrite interp_ret.
    reflexivity.
Qed.

(** The tactics [tau_steps] and [autorewrite with itree] offer
    a little automation to simplify monadic expressions. *)
Lemma factorial_correct' : forall n,
    factorial n ≈ Ret (factorial_spec n).
Proof.
  intros n.
  unfold factorial.
  induction n as [ | n' IH ].
  - (* n = 0 *)
    tau_steps. (* Just compute away. *)
    reflexivity.
  - (* n = S n' *)
    rewrite rec_as_interp.
    unfold fact_body at 2.
    autorewrite with itree.
    rewrite IH.             (* Induction hypothesis *)
    autorewrite with itree.
    reflexivity.
Qed.

(** ** Fibonacci *)

(** Exercise *)
(** Carry out the analogous proof of correctness for the Fibonacci
    function, whose naturally recursive coq definition is given below.
 *)

Fixpoint fib_spec (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib_spec n'' + fib_spec n'
    end
  end.

Definition fib_body : nat -> itree (callE nat nat +' E) nat :=
(* SOLN *)  
  fun n =>
    match n with
    | 0 => Ret 0
    | S n' =>
      match n' with
      | 0 => Ret 1
      | S n'' =>
        y1 <- call n'' ;;
        y2 <- call n' ;;
        Ret (y1 + y2)
      end
    end.
(* STUBWITH (fun n => Ret 0) *)

Definition fib n : itree E nat :=
  rec fib_body n.

(** Since fib uses two recursive calls, we need to strengthen the
    induction hypothesis.  One way to do that is to prove the
    property for all [m <= n].

    You may find the following two lemmas useful at the start
    of each case.
[[
Nat.le_0_r : forall n : nat, n <= 0 <-> n = 0
Nat.le_succ_r : forall n m : nat, n <= S m <-> n <= m \/ n = S m
]]
 *)

Lemma fib_correct : forall n m, m <= n ->
    fib m ≈ Ret (fib_spec m).
Proof.
(* SOLN *)  
  intros n.
  unfold fib.
  induction n as [ | n' IH ]; intros.
  - (* n = 0 *)
    apply Nat.le_0_r in H. subst m.
    unfold fib.
    rewrite rec_as_interp. simpl.
    rewrite interp_ret.
    (* alternatively, [tau_steps], or [autorewrite with itree] *)
    reflexivity.
  - (* n = S n' *)
    apply Nat.le_succ_r in H.
    destruct H.
    + apply IH; auto.
    + rewrite rec_as_interp.
      subst m. simpl.
      destruct n' as [ | n'' ].
      * rewrite interp_ret. reflexivity.
      * autorewrite with itree.
        rewrite IH. 2: lia.
        autorewrite with itree.
        rewrite IH. 2: lia.
        autorewrite with itree.
        reflexivity.
Qed.
(* STUBWITH Admitted. *)

(** ** Logarithm *)

(** An example of a function which is not structurally recursive:
    logarithm in base [b].
 *)

Definition log_ (b : nat) : nat -> itree E nat :=
  rec-fix log_b n :=
    if n <=? 1 then
      Ret O
    else
      y <- log_b (n / b) ;; Ret (S y).

Example log_2_64 : log_ 2 (2 ^ 6) ≈ Ret 6.
Proof.
  tau_steps.
  reflexivity.
Qed.

(** We can prove that [log_ b (b ^ y) ≈ Ret y] when [1 < b]. *)

(** These lemmas take care of the boring arithmetic. *)
Lemma log_correct_helper :
  forall b y, 1 < b ->
              (b * b ^ y <=? 1) = false.
Proof.
  intros.
  apply Nat.leb_gt.
  apply Nat.lt_1_mul_pos; auto.
  apply neq_0_lt. intro.
  apply (Nat.pow_nonzero b y); lia.
Qed.

Lemma log_correct_helper2 :
  forall b y, 1 < b ->
              (b * b ^ y / b) = (b ^ y).
Proof.
  intros; rewrite Nat.mul_comm, Nat.div_mul; lia.
Qed.

Lemma log_correct : forall b y, 1 < b -> log_ b (b ^ y) ≈ Ret y.
Proof.
  intros b y H.
  unfold log_, rec_fix.
  induction y.
  - rewrite rec_as_interp; cbn.
    autorewrite with itree.
    reflexivity.
  - rewrite rec_as_interp; cbn.
    (* (b * b ^ y <=? 1) = false *)
    rewrite log_correct_helper by auto.
    autorewrite with itree.
    (* (b * b ^ y / b) = (b ^ y)*)
    rewrite log_correct_helper2 by auto.
    rewrite IHy.
    autorewrite with itree.
    reflexivity.
Qed.
