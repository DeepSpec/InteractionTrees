(** * Introduction to interaction trees *)

(** This file contains exercises to get familiar with the
    Interaction Trees library, via the simplified
    interface of [theories/ITree/Simple.v].

    The solutions can be found in [examples/Introduction.v].
 *)

(* begin hide *)
From Coq Require Import
     Arith
     Lia
     List.

From ExtLib Require Import
     Monad
     Traversable
     Data.List.

From ITree Require Import
     Simple.

Import ListNotations.
Import ITreeNotations.
Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Effects *)

(** We first show how to represent effectful computations
    as interaction trees. The [itree] type is parameterized
    by a type of "uninterpreted effects", which is typically
    an indexed type with constructors describing the possible
    interactions with the environment.

    For instance, [ioE] below is a type of simple input/output
    effects. The fields of each constructor contain data produced
    by the tree, and the type index the type of answer that the
    tree expects as a result of the effect.
 *)

Inductive ioE : Type -> Type :=
| Input : ioE (list nat)
  (** Ask for a list of [nat] from the environment. *)

| Output : list nat -> ioE unit
  (** Send a list of [nat]. *)
.

(** Effects are wrapped as itrees using [ITree.lift], and
    composed using monadic operations [bind] and [ret]. *)

(** Read some input, and echo it back, appending [1] to it. *)
Definition write_one : itree ioE unit :=
  xs <- ITree.lift Input;;
  ITree.lift (Output (xs ++ [1])).

(** We can _interpret_ interaction trees by giving semantics
    to their effects individually, as a _handler_: a function
    of type [forall R, ioE R -> M R] for some monad [M]. *)

(** The handler [handle_io] below responds to every [Input] effect
    with [[0]], and appends any [Output] to a global log.

    Here the target monad is [M := stateT (list nat) (itree void1)],
    - [stateT] is the state monad transformer, that type unfolds to
      [M R := list nat -> itree void1 (list nat * R)];
    - [void1] is the empty effect (so the resulting itree can perform
      no effect). *)

Compute Monads.stateT (list nat) (itree void1) unit.
Print void1.

Definition handle_io
  : forall R, ioE R -> Monads.stateT (list nat) (itree void1) R
  := fun R e log =>
       match e with
       | Input => ret (log, [0])
       | Output o => ret (log ++ o, tt)
       end.

(** [interp] lifts any handler into an _interpreter_, of type
    [forall R, itree ioE R -> M R]. *)
Definition interp_io
  : forall R, itree ioE R -> itree void1 (list nat * R)
  := fun R t => interp handle_io R t [].

(** We can now interpret [write_one]. *)
Definition interpreted_write_one : itree void1 (list nat * unit)
  := interp_io _ write_one.

(** Intuitively, [interp_io] replaces every [ITree.lift] in the
    definition of [write_one] with [handle_io]:
[[
  interpreted_write_one :=
    xs <- handle_io _ Input;;
    handle_io _ (Output (xs ++ [1]))
]]
 *)

(** An [itree void1] is a computation which can either return a value,
    or loop infinitely. Since Coq is total, [interpreted_write_one]
    will not be reduced naively.

    Instead, we can force computation with fuel, using [burn]:
 *)
Compute (burn 100 interpreted_write_one).

(** * General recursion with interaction trees *)

(** We give examples of defining recursive functions using ITrees,
    demonstrating:
    - [rec]
    - equational reasoning using [≈] ([\approx])
*)

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

(** *** Evaluation *)

(** Contrary to definitions by [Fixpoint], there are no restrictions
    on the arguments of recursive calls: [rec] may thus produce
    diverging computations, and Coq will not naively reduce
    [factorial 5].

    We can force the computation with fuel, e.g., using [burn]...
 *)
Compute (burn 100 (factorial 5)).

(** ... or with tactics, such as [tau_steps], which removes
    all taus from the left-hand side of an [≈] equation. *)
Example fact_5 : factorial 5 ≈ Ret 120.
Proof.
  tau_steps. reflexivity.
Qed.

(** *** Alternative notation *)

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

(** *** Correctness *)

(** [rec] is actually a special version of [interp], which replaces
    every [call] in [fact_body] with [factorial] itself.
 *)
Lemma unfold_factorial : forall x,
    factorial x ≈ match x with
                  | 0 => Ret 1
                  | S m =>
                    y <- factorial m ;;
                    Ret (x * y)
                  end.
Proof.
  intros x.
  unfold factorial.
  rewrite rec_as_interp; unfold fact_body at 2.
  destruct x.
  - rewrite interp_ret.
    reflexivity.
  - rewrite interp_bind.
    rewrite interp_recursive_call.
    setoid_rewrite interp_ret.
    reflexivity.
Qed.

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
  induction n as [ | n' IH ].
  - (* n = 0 *)
    (* FILL IN HERE *) admit.
  - (* n = S n' *)
    (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.

(** ** Fibonacci *)

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

Definition fib_body : nat -> itree (callE nat nat +' E) nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition fib n : itree E nat :=
  rec fib_body n.

Example fib_3_6 : mapT fib [4;5;6] ≈ Ret [3; 5; 8].
Proof.
  (* 
  tau_steps. reflexivity.
  *)
(* FILL IN HERE *) Admitted.

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

Lemma fib_correct_aux : forall n m, m <= n ->
    fib m ≈ Ret (fib_spec m).
Proof.
  intros n.
  unfold fib.
  induction n as [ | n' IH ]; intros.
  - (* n = 0 *)
    apply Nat.le_0_r in H. subst m.
    (* FILL IN HERE *) admit.
  - (* n = S n' *)
    apply Nat.le_succ_r in H.
    (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.

(** ** Logarithm *)

(** An example of a function which is not structurally recursive.
    [log_ b n]: logarithm of [n] in base [b].
    Note that this diverges if [n > 1] and [b = 0].
 *)

Definition log (b : nat) : nat -> itree E nat :=
  rec-fix log_b n :=
    if n <=? 1 then
      Ret O
    else
      y <- log_b (n / b) ;; Ret (S y).

Example log_2_64 : log 2 (2 ^ 6) ≈ Ret 6.
Proof.
  tau_steps. reflexivity.
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

Lemma log_correct : forall b y, 1 < b -> log b (b ^ y) ≈ Ret y.
Proof.
  intros b y H.
  unfold log, rec_fix.
  induction y.
  - (* FILL IN HERE *) admit.
  - (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.