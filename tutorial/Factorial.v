(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Nat
     Setoid
     RelationClasses
     Program
     Morphisms.

From ExtLib Require Import
     Monad.

From ITree Require Import
     Simple.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

Definition E := void1.

(** * Factorial Example *)

(** * Factorial *)

(** This file gives and example of defining a recursive version of the "factorial" 
    function using ITrees. It demonstrates
       - [rec]
       - equational reasoning using ≈
*)

(** The generic [rec] interface of the library's [Interp] module can be used to
    define a single recursive function.  The more general [mrec] (from which [rec] is defined)
    allows multiple, mutually recursive definitions.

    To use [rec], we instantiate the generic "recursive" call event [callE] at the 
    desired type.  In this case, since, [factorial : nat -> nat], we use [callE nat nat].
*)

(** [factC] is an event representing the recursive call.  Since in general, the 
    function might have other effects of type [E], the resulting itree has 
    type [(callE nat nat +' E)].  [factC] simply injects the argument [n] into the 
    event.
 *)

(** We write the body of the function monadically, using events rather than recursive calls. *)
Definition fact_body (x : nat) : itree (callE nat nat +' E) nat :=
  match x with
  | 0 => Ret 1
  | S m => y <- call m ;; Ret (x * y)
  end.

(** The factorial function itself is defined as an itree by 'tying the knot' using [rec]. 

    (Aside: Note that [factorial] is actually a [KTree] of type [ktree nat nat].)
*)
Definition factorial (n : nat) : itree E nat :=
  rec fact_body n.

Example fact_5 : exists y, factorial 5 ≈ Ret y.
Proof.
  eexists.
  tau_steps.
  reflexivity.
Qed.

(** An equivalent definition with a [rec-fix] notation looking like [fix].
 *)
Definition factorial' : nat -> itree E nat :=
  rec-fix fact x :=
    match x with
    | 0 => Ret 1
    | S m => y <- fact m ;; Ret (x * y)
    end.

Lemma factorial_same : factorial = factorial'.
Proof. reflexivity. Qed.

(** This is the Coq specification -- the usual mathematical definition. *)
Fixpoint factorial_spec (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * factorial_spec m
  end.

(** We can prove that the ITrees version [factorial] is "equivalent" to the
    [factorial_spec] version.  The proof goes by induction on n and uses only
    rewriting -- no coinduction necessary. Here, we step through each step of
    rewriting to illustrate the use of the equational theory, which is mostly
    applications of the monad laws and the properties of [rec], seen as an 
    instance of [mrec]. 

    In this proof, we do all of the rewriting steps explicitly.
*)
Lemma factorial_correct : forall n, factorial n ≈ Ret (factorial_spec n).
Proof.
  intros n.
  induction n; intros; subst.
  - unfold factorial. rewrite rec_as_interp. simpl. rewrite ret_interp. reflexivity.
  - unfold factorial. rewrite rec_as_interp. simpl.
    rewrite interp_bind.
    rewrite interp_recursive_call.
    rewrite IHn.
    rewrite ret_bind.
    rewrite ret_interp.
    reflexivity.
Qed.

(** * Fibonacci *)

(** Exercise *)
(** Carry out the analogous proof of correctness for the Fibonacci function, whose
    naturally recursive coq definition is given below. *)

Fixpoint fib_spec (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m =>
    match m with
    | 0 => 1
    | S k => fib_spec m + fib_spec k
    end
  end.

(** We write the body of the fib monadically, using events rather than recursive calls. *)
Definition fib_body : nat -> itree (callE nat nat +' E) nat :=
(* SOLN *)  
  fun x => match x with
        | 0 => Ret 1
        | S m =>
          match m with
          | 0 => Ret 1
          | S k => y1 <- call m ;;
                  y2 <- call k ;;
                  Ret (y1 + y2)
          end
        end.
(* STUBWITH Ret 0 *)

Require Import Omega.

Definition fib n : itree E nat :=
  rec fib_body n.

(** Since fib uses two recursive calls, we need to strengthen the induction hypothesis.  One way
   to do that is to prove the property for all [m <= n]. *)
(* SAZ: is this a good example? The stronger induction hypothesis is kind of orthogonal to the 
   point we're trying to make. *)
Lemma fib_correct : forall n m, m <= n ->
    fib m ≈ Ret (fib_spec m).
Proof.
(* SOLN *)  
  intros n.
  induction n; intros; subst.
  - apply Le.le_n_0_eq in H. subst. 
    unfold fib.  rewrite rec_as_interp. simpl. rewrite ret_interp.  reflexivity.
  - induction m; intros; subst.
    + unfold fib. rewrite rec_as_interp. simpl. rewrite ret_interp. reflexivity.
    + unfold fib.
      rewrite rec_as_interp. simpl.
      destruct m.
      * rewrite ret_interp. reflexivity.
      * rewrite interp_bind. rewrite interp_recursive_call. rewrite IHm.
        rewrite ret_bind. rewrite interp_bind. rewrite interp_recursive_call.
        unfold fib in IHn. rewrite IHn. rewrite ret_bind.
        rewrite ret_interp. reflexivity.
        omega. omega. 
Qed.
(* STUBWITH Admitted. *)

(** Logarithm *)

Definition log_ (b : nat) : nat -> itree E nat :=
  rec-fix log_b n :=
    if n =? O then
      Ret O
    else
      y <- log_b (n / b) ;; Ret (S y).

Example log_2_100 : exists y, log_ 2 100 ≈ Ret y.
Proof.
  eexists.
  tau_steps.
  reflexivity.
Qed.
