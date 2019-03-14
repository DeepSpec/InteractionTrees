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
     ITree
     MorphismsFacts
     Recursion
     RecursionFacts.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Factorial Example *)

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
Definition fact_body {E}  : nat -> itree (callE nat nat +' E) nat :=
  (fun x => match x with
         | 0 => Ret 1
         | S m => y <- call m ;; Ret (x * y)
         end).

(** The factorial function itself is defined as an itree by 'tying the knot' using [rec]. 

    (Aside: Note that [factorial] is actually a [KTree] of type [ktree nat nat].)
*)
Definition factorial {E} (n:nat) : itree E nat :=
  rec fact_body n.

(** This is the Coq specification -- the usual mathematical definition. *)
Fixpoint factspec (n:nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * factspec m
  end.

(** We can prove that the ITrees version [factorial] is "equivalent" to the
    [factspec] version.  The proof goes by induction on n and uses only
    rewriting -- no coinduction necessary. Here, we step through each step of
    rewriting to illustrate the use of the equational theory, which is mostly
    applications of the monad laws and the properties of [rec], seen as an 
    instance of [mrec]. 
*)
(* SAZ: The rewriting in this proof is a bit annoying.  
    - We have to use itree_eta in order to rewrite with ret_bind.  
    - the use of cbn to drive the interp forward also unfolds the fact_body too
      much, which means we have to use fold_bind so that interp_bind can see
      the bind.
*)
Lemma factorial_correct : forall {E} n, (factorial n : itree E nat) ≈ Ret (factspec n).
Proof.
  intros E n.
  induction n; intros; subst.
  - unfold factorial. rewrite rec_unfold. simpl. rewrite ret_interp. reflexivity.
  - unfold factorial. rewrite rec_unfold. simpl.
    rewrite interp_bind.
    rewrite interp_recursive_call.
    rewrite IHn.
    rewrite ret_bind.
    rewrite ret_interp.
    reflexivity.
Qed.

(* begin hide *)
(* SAZ: we might experiment with automating monadic rewriting according to the equational reasoning, 
   something like: *)
Ltac simpl_monad :=
    repeat match goal with
           | [ |- context[Tau ?T] ] => progress rewrite tau_eutt
           | [ |- context[ITree.bind (Ret ?X) ?K] ] => progress rewrite ret_bind
           | [ |- context[interp_mrec _ _ (ITree.bind ?T ?K)] ] => progress rewrite interp_mrec_bind
           | [ |- context[interp_mrec _ _ (Ret ?X)] ] => progress rewrite ret_mrec                                            end.
                     
(* Then the proof above becomes: 

    simpl_monad.
    rewrite IHn.
    simpl_monad.
    reflexivity.
*)
(* end hide *)

