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
     FixFacts
     MorphismsFacts.

Import MonadNotation.
Open Scope monad_scope.

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
(* SAZ: TODO - we should probably add this (suitably renamed) to Interp.v *)
Definition factC {E} n : itree (callE nat nat +' E) nat := ITree.liftE (inl1 (Call n)).

(** We write the body of the function monadically, using events rather than recursive calls. *)
Definition fact_body {E}  : nat -> itree (callE nat nat +' E) nat :=
  (fun x => match x with
         | 0 => Ret 1
         | S m => y <- factC m ;; Ret (x * y)
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

(* SAZ: Why was this removed from the library? *)
Ltac fold_bind := (change @ITree.bind' with (fun E T U k t => @ITree.bind E T U t k) in *; simpl in *).


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
  - rewrite itree_eta. cbn. reflexivity.
  - rewrite itree_eta.
    cbn; fold_bind.    
    rewrite tau_eutt.
    rewrite ret_bind.
    rewrite interp_mrec_bind.
    rewrite IHn.
    rewrite ret_bind.
    rewrite interp_mrec_bind.
    rewrite ret_mrec.
    rewrite ret_bind.
    rewrite ret_mrec.
    reflexivity.
Qed.


(* HIDE *)
(* SAZ: we might experiment with automating monadic rewriting according to the equational reasoning, 
   something like: *)
Ltac simpl_monad :=
    repeat match goal with
           | [ |- context[Tau ?T] ] => progress rewrite tau_eutt
           | [ |- context[ITree.bind (Ret ?X) ?K] ] => progress rewrite ret_bind
           | [ |- context[interp_mrec _ _ (ITree.bind ?T ?K)] ] => progress rewrite interp_mrec_bind
           | [ |- context[interp_mrec _ _ (Ret ?X)] ] => progress rewrite ret_mrec                                                                         
           end.
                     
(* Then the proof above becomes: 

    simpl_monad.
    rewrite IHn.
    simpl_monad.
    reflexivity.
*)
(* /HIDE *)

