Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Nat
     Setoid
     RelationClasses
     Program
     Morphisms.

From ITree Require Import
     ITree
     Fix
     FixFacts
     Eq.Eq
     Eq.UpToTaus
     MorphismsFacts.

(* Define the recursive factorial function via events. 
   Here we use the generic "rec" interface of the library, instantiating callE
   with the type of factorial : nat -> nat.
*)
Definition factC {E} n : itree (callE nat nat +' E) nat := ITree.liftE (inl1 (Call n)).

(* We write the body of the function monadically, using events rather than recursive calls. *)
Definition fact_body {E} (rec : nat -> itree (callE nat nat +' E) nat) : nat -> itree (callE nat nat +' E) nat :=
  (fun x => match x with
         | 0 => Ret 1
         | S m => y <- rec m ;; Ret (x * y)
         end).

Definition factorial {E} (n:nat) : itree E nat :=
  rec (fact_body factC) n.


(* This is the Coq specification -- the usual mathematical definition. *)
Fixpoint factspec (n:nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * factspec m
  end.

(* The proof is by induction on n and uses only rewriting, no coinduction. *)
(* SAZ: The rewriting in this proof is a bit annoying.  
    - We have to use itree_eta in order to rewrite with ret_bind.  
    - the use of cbn to drive the interp forward also unfolds the fact_body too
      much, which means we have to use fold_bind so that interp_bind can see
      the bind.
*)
Lemma factorial_correct : forall {E} n, (factorial n : itree E nat) ≈ Ret (factspec n).
Proof.
  intros E.
  intros n.
  induction n; intros; subst.
  - rewrite itree_eta. cbn. reflexivity.
  - unfold factorial.
    rewrite rec_unfold.
    rewrite itree_eta.
    cbn. 
    rewrite tau_eutt.
    rewrite IHn.
    rewrite itree_eta.
    rewrite ret_bind.
    fold_bind. rewrite interp_bind.
    rewrite interp_ret. rewrite ret_bind.
    rewrite interp_ret. reflexivity.
Qed.