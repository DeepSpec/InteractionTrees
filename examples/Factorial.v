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
Definition fact_body {E}  : nat -> itree (callE nat nat +' E) nat :=
  fun x => match x with
        | 0 => Ret 1
        | S m => y <- call m ;; Ret (x * y)
        end.

(** The factorial function itself is defined as an itree by 'tying the knot' using [rec]. 

    (Aside: Note that [factorial] is actually a [KTree] of type [ktree nat nat].)
*)
Definition factorial {E} (n:nat) : itree E nat :=
  rec fact_body n.

(** This is the Coq specification -- the usual mathematical definition. *)
Fixpoint factorial_spec (n:nat) : nat :=
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
Lemma factorial_correct : forall {E} n, (factorial n : itree E nat) ≈ Ret (factorial_spec n).
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


(** * Fibonacci *)

(** Exercise *)
(** Carry out the analogous proof of correctness for the Fibonacci function, whose
    naturally recursive coq definition is given below. *)

Fixpoint fib_spec (n:nat) : nat :=
  match n with
  | 0 => 1
  | S m =>
    match m with
    | 0 => 1
    | S k => fib_spec m + fib_spec k
    end
  end.

(** We write the body of the fib monadically, using events rather than recursive calls. *)
Definition fib_body {E}  : nat -> itree (callE nat nat +' E) nat :=
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

Definition fib {E} n : itree E nat :=
  rec fib_body n.

(** Since fib uses two recursive calls, we need to strengthen the induction hypothesis.  One way
   to do that is to prove the property for all [m <= n]. *)
(* SAZ: is this a good example? The stronger induction hypothesis is kind of orthogonal to the 
   point we're trying to make. *)
Lemma fib_correct : forall {E} n m, m <= n ->
    (fib m : itree E nat ) ≈ Ret (fib_spec m).
Proof.
(* SOLN *)  
  intros E n.
  induction n; intros; subst.
  - apply Le.le_n_0_eq in H. subst. 
    unfold fib.  rewrite rec_unfold. simpl. rewrite ret_interp.  reflexivity.
  - induction m; intros; subst.
    + unfold fib. rewrite rec_unfold. simpl. rewrite ret_interp. reflexivity.
    + unfold fib.
      rewrite rec_unfold. simpl.
      destruct m.
      * rewrite ret_interp. reflexivity.
      * rewrite interp_bind. rewrite interp_recursive_call. rewrite IHm.
        rewrite ret_bind. rewrite interp_bind. rewrite interp_recursive_call.
        unfold fib in IHn. rewrite IHn. rewrite ret_bind.
        rewrite ret_interp. reflexivity.
        omega. omega. 
Qed.
(* STUBWITH Admitted. *)


Inductive tree (X:Type) :=
| Empty
| Node (t1 : tree X) (x:X) (t2 : tree X)
.


Require Import Lists.List.
Require Import Paco.paco.
Open Scope list_scope.




Definition bfs_body {E} (n:nat) (q : list (tree nat)) : itree (callE (list (tree nat)) bool +' E) bool :=
  match q with
  | [] => Ret false
  | t::ts => match t with
           | Empty => call ts
           | Node t1 x t2 =>
             if Nat.eqb n x then Ret true else call (ts ++ [t1; t2])
           end
  end.

Definition bfs {E} n (t:tree nat) : itree E bool :=
  rec (bfs_body n) [t].

Definition dfs_body {E} (n:nat) (q : list (tree nat)) : itree (callE (list (tree nat)) bool +' E) bool :=
  match q with
  | [] => Ret false
  | t::ts => match t with
           | Empty => call ts
           | Node t1 x t2 =>
             if Nat.eqb n x then Ret true else call ([t1 ; t2] ++ ts)
           end
  end.

Definition dfs {E} n (t:tree nat) : itree E bool :=
  rec (bfs_body n) [t].



Lemma bfs_dfs : forall {E} n q, rec (bfs_body n) q ≈ (rec (dfs_body n) q : itree E bool).
Proof.
  intros E n q.
  pupto2_init.
  revert q.
  pcofix CIH.
  intros q.
  do 2 rewrite rec_unfold.
  induction q; simpl.
  - rewrite ret_interp. rewrite ret_interp.  pupto2_final.  pfold.  pfold. econstructor. reflexivity.  (* SAZ This reflexivity proof is annoyting .*)
  - destruct a.
    + rewrite interp_recursive_call.  rewrite interp_recursive_call.
      rewrite rec_unfold. rewrite rec_unfold. assumption.
    + destruct (n =? x).
      * rewrite ret_interp. rewrite ret_interp. pupto2_final.  pfold.  pfold. econstructor. reflexivity.  (* SAZ This reflexivity proof is annoyting .*)
      * rewrite interp_recursive_call.  rewrite interp_recursive_call.
        
      
                              

Lemma bfs_q : forall {E:Type->Type} n t ts,
                  (rec (bfs_body n) (t::ts) : itree E bool) ≈ match t with
                                 | Empty => rec (bfs_body n) ts
                                 | Node t1 x t2 =>
                                   if Nat.eqb n x then Ret true else rec (bfs_body n) (ts ++ [t1; t2])
                                                          end.
Proof.
  intros.
  rewrite rec_unfold. simpl.
  destruct t.
  rewrite interp_recursive_call. reflexivity.
  destruct (n =? x).
  rewrite ret_interp. reflexivity.
  rewrite interp_recursive_call. reflexivity.
Qed.

Require Import Lists.List.
Require Import Paco.paco.

Fixpoint contains n (t:tree nat) : bool :=
  match t with
  | Empty => false
  | Node t1 x t2 => if Nat.eqb n x then true else orb (contains n t1) (contains n t2)
  end.

Lemma fold_orb_true : forall l : list bool, 
    fold_left (fun x y => orb x y) l true = true.
Proof.
  induction l; auto.
Qed.

Lemma bfs_contains : forall E n (q : list (tree nat)),
    (rec (bfs_body n) q : itree E bool) ≈
        (Ret (List.fold_left (fun x y => orb x y) (List.map (contains n) q) false)).
Proof.
  intros E n q.
  pupto2_init.
  revert q.
  pcofix CIH.
  intros q.
  induction q; simpl.
  - rewrite rec_unfold. simpl.  rewrite ret_interp. pupto2_final.  pfold. pfold. econstructor. reflexivity.
  - rewrite rec_unfold. simpl. destruct a; simpl.
    + rewrite interp_recursive_call.  assumption.
    + destruct (n =? x); simpl.
      * rewrite fold_orb_true.
        rewrite ret_interp. pupto2_final. pfold. pfold. econstructor. reflexivity.
      * rewrite interp_recursive_call.
        


Lemma bfs_q2 : forall {E:Type->Type} n q1 q2,
    (rec (bfs_body n) (q1 ++ q2) : itree E bool) ≈ 
                                              (y1 <- rec (bfs_body n) q1 ;;
                                               y2 <- rec (bfs_body n) q2 ;;
                                               Ret (orb y1 y2)).
Proof.
  intros E n.
  induction q1; intros q2; simpl.
  - rewrite rec_unfold. rewrite rec_unfold.
    simpl.  rewrite ret_interp. rewrite ret_bind.
    rewrite rec_unfold.  simpl. rewrite bind_ret. reflexivity.
  - do 2 rewrite rec_unfold.
    simpl.
    destruct a.
    + rewrite interp_recursive_call.
      rewrite IHq1.
      rewrite interp_recursive_call.
      reflexivity.
    + destruct (n =? x).
      rewrite ret_interp.
      rewrite ret_bind. simpl. 
    

  



Lemma contains_bfs: forall {E} n t, (bfs n t : itree E bool) ≈ Ret (contains t n).
Proof.
  intros E n t.
  pupto2_init.
  revert n t.
  pcofix CIH.
  intros n t.
  unfold bfs.
  rewrite bfs_q.
  destruct t; simpl.
  - rewrite rec_unfold.  simpl. rewrite ret_interp. pupto2_final. pfold.  pfold. econstructor. reflexivity.
  - destruct (n=?x).
    pfold. pfold. econstructor. reflexivity.
    
  


