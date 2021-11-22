From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Logic.Classical
.

Require Import Lia.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq
     CPO.CPO
     CPO.ITreeApprox
     CPO.ITreeApproxSup
.

From ExtLib Require Import
     Structures.Monad.

Definition strong_ktree_approx {R S E} RR (f g : R -> itree E S) :=
  forall x, strong_itree_approx RR (f x) (g x).

Definition weak_ktree_approx {R S E} RR (f g : R -> itree E S) :=
  forall x, weak_itree_approx RR (f x) (g x).

Definition ktree_monotone_approx {R S E} RR (seq : sequence (R -> itree E S) ) : Prop :=
  forall x, monotone_approx RR (apply_seq seq x).

Definition ktree_approx_sup {R S E} test_and_apply (seq : sequence (R -> itree E S) ) : R -> itree E S :=
  fun x => itree_approx_sup test_and_apply (apply_seq seq x). 

Global Instance itree_cpo {R E} test_and_apply : weak_cpo (itree E R) :=
  {|
    weak_leq := weak_itree_approx eq;
    strong_leq := strong_itree_approx eq;
    sup := itree_approx_sup test_and_apply;
    weak_eq := eutt eq;
    strong_eq := eq_itree eq;
    bot := ITree.spin;
  |}.

Global Instance ktree_cpo {R S E} test_and_apply : weak_cpo (R -> itree E S) :=
  {|
    weak_leq := weak_ktree_approx eq;
    strong_leq := strong_ktree_approx eq;
    sup := ktree_approx_sup test_and_apply;
    weak_eq := fun k1 k2 => forall r, k1 r ≈ k2 r;
    strong_eq := fun k1 k2 => forall r, k1 r ≅ k2 r;
    bot := fun _ => ITree.spin;
  |}.


Definition ktree_bot {R S E} := fun (x : R) => @ITree.spin E S.

Definition ktree_fix_seq {R S E} (f : (R -> itree E S) -> (R -> itree E S) ) : sequence (R -> itree E S) :=
  fun n => frepeat f n ktree_bot.

Definition ktree_fix {R S E} test_and_apply (f : (R -> itree E S) -> (R -> itree E S) ) (x : R) : itree E S :=
  itree_approx_sup test_and_apply (apply_seq (ktree_fix_seq f) x ).
(* got confused here 
Definition scott_cont {R S E} test_and_apply (f : (R -> itree E S) -> (R -> itree E S) ) : Prop :=
  forall (seq : sequence (R -> itree E S) ), ktree_monotone_approx eq seq ->
  forall x, f (itree_approx_sup test_and_apply (apply_seq seq)) ≈ itree_approx_sup test_and_apply (apply_seq (map f seq) x).
 *)
(* TODO : move to a some example directory if/when cleaning up for pull request*)
Section FactExample.

Import Monads. Locate MonadNotation.
Import MonadNotation.
Local Open Scope monad_scope.

Variant void1 : Type -> Type := .

Definition test_void : forall A B C, void1 A -> A -> void1 B -> (B -> C) -> C -> C :=
  fun _ _ _ v => match v with end.


Fixpoint fact (n : nat) := 
  match n with
  | 0 => 1
  | S m => n * (fact m) end.

Notation Delay A := (itree void1 A).

Definition factf (rec : nat -> Delay nat ) (n : nat) : Delay nat :=
  if Nat.eqb n 0 
  then Ret 1
  else m <- (rec (n - 1) );; Ret (n * m).
(*
Lemma scott_cont_subst : @scott_continuous _ (itree_cpo )
*)

    (* this is the scott cont of bind (technically subst but whatever) *)
(*
  destruct (observe (seq 0 n) ) eqn : H0; symmetry in H0; use_simpobs; try destruct e.
  - unfold apply_seq, map. unfold factf. 
    destruct (Nat.eqb n 0) eqn : Hn. 
    + rewrite sup_head_ret; try reflexivity. gstep. constructor. auto.
    + cbn. (* can I pull this bind out? *) admit.
  -  *)
    (*properly defined, so how do I write it*)


Definition ktree_fact : nat -> Delay nat := ktree_fix test_void factf.



Definition ackf (rec : nat * nat -> Delay nat) : nat * nat -> Delay nat :=
  fun '(m,n) =>
    match (m,n) with
    | (0, _ ) => Ret (n + 1)
    | (S m', 0) => rec (m', 1)
    | (S m', S n') => r <- rec (m, n');; rec (m', r) end
 . 

Definition ktree_ackf := ktree_fix test_void ackf.

Fixpoint half (n : nat) : nat :=
  match n with
  | S (S m) => S (half m)
  | 1 => 1
  | 0 => 0 end.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false 
  | S (S m) => evenb m end.

Definition collatzf (rec : nat -> Delay nat) : nat -> Delay nat :=
  fun n => if Nat.eqb n 1 
        then Ret 1 
        else if evenb n then rec (half n)
        else rec (3 * n + 1).

Lemma scott_cont_collatzf : @scott_continuous _ (ktree_cpo test_void) collatzf.
Proof.
  red. cbn. intros. unfold collatzf.
  rename r into n. destruct (Nat.eqb n 1) eqn : Hn1.
  - cbn. unfold ktree_approx_sup, apply_seq, map. cbn.
    rewrite Hn1.
    setoid_rewrite sup_head_ret; reflexivity.
  - unfold map. destruct (evenb n) eqn :Hnev.
    + cbn. unfold ktree_approx_sup, apply_seq, map. cbn.
      rewrite Hn1, Hnev. reflexivity.
    + cbn. unfold ktree_approx_sup, apply_seq, map. cbn.
      rewrite Hn1, Hnev. reflexivity.
Qed.

Lemma monotone_collatzf : @monotone_fun _ (ktree_cpo test_void) collatzf.
Proof.
  red. cbn. intros.
  intros n. unfold collatzf.
  destruct (Nat.eqb n 1). pstep. constructor. auto.
  destruct (evenb n); auto.
Qed.

 (* this one was easy because it is tail recursive *)

(*writing some lemmas will certainly help but maybe ltac wizardry is what is really needed,
  what is valid to do with a recursive call, just call it, 
  call it and then bind it to something else,

  maybe call it inside

 *)

(* could also write a relational collatz def, and prove it coincides with the fixpoint of collatzf*)

Lemma scott_cont_factf : @scott_continuous _ (ktree_cpo test_void) factf.
Proof.
  red. cbn.
  intros seq Hmon n. unfold ktree_approx_sup.  unfold apply_seq, map.
  induction n.
  - cbn. rewrite sup_head_ret; cbn; try reflexivity.
  - cbn. assert (n - 0 = n). lia. rewrite H. clear H. 
    remember (fun n0 : nat => seq n0 n ) as seq'.
    remember (fun m => Ret (m + n * m) ) as k.
    assert (itree_approx_sup test_void (fun n0 : nat => ITree.bind (seq n0 n) k) ≅
                            itree_approx_sup test_void (map (ITree.subst k) seq'  ) ).
    { eapply proper_fun_seq; intros; try destruct e; try destruct e1.
      admit. (* might be a weakness in the current set up, should be avoidable*)
      intros n1 n2 Hn; subst. reflexivity. }
    rewrite H.
    Abort.

Definition ktree_collatz := ktree_fix test_void collatzf.


Goal burn 50 (ktree_fact 0) ≈ Ret 1.
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 1) ≈ Ret 1.
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 2) ≈ Ret (fact 2).
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 3) ≈ Ret (fact 3).
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 4) ≈ Ret (fact 4).
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 5) ≈ Ret (fact 5).
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 6) ≈ Ret (fact 6).
  reflexivity.
Qed.

Goal burn 50 (ktree_fact 7) ≈ Ret (fact 7).
  reflexivity.
Qed.


Goal burn 50 (ktree_fact 10) ≈ Ret (fact 10).
  reflexivity.
Qed.

Lemma fix_factf_correct : forall n, ktree_fact n ≈ (Ret (fact n) ).
Proof.
  intros. induction n.
  - unfold ktree_fact. unfold ktree_fix. cbn.
    rewrite sup_head_tau.
    2 : { cbn. unfold ktree_bot. rewrite spin_cong_tau_spin. reflexivity. }
    rewrite tau_eutt. rewrite sup_head_ret. reflexivity.
    unfold advance, peel_tau. cbn. rewrite peel_tau_elem_ret. reflexivity.
  - cbn.  unfold ktree_fact. (* here the only reasonable way is scott continuity *)
(* started to get slow but still worked 
Goal burn 50 (ktree_fact 7) ≈ Ret (fact 7).
  cbn. reflexivity.
Qed.
*)
End FactExample.
