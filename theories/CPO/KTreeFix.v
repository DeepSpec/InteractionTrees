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
     CPO.ITreeCPO
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

Global Instance ktree_cpo_laws {R S E} test_and_apply :
  test_and_apply_correct E test_and_apply ->
  weak_cpo_laws (@ktree_cpo R S E test_and_apply).
Proof.
  intros Htaa.
  econstructor; cbn.
  - split; intros. unfold weak_ktree_approx. setoid_rewrite H.
    split; intros; apply weak_itree_approx_refl. unfold weak_ktree_approx in H.
    destruct H. apply weak_itree_approx_antisym; auto.
  - split; intros; unfold strong_ktree_approx. setoid_rewrite H.
    split; intros; apply strong_itree_approx_refl. destruct H.
    apply strong_itree_approx_antisym; auto.
  - intros. rewrite H. reflexivity.
  - intros. red. intros. apply strong_to_weak_itree_approx; auto.
  - intros. red. intros. apply strong_itree_approx_spin_bottom.
  - intros. red in H. cbn in H. constructor; eauto.
    + cbn. unfold weak_ktree_approx, ktree_approx_sup. intros.
      unfold apply_seq. cbn. unfold map.
      set (fun n => seq n x) as seq'. assert (seq n x = seq' n). auto. rewrite H0.
      eapply sup_is_upper_bound; destruct Htaa; eauto.
      constructor; cbv; intros; subst; auto. red. intros. apply H. auto.
    + cbn. unfold weak_ktree_approx, ktree_approx_sup, apply_seq, map.
      intros. set (fun n => seq n x) as seq'.
      eapply sup_is_below_all_upper_bounds; eauto; destruct Htaa; eauto.
      constructor; cbv; intros; subst; auto. red. intros. apply H. auto. 
  - repeat intro. cbn in *. red in H. cbn in H.
    unfold ktree_approx_sup, apply_seq, map. 
    eapply proper_fun_seq'; auto. repeat red. intros; subst. apply H.
  - intros. unfold ktree_approx_sup, apply_seq, map.
    set (fun n => seq n r) as seq'. 
    rewrite sup_advance_eutt; destruct Htaa; auto.
    2 : constructor; cbv; intros; subst; auto.
    2 : { unfold seq';  red in H. red. intros. eapply H. auto. }
    unfold advance, seq'. reflexivity.
Unshelve.
 constructor; red; cbn; intros. reflexivity.
 rewrite H. reflexivity.
 rewrite <- H0. auto.
 constructor. red. cbn. intros. red. intros. apply weak_itree_approx_refl.
 red. cbn. unfold weak_ktree_approx. intros. eapply weak_itree_approx_trans_eq; eauto.
 constructor; red; cbn; intros. reflexivity. rewrite H. reflexivity.
 rewrite H. auto.
 constructor; red; cbn; unfold strong_ktree_approx. intros. apply strong_itree_approx_refl.
 intros. cbn in *. 
 eapply strong_itree_approx_mon with (RR1 := rcompose eq eq). intros. inv H1. auto.
 eapply strong_itree_approx_trans; eauto.
Qed.

Definition ktree_fix {R S E} test_and_apply (f : (R -> itree E S) -> (R -> itree E S) ) : R -> itree E S :=
  @weak_cpo_fix _ f (ktree_cpo test_and_apply).
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

Lemma test_void_correct : test_and_apply_correct void1 test_void.
Proof.
  constructor; intros; try destruct e; try destruct e1. destruct H.
Qed.

Lemma scott_cont_factf : @scott_continuous _ (ktree_cpo test_void) factf.
Proof.
  red. cbn.
  intros seq Hmon n. unfold ktree_approx_sup.  unfold apply_seq, map.
  induction n.
  - cbn. rewrite sup_head_ret; cbn; try reflexivity.
  - cbn. assert (n - 0 = n). lia. rewrite H. clear H. 
    specialize (subst_scott_cont void1 test_void test_void_correct) as Hscott.
    red in Hscott. cbn in Hscott. setoid_rewrite Hscott; try reflexivity.
    red. cbn. intros. apply Hmon. auto.
Qed.

Lemma monotone_factf : @monotone_fun _ (ktree_cpo test_void) factf.
Proof.
  red. cbn. red. intros.
  unfold factf. destruct (Nat.eqb x 0).
  apply strong_itree_approx_refl. cbn.
  eapply strong_itree_approx_bind; eauto. intros; subst.
  apply strong_itree_approx_refl.
Qed.

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

(*
Goal burn 50 (ktree_fact 10) ≈ Ret (fact 10).
  reflexivity.
Qed.
*)
Lemma fix_factf_correct : forall n, ktree_fact n ≈ (Ret (fact n) ).
Proof.
  intros. induction n.
  - unfold ktree_fact. unfold ktree_fix. cbn.
    unfold ktree_approx_sup. rewrite sup_head_tau.
    2 : { cbn.  rewrite spin_cong_tau_spin. reflexivity. }
    rewrite tau_eutt. rewrite sup_head_ret. reflexivity.
    unfold advance, peel_tau. cbn. rewrite peel_tau_elem_ret. reflexivity.
  - unfold ktree_fact, ktree_fix. 
    specialize (scott_continuous_fix) as Hscf.
    specialize Hscf with (T := nat -> itree void1 nat) (C := (ktree_cpo test_void)).
    assert (weak_cpo_laws (@ktree_cpo nat nat void1 test_void)).
    apply  ktree_cpo_laws. apply test_void_correct.
    eapply Hscf in H. 2 : apply scott_cont_factf.
    2 : apply monotone_factf.
    cbn in H. setoid_rewrite H. unfold factf at 1. simpl. 
    assert ((n - 0) = n). lia. rewrite H0. rewrite IHn.
    rewrite bind_ret_l. reflexivity.
Qed.
(* Ideally I would write some ltac wizardry named unfold_fix or something
   which would search a hint library to be able to do this with less annoyance
   if only I was an ltac wizard :(
 *)


End FactExample.
