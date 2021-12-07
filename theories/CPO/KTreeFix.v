From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     Logic.Classical
     PeanoNat
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
     CPO.KTreeCPO
.

From ExtLib Require Import
     Structures.Monad.
(*
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
(* TODO : move to a some example directory if/when cleaning up for pull request*) *)
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

Definition collatzf (rec : nat -> Delay unit) : nat -> Delay unit :=
  fun n => if Nat.eqb n 1 
        then Ret tt 
        else if evenb n then rec (half n)
        else rec (3 * n + 1).

Lemma scott_cont_collatzf : @scott_continuous _ _ (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) collatzf.
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

Lemma monotone_collatzf : @monotone_fun _ _ (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) collatzf.
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

Lemma scott_cont_factf : @scott_continuous _ _  (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) factf.
Proof.
  red. cbn.
  intros seq Hmon n. unfold ktree_approx_sup. unfold apply_seq, map.
  induction n.
  - cbn. rewrite sup_head_ret; cbn; try reflexivity.
  - cbn. assert (n - 0 = n). lia. rewrite H. clear H. 
    specialize (subst_scott_cont void1 test_void test_void_correct) as Hscott.
    red in Hscott. cbn in Hscott. setoid_rewrite Hscott; try reflexivity.
    red. cbn. intros. apply Hmon. auto.
Qed.

Lemma monotone_factf : @monotone_fun _ _ (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) factf.
Proof.
  red. cbn. red. intros.
  unfold factf. destruct (Nat.eqb x 0).
  apply strong_itree_approx_refl. cbn.
  eapply strong_itree_approx_bind; eauto. intros; subst.
  apply strong_itree_approx_refl.
Qed.

Definition ktree_collatz := ktree_fix test_void collatzf.

(*
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
*)
(*maybe I should turn scott continuous into a typeclass so that typeclass resolution can be leveraged to help, because hopefully I could write some tactics to automate a bunch of this *)
Lemma fix_factf_correct : forall n, ktree_fact n ≈ (Ret (fact n) ).
Proof.
  intros.
  (* get rewriting lemma *)
  specialize (scott_continuous_fix) as Hscf.
  specialize Hscf with (T := nat -> itree void1 nat) (C := (E_ktree_cpo void1 test_void)).
  assert (weak_cpo_laws (@E_ktree_cpo void1 test_void nat nat)).
  apply  E_ktree_cpo_laws. apply test_void_correct.
  eapply Hscf in H; eauto. 3 : apply scott_cont_factf.
  3 : apply monotone_factf.
  2 :eapply ktree_pointed_weak_cpo_laws; apply test_void_correct.
  cbn in H. rename H into Hfix.
  (* function specific reasoning *)
  induction n.
  - rewrite Hfix. cbn. reflexivity.
  - rewrite Hfix. cbn. assert (n- 0 = n). lia.
    rewrite H. rewrite IHn. rewrite bind_ret_l.
    reflexivity.
Qed.
(*fix this file tomorrow, and maybe start to draw up the new and improved bind_rec *)
Lemma monotone_ackf : @monotone_fun _ _ (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) ackf.
Proof.
  red. cbn. red. intros.
  unfold ackf. destruct x as [m n].
  destruct m; try apply strong_itree_approx_refl.
  destruct n; try apply H. cbn.
  eapply strong_itree_approx_bind; eauto.
  intros; subst. auto.
Qed.
Arguments bind_rec {E} {R} {S} {T}.
Lemma scott_cont_ackf : @scott_continuous _ _  (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) ackf.
Proof.
  red. cbn.
  intros seq Hmon x.
  destruct x as [m n]. unfold ackf.
  destruct m.
  - unfold ktree_approx_sup, apply_seq, map. rewrite sup_head_ret; cbn; reflexivity.
  - destruct n; try reflexivity.
    cbn. unfold map. cbn.
    specialize (bind_rec_scott_cont void1 test_void test_void_correct) as Hscott.
    red in Hscott. cbn in Hscott. unfold KTreeCPO.ktree_approx_sup in *.
     set (fun (rec : nat * nat -> Delay nat) (r : nat) => rec (m,r)) as kcont.
    set (bind_rec (fun (rec : nat * nat -> Delay nat) (r : nat) => rec (m,r))) as br.
    specialize (Hscott (nat * nat) nat nat kcont)%type.
    eapply Hscott in Hmon. Unshelve. all : try apply (S m, n).
    2 : { red. cbn. intros. unfold kcont.
          unfold KTreeCPO.strong_ktree_approx in *. auto. }
    2 : { red. intros. cbn in *. unfold KTreeCPO.weak_ktree_approx in *. unfold kcont. auto. }
    2 : { red. intros. unfold kcont. unfold map. cbn.
          unfold  KTreeCPO.ktree_approx_sup. unfold apply_seq, map.
          intros. reflexivity. }
    unfold ktree_approx_sup, apply_seq, map.
    unfold bind_rec, apply_seq, map, kcont in Hmon.
    symmetry in Hmon. rewrite Hmon. reflexivity.
Qed.


Local Open Scope nat_scope.

Definition fibf (rec : nat -> Delay nat) (n : nat) : Delay nat :=
  if n =? 0
  then Ret 1
  else if n =? 1 then Ret 1
  else x <- rec (n - 1);; y <- rec (n - 2);; Ret (x + y).

Definition ktree_fib : nat -> Delay nat := ktree_fix test_void fibf.

Lemma scott_cont_fibf : @scott_continuous _ _  (E_ktree_cpo void1 test_void) (E_ktree_cpo void1 test_void) fibf.
Proof.
  red. cbn. intros seq Hmon n.
  destruct n.
  - unfold ktree_approx_sup, apply_seq, map. rewrite sup_head_ret; cbn; reflexivity.
  - cbn. unfold ktree_approx_sup. destruct (n =? 0) eqn : Hn.
    + unfold ktree_approx_sup, apply_seq, map. rewrite sup_head_ret; cbn; try reflexivity.
      rewrite Hn; reflexivity.
    + unfold fibf, apply_seq, map. cbn. rewrite Hn.
      set (fun (rec : nat -> Delay nat) (x : nat) => ITree.bind (rec (n - 1)) (fun y => Ret (x + y) ) ) as kcont.
      specialize (bind_rec_scott_cont void1 test_void test_void_correct) as Hscott.
      red in Hscott. cbn in Hscott. unfold KTreeCPO.ktree_approx_sup in *.
      specialize (Hscott nat nat nat kcont). symmetry in Hscott.
      unfold bind_rec, kcont, apply_seq, map in Hscott. 
      rewrite Hscott; try reflexivity; clear Hscott; auto.
      * red. cbn. unfold KTreeCPO.strong_ktree_approx. intros.
        eapply strong_itree_approx_bind; eauto. intros; subst.
        apply strong_itree_approx_refl.
      * red. cbn. unfold KTreeCPO.weak_ktree_approx. intros.
        eapply weak_itree_approx_bind; eauto. intros; subst.
        apply weak_itree_approx_refl.
      * red. intros. unfold kcont. unfold map. cbn.
        unfold  KTreeCPO.ktree_approx_sup. unfold apply_seq, map. intros.
        specialize (subst_scott_cont void1 test_void test_void_correct) as Hscott.
    red in Hscott. cbn in Hscott. setoid_rewrite Hscott; try reflexivity.
    red. intros. eapply H. auto.
Qed.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => match m with
          | 0 => 1
          | S m' => fib m + fib m' end
  end.

Lemma ktree_fib_unfold : forall n, ktree_fib n ≈ fibf ktree_fib n.
Proof.
  intros.
  specialize (scott_continuous_fix) as Hfix.
  specialize (scott_cont_fibf) as Hscott.
  eapply Hfix in Hscott; eauto. apply E_ktree_cpo_laws; apply test_void_correct.
  apply ktree_pointed_weak_cpo_laws; apply test_void_correct.
  unfold fibf, strong_ktree_approx. red. cbn. unfold strong_ktree_approx. intros.
  destruct (x =? 0); destruct (x =? 1); try apply strong_itree_approx_refl.
  eapply strong_itree_approx_bind; try apply strong_itree_approx_refl; eauto.
  intros; subst.
  eapply strong_itree_approx_bind; try apply strong_itree_approx_refl; eauto.
  intros; subst. apply strong_itree_approx_refl.
Qed.
  

Lemma ktree_fib_correct_aux : forall n,
    ktree_fib (2 + n) ≈ x <- ktree_fib (1 + n);; y <- ktree_fib n;; Ret (x + y).
Proof.
  intros.
  rewrite ktree_fib_unfold. cbn.
  assert (n - 0 = n). lia. rewrite H. reflexivity.
Qed.

Lemma ktree_fib_correct : forall n, ktree_fib n ≈ Ret (fib n).
Proof.
  intros n.
  enough (ktree_fib n ≈ Ret (fib n) /\ ktree_fib (S n) ≈ Ret (fib (S n))  ).
  destruct H; auto.
  induction n; split.
  - rewrite ktree_fib_unfold. reflexivity.
  - rewrite ktree_fib_unfold. reflexivity.
  - tauto.
  - destruct IHn as [IHn IHSn].
    setoid_rewrite ktree_fib_correct_aux.
    rewrite IHSn. setoid_rewrite IHn. do 2 setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

(*
Notation Delay' A := (itree' void1 A).
CoFixpoint par_or' (b1 b2 : Delay' bool) : Delay bool :=
  match b1, b2 with
  | RetF b, _ => if b then Ret b else go b2
  | _, RetF b => if b then Ret b else go b1
  | TauF b1', TauF b2' => Tau (par_or' (observe b1') (observe b2'))
  | _, _ => ITree.spin end.

Definition par_or (b1 b2 : Delay bool) : Delay bool := par_or' (observe b1) (observe b2).
*)
End FactExample.
