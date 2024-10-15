(** * Utilities for the compiler tutorial *)

(** This file should not be required to be read for
    understanding the remaining of the tutorial.
    It however contains no hidden black magic. Its
    main content is the following:
    - a few simple generic tactics;
    - a collection of facts about ExtLib's association
    lists [alist] that should probably be moved over ExtLib;
    - a function converting [nat] to their decimal representation
    as [string], and an unreasonably painful proof of the injectivity
    of this function.
    - a [traverse_] function.
*)

(* begin hide *)
From Coq Require Import
     Ascii
     String
     List
     Arith
     ZArith
     Nat
     Psatz.

From ExtLib Require Import
     Core.RelDec
     Programming.Show
     Data.Map.FMapAList.
(* end hide *)

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac inv h := inversion h; subst; clear h.

Section alistFacts.


  (* Generic facts about alists. To eventually move to ExtLib. *)

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Arguments alist_add {_ _ _ _}.
  Arguments alist_find {_ _ _ _}.
  Arguments alist_remove {_ _ _ _}. 

  Context {K V: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.
  
  Lemma In_add_eq:
    forall k v (m: alist K V),
      alist_In k (alist_add k v m) v.
  Proof.
    intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
  Qed.

  (* A removed key is not contained in the resulting map *)
  Lemma not_In_remove:
    forall (m : alist K V) (k : K) (v: V),
      ~ alist_In k (alist_remove k m) v.
  Proof.
    induction m as [| [k1 v1] m IH]; intros.
    - simpl; intros abs; inv abs. 
    - simpl; flatten_goal.
      + unfold alist_In; simpl.
        rewrite Bool.negb_true_iff in Heq; rewrite Heq.
        intros abs; eapply IH; eassumption.
      + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        intros abs; eapply IH; eauto. 
  Qed.

  (* Removing a key does not alter other keys *)
  Lemma In_In_remove_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_remove k' m) v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
    simpl.
    flatten_goal.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
      flatten_goal; auto.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
      flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
  Qed.       

  Lemma In_remove_In_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      alist_In k (alist_remove k' m) v ->
      alist_In k m v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
    simpl in IN; flatten_hyp IN.
    - unfold alist_In in *; simpl in *.
      flatten_all; auto.
      eapply IH; eauto.
    -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
     unfold alist_In; simpl. 
     flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
     exfalso; eapply not_In_remove; eauto.
     eapply IH; eauto.
  Qed.       

  Lemma In_remove_In_ineq_iff:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k (alist_remove k' m) v <->
      alist_In k m v.
  Proof.
    intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
  Qed.       

  (* Adding a value to a key does not alter other keys *)
  Lemma In_In_add_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_add k' v' m) v.
  Proof.
    intros.
    unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
    apply In_In_remove_ineq; auto.
  Qed.

  Lemma In_add_In_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k (alist_add k' v' m) v ->
      alist_In k m v. 
  Proof.
    intros k v k' v' m ineq IN.
    unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
    eapply In_remove_In_ineq; eauto.
  Qed.

  Lemma In_add_ineq_iff: 
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      alist_In k m v <-> alist_In k (alist_add k' v' m) v.
  Proof.
    intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
  Qed.

  (* alist_find fails iff no value is associated to the key in the map *)
  Lemma alist_find_None:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Proof.
    induction m as [| [k1 v1] m IH]; [simpl; easy |].
    simpl; split; intros H. 
    - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
      apply (H v1); left; reflexivity.
      apply IH; intros v abs; apply (H v); right; assumption.
    - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
      intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
  Qed.

  Lemma alist_In_add_eq : forall m (k:K) (v n:V), alist_In k (alist_add k n m) v -> n = v.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - unfold alist_add in H.
      unfold alist_In in H. simpl in H.
      destruct (k ?[ eq ] k); inversion H; auto.
    - unfold alist_add in H.
      unfold alist_In in H.
      simpl in H.
      destruct (k ?[ eq ] k). inversion H; auto.
      pose proof (@not_In_remove ((k1,v1)::m)).
      unfold alist_In in H0. simpl in H0.
      apply H0 in H.
      contradiction.
  Qed.

  Lemma alist_find_remove_none:
    forall (m : list (K*V)) (k1 k2 : K), k2 <> k1 -> alist_find k1 (alist_remove k2 m) = None -> alist_find k1 m = None.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k1 ?k2 ineq HF; simpl in *.
    - reflexivity.
    - destruct (rel_dec_p k1 k).
      + subst. eapply rel_dec_neq_false in ineq; eauto. rewrite ineq in HF. simpl in HF.
        assert (k = k) by reflexivity.
        apply rel_dec_correct in H. rewrite H in HF. inversion HF.
      + destruct (rel_dec_p k2 k); simpl in *.
        apply rel_dec_correct in e. rewrite e in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n. eapply IH. apply ineq. assumption.
        eapply rel_dec_neq_false in n0; eauto. rewrite n0 in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n in *. eapply IH. apply ineq. assumption.
  Qed.
    
  Lemma alist_find_add_none:
    forall m (k r :K) (v:V), 
    alist_find k (alist_add r v m) = None ->
    alist_find k m = None.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - reflexivity.
    - simpl in *.
      remember (k ?[ eq ] r) as x.
      destruct x.  inversion H.
      remember (r ?[ eq] k1) as y.
      destruct y. simpl in *. symmetry in Heqy. rewrite rel_dec_correct in Heqy. subst.
      rewrite <- Heqx.
      apply (alist_find_remove_none _ k k1); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
      simpl in H.
      destruct (k ?[ eq ] k1); auto.
      apply (alist_find_remove_none _ k r); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
  Qed.      

  
  Lemma alist_find_neq : forall m (k r:K) (v:V), k <> r -> alist_find k (alist_add r v m) = alist_find k m.
  Proof.
    intros.
    remember (alist_find k (alist_add r v m)) as x.
    destruct x.
    - symmetry in Heqx. apply In_add_In_ineq in Heqx; auto.
    - symmetry in Heqx. symmetry. eapply alist_find_add_none. apply Heqx.
 Qed.
  
  
End alistFacts.
Arguments alist_find {_ _ _ _}.
Arguments alist_add {_ _ _ _}.
Arguments alist_find {_ _ _ _}.
Arguments alist_remove {_ _ _ _}. 

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.

(* Should go ext-lib *)
Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
  fix traverse__ l: M unit :=
    match l with
    | nil => ret tt
    | a::l => (f a;; traverse__ l)%monad
    end.
