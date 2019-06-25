From ITree Require Import
     Basics.Basics
     Basics.Function
     ITree
     Basics.Category
     SubKTree.

From Coq Require Import
     Psatz
     Omega
     ProofIrrelevance
     ProofIrrelevanceFacts.

Require Import Program.Equality.

Definition fin (n:nat) := {x:nat | x < n}.

Program Definition f1 {n} : fin (S n) := _.
Next Obligation.
  exists 0. lia.
Defined.  

Lemma unique_f1 : forall (a : fin 1), a = f1.
Proof.
  destruct a. destruct f1. apply subset_eq_compat.
  lia.
Qed.
  
Program Definition FS {n} : fin n -> fin (S n) := _.
Next Obligation.
  destruct H.
  exists (S x). lia.
Defined.  

Lemma fin_0 : fin 0 -> void.
Proof.
  intros.
  destruct H.
  apply PeanoNat.Nat.nlt_0_r in l. 
  contradiction.
Qed.

Global Instance FinEmbedding: Embedding nat := fin.
Global Instance FinInitial: Embedded_initial 0 :=
  {|
    iI_void := fin_0;
    void_iI := fun v => match v with end;
  |}.

Lemma split_fin_helper:
  forall n m x : nat, x < n + m -> ~ x < n -> x - n < m.
Proof.
  intros n m x l n0.
  lia.
Defined.
  
Program Definition split_fin_sum (n:nat) (m:nat) : fin (n+m) -> (fin n) + (fin m) := _.
Next Obligation.
  destruct H.
  destruct (Compare_dec.lt_dec x n).
  - left. exists x. assumption.
  - right.
    exists (x - n).
    apply split_fin_helper; assumption.
Defined.

Program Definition L {n} (m:nat) (a:fin n) : fin (n + m) := _.
Next Obligation.
  destruct a.
  exists x. apply PeanoNat.Nat.lt_lt_add_r.  assumption.
Defined.

Program Definition R {m} (n:nat) (a:fin m) : fin (n + m) := _.
Next Obligation.
  destruct a.
  exists (n + x). lia.
Defined.

Lemma R_0_a : forall (n:nat) (a : fin n), R 0 a = a.
Proof.
  intros.
  destruct a. simpl.
  apply subset_eq_compat. reflexivity.
Qed.  

Lemma R_1_a : forall (n:nat) (a : fin n), R 1 a = FS a.
Proof.
  intros.
  destruct a. simpl.
  apply subset_eq_compat. reflexivity.
Qed.  


Lemma split_fin_sum_0_a : forall m (a : fin (0 + m)),
    (@split_fin_sum 0 m a) = inr a.
Proof.
  intros.
  unfold split_fin_sum, split_fin_sum_obligation_1.
  destruct a.
  destruct (Compare_dec.lt_dec x 0).
  - inversion l0.
  - assert ((exist (fun x0 : nat => x0 < m) (x - 0) (split_fin_helper 0 m x l n)) =
            (exist (fun x0 : nat => x0 < 0 + m) x l)).
    { apply subset_eq_compat. lia. }
    rewrite H. reflexivity.
Qed.

Lemma split_fin_sum_FS_inr :
  (@split_fin_sum (S O) (S O) (FS f1) = inr f1).
Proof.
  cbn.
  f_equal.
  apply subset_eq_compat. reflexivity.
Qed.

Lemma split_fin_sum_f1_inl :
  (@split_fin_sum 1 1 (@f1 1)) = inl f1.
Proof.
  simpl. f_equal. apply subset_eq_compat. reflexivity.
Qed.

Lemma L_1_f1 : (L 1 (@f1 0)) = f1.
Proof.
  destruct f1. simpl.
  apply subset_eq_compat. lia.
Qed.  

Lemma split_fin_sum_L_L_f1 : 
  (@split_fin_sum _ _ (L 1 (L 1 (@f1 0)))) = inl f1.
Proof.
  rewrite L_1_f1.
  destruct f1. simpl.
  destruct (lt_dec x 2).
  - f_equal. apply subset_eq_compat. reflexivity.
  - contradiction.
Qed.    
  
Lemma split_fin_sum_R_2 : split_fin_sum _ _ (R 2 (@f1 0)) = inr f1.
Proof.
  destruct f1. simpl.
  f_equal. apply subset_eq_compat. lia.
Qed.  

Definition merge_fin_sum (n m: nat): fin n + fin m -> fin (n + m) :=
  fun v => 
    match v with
    | inl v => L m v
    | inr v => R n v
    end.

Lemma merge_fin_sum_inr : (merge_fin_sum 1 1 (inr f1)) = (FS f1).
Proof.
  simpl. apply subset_eq_compat. reflexivity.
Qed.
  
Lemma merge_fin_sum_inl_1 : forall f, (merge_fin_sum 1 1 (inl f)) = f1.
Proof.
  destruct f. simpl. 
  apply subset_eq_compat. lia.
Qed.  
  
Global Instance FinSum: Embedded_sum plus :=
  {|
    isum_sum := split_fin_sum;
    sum_isum := merge_fin_sum
  |}.

Arguments split_fin_sum {n m}.


Lemma merge_split:
  forall (n m : nat) (a : fin (n + m)), merge_fin_sum n m (split_fin_sum a) = a.
Proof.
  intros n m a.
  destruct a.
  simpl.
  unfold split_fin_sum, split_fin_sum_obligation_1.
  destruct (Compare_dec.lt_dec x n).
  - simpl. assert ((PeanoNat.Nat.lt_lt_add_r x n m l0) = l).
    { apply proof_irrelevance. }
    rewrite H. reflexivity.
  - simpl.
    eapply subset_eq_compat.
    lia.
Qed.


Lemma split_merge:
  forall (n m : nat) (a : fin n + fin m), split_fin_sum (merge_fin_sum n m a) = a.
Proof.
  intros n m.
  intros.
  destruct a; simpl.
  - destruct f. simpl.
    destruct (Compare_dec.lt_dec x n).
    + assert ((exist (fun x0 : nat => x0 < n) x l0) = (exist (fun x0 : nat => x0 < n) x l)).
      { apply subset_eq_compat. reflexivity. }
      rewrite H. reflexivity.
    + contradiction.
  - destruct f. simpl.
    destruct (Compare_dec.lt_dec (n+x) n).
    + omega.  (* SAZ: TODO - find a nicer proof rather than use omega? *)
    + f_equal.
      apply subset_eq_compat. lia. 
Qed.
    

Global Instance FinSumIso {n m: nat}: Iso Fun (@split_fin_sum n m) (@merge_fin_sum n m).
Proof.
  split; unfold SemiIso, eq2, eeq, id_, Id_Fun, cat, Cat_Fun.
  - apply merge_split.
  - apply split_merge.
Qed.      

Global Instance FiniIIso: Iso Fun iI_void void_iI := {}.
- intros x. destruct x. omega.
- intros x. destruct x.
Defined.
