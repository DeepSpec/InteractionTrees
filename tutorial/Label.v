From ITree Require Import
     Basics.Basics
     Basics.Function
     ITree
     Basics.Category
     SubKTree.

From Coq Require Import
     Psatz
     Vectors.Fin.

Require Import Program.Equality.

Global Instance FinEmbedding: Embedding nat := Fin.t.
Global Instance FinInitial: Embedded_initial 0 :=
  {|
    iI_void := fun (v: Fin.t 0) => match v with end;
    void_iI := fun v => match v with end;
  |}.



Definition fin_case {n : nat} (k : Fin.t (S n)) : forall R, R -> (Fin.t n -> R) -> R :=
  match k with
  | F1 => fun _ r _ => r
  | FS k => fun _ _ f => f k
  end.

Arguments fin_case {n} k [R].

Definition split_fin_S (n: nat) (k: Fin.t (S n)) : (Fin.t 1) + (Fin.t n) :=
  match k with
  | F1 => inl F1
  | FS k => inr k
  end.

Definition split_fin_sum_ (m: nat) :=
  nat_rec (fun n => Fin.t (n + m) -> Fin.t n + Fin.t m)
          (fun k => inr k)
          (fun n IH (k: Fin.t (S n + m)) =>
             match split_fin_S (n + m) k with
             | inl _ => inl F1
             | inr k => match IH k with
                       | inl k => inl (FS k)
                       | inr k => inr k
                       end
             end
          ).

Definition split_fin_sum n m := split_fin_sum_ m n. 

Definition merge_fin_sum (n m: nat): Fin.t n + Fin.t m -> Fin.t (n + m) :=
  fun v => 
    match v with
    | inl v => L m v
    | inr v => R n v
    end.

Global Instance FinSum: Embedded_sum plus :=
  {|
    isum_sum := split_fin_sum;
    sum_isum := merge_fin_sum
  |}.

Definition fin_case_ind {n} (k : Fin.t (S n)) : forall
        (P : Fin.t (S n) -> Prop)
        (P_r : P F1)
        (P_f : forall (k : Fin.t n), P (FS k))
  , P k :=
  match k in Fin.t m return
        match m with
        | O => fun _ => False
        | S n => fun k => forall
        (P : Fin.t (S n) -> Prop)
        (P_r : P F1)
        (P_f : forall (k : Fin.t n), P (FS k)), P k
        end k with
  | F1 => fun _ P_r _ => P_r
  | FS k => fun _ _ P_f => P_f k
  end.

Definition unique_F1 (r1 : Fin.t 1) : r1 = F1 :=
  fin_case_ind r1 (fun r1 => r1 = F1) eq_refl (case0 _).

Lemma split_fin_S_left:
  forall (n: nat) (k : Fin.t (S n)) t,
    split_fin_S n k = inl t -> k = F1. 
Proof.
  unfold split_fin_S.
  intros; dependent destruction k; [reflexivity | inversion H].
Qed.

Definition to_nat' {n: nat} (k: Fin.t n): nat := proj1_sig (to_nat k).

Lemma to_nat'_FS {n} (k: Fin.t n):
  to_nat' (FS k) = S (to_nat' k).
Proof.
  unfold to_nat'; simpl; destruct (to_nat k); reflexivity. 
Qed.

Lemma split_fin_S_right:
  forall (n: nat) (k : Fin.t (S n)) t,
    split_fin_S n k = inr t -> to_nat' k = S (to_nat' t). 
Proof.
  unfold split_fin_S.
  intros; dependent destruction k.
  - inv H.
  - inv H; apply to_nat'_FS. 
Qed.

Arguments split_fin_sum {n m}.

Lemma split_fin_sum_left:
  forall {n m} (k: Fin.t (n + m)) k',
    split_fin_sum k = inl k' ->
    to_nat' k = to_nat' k'.
Proof.
  induction n as [| n IH]; simpl; intros.
  - inv H.
  - destruct (split_fin_S (n + m) k) eqn:EQ.
    + apply split_fin_S_left in EQ; subst.
      inv H; reflexivity.
    + destruct (split_fin_sum t) eqn: EQ'.
      * inv H.
        apply IH in EQ'.
        rewrite to_nat'_FS.
        apply split_fin_S_right in EQ.
        rewrite EQ, <- EQ'; reflexivity.
      * inv H.
Qed.

(* Admitted for now, TODO *)
Global Instance FinSumIso {n m: nat}: Iso Fun (@split_fin_sum n m) (@merge_fin_sum n m).
Admitted.

Global Instance FiniIIso: Iso Fun iI_void void_iI := {}.
intros x; inversion x.
intros x; inversion x.
Defined.
