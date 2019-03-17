(* A version of [Fin] that may be easier to use than the standard one.
 *)

Fixpoint Fin (n : nat) : Type :=
  match n with
  | O => Empty_set
  | S n' => option (Fin n')
  end.

Definition F1 {n : nat} : Fin (S n) := None.
Definition FS {n : nat} : Fin n -> Fin (S n) := Some.

Fixpoint split_fin_sum {n m : nat}
  : Fin (n + m) -> (Fin n) + (Fin m)
  := match n with
     | O => inr
     | S n' => fun k =>
       match k with
       | None => inl None
       | Some k' =>
         match split_fin_sum k' with
         | inl l' => inl (Some l')
         | inr r' => inr r'
         end
       end
     end.

Fixpoint inl_fin_sum {n m : nat} : Fin n -> Fin (n + m)
  := match n with
     | O => fun k => match k : Empty_set with end
     | S n => fun k =>
       match k with
       | None => None
       | Some k' => Some (inl_fin_sum k')
       end
     end.

Fixpoint inr_fin_sum {n m : nat} (k : Fin m) : Fin (n + m)
  := match n with
     | O => k
     | S n' => FS (inr_fin_sum k)
     end.

Definition merge_fin_sum {n m : nat} (k : Fin n + Fin m)
  : Fin (n + m)
  := match k with
     | inl l => inl_fin_sum l
     | inr r => inr_fin_sum r
     end.

Lemma inl_split_fin_sum {n m : nat} (k : Fin n)
  : @split_fin_sum n m (inl_fin_sum k) = inl k.
Proof.
  revert k; induction n; intros k.
  - inversion k.
  - (* Definitely Not Magic *)
    destruct k; cbn.
    + rewrite IHn; reflexivity.
    + reflexivity.
Qed.

Lemma inr_split_fin_sum {n m : nat} (k : Fin m)
  : @split_fin_sum n m (inr_fin_sum k) = inr k.
Proof.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma merge_split_fin_sum {n m : nat} (k : Fin n + Fin m)
  : split_fin_sum (merge_fin_sum k) = k.
Proof.
  destruct k; cbn.
  - apply inl_split_fin_sum.
  - apply inr_split_fin_sum.
Qed.

Lemma split_merge_fin_sum {n m : nat} (k : Fin (n + m))
  : merge_fin_sum (split_fin_sum k) = k.
Proof.
  revert k; induction n; intros k.
  - reflexivity.
  - destruct k; cbn.
    + specialize (IHn f).
      destruct split_fin_sum; cbn in *; rewrite IHn; reflexivity.
    + reflexivity.
Qed.
