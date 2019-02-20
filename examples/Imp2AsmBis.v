From ITree Require Import ITree.

Require Import Program.Basics. (* ∘ *)

(* Diagramatic/categorical sum combinators. *)

Definition id {A} (x : A) : A := x.

Definition sum_bimap {A B C D} (f : A -> B) (g : C -> D)
           (ac : A + C) : B + D :=
  match ac with
  | inl a => inl (f a)
  | inr c => inr (g c)
  end.

Definition sum_assoc_r {A B C} (abc : (A + B) + C) : A + (B + C) :=
  match abc with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition sum_assoc_l {A B C} (abc : A + (B + C)) : (A + B) + C.
Admitted.

Definition sum_elim {A B C} (f : A -> C) (g : B -> C) : A + B -> C.
Admitted.

Definition sum_merge {A} : A + A -> A := sum_elim id id.

(* ASM definition *)

(* Blocks are indexed by type of jump labels. *)
Axiom block : Type -> Type.
(* Collection of blocks labeled by [A], with jumps in [B]. *)
Definition bks A B := A -> block B.
Axiom E0 : Type -> Type.

Axiom cat_b : forall {A B C D},
    (bks A B) ->
    (bks C D) ->
    (bks (A + C) (B + D)).

Axiom rewire_b : forall {A B C D},
    (C -> A) ->
    (B -> D) ->
    (bks A B) ->
    (bks C D).

(* ASM: linked blocks, can jump to themselves *)
Record asm A B : Type := {
  internal : Type;
  code : bks (A + internal) ((A + internal) + B)
}.
Arguments internal {A B}.
Arguments code {A B}.

(* Denotations as itrees *)
Definition den A B : Type := A -> itree E0 B.
(* den can represent both blocks (A -> block B) and asm (asm A B). *)

Notation eq_den d1 d2 := (forall a, eutt eq (d1 a) (d2 a)).

(* Denotation of [bks] *)
Axiom denote_b : forall {A B}, bks A B -> den A B.

(* Denotation of [asm] *)
Definition denote_asm {A B} : asm A B -> den A B :=
  fun s a => loop (denote_b (code s)) (inl a).

(* Denotation of [cat_b] *)
Definition cat_den : forall {A B C D},
    (den A B) ->
    (den C D) ->
    (den (A + C) (B + D)).
Admitted.

(* Denotation of [rewire_b] *)
Definition rewire_den {A B C D} (f : C -> A) (g : B -> D)
           (ab : den A B) : den C D :=
  fun a => ITree.map g (ab (f a)).

(* Correctness of [cat_b] and [rewire_b] (easy) *)

Lemma cat_correct {A B C D} (ab : bks A B) (cd : bks C D) :
  eq_den (denote_b (cat_b ab cd)) (cat_den (denote_b ab) (denote_b cd)).
Admitted.

Lemma rewire_correct {A B C D} (f : C -> A) (g : B -> D) (ab : bks A B) :
  eq_den (denote_b (rewire_b f g ab)) (rewire_den f g (denote_b ab)).
Admitted.

(*
(* Sequential composition of bks. *)
Definition seq_bks {A B C} (ab : bks A (A + B)) (bc : bks B (B + C)) : bks (A + B) ((A + B) + C) :=
  let rw : (A + B) + (B + C) -> (A + B) + C :=
      sum_bimap
        (sum_bimap id sum_merge ∘ sum_assoc_r : (A + B) + B -> A + B)
        (id : C -> C) ∘ sum_assoc_l in
  rewire_b rw (cat_b ab bc).
*)

Definition rw {A I B J C} : ((A + I) + B) + ((B + J) + C) ->
      ((A + (I + (B + J))) + C).
Admitted.

Definition corw {A I B J} : (A + (I + (B + J))) -> (A + I) + (B + J).
Admitted.

(* Sequential composition of bks. *)
Definition seq_bks {A I B J C}
           (ab : bks (A + I) ((A + I) + B))
           (bc : bks (B + J) ((B + J) + C)) :
  bks (A + (I + (B + J))) ((A + (I + (B + J))) + C) :=
  rewire_b corw rw (cat_b ab bc).

(* Sequential composition of asm. *)
Definition seq_asm {A B C} (ab : asm A B) (bc : asm B C) : asm A C :=
  {| code := seq_bks (code ab) (code bc) |}.

(* Sequential composition of den. *)
Definition seq_den {A B C} (ab : den A B) (bc : den B C) : den A C :=
  fun a => ab a >>= bc.

Theorem seq_correct {A B C} (ab : asm A B) (bc : asm B C) :
  eq_den (denote_asm (seq_asm ab bc))
         (seq_den (denote_asm ab) (denote_asm bc)).
Admitted.
(* Use FixFacts.bind_loop to prove this *)
