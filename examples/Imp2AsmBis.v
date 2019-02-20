
From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.


From ITree Require Import ITree FixFacts.

Require Import Program.Basics. (* ∘ *)

  Set Nested Proofs Allowed.

(* Diagramatic/categorical sum combinators. *)

Definition id {A} (x : A) : A := x.

Definition sum_elim {A B C} (f : A -> C) (g : B -> C) : A + B -> C :=
  fun x =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

Definition sum_bimap {A B C D} (f : A -> B) (g : C -> D) :
  A + C -> B + D :=
  sum_elim (inl ∘ f) (inr ∘ g).

Definition sum_map_l {A B C} (f : A -> B) : A + C -> B + C :=
  sum_bimap f id.

Definition sum_map_r {A B C} (f : A -> B) : C + A -> C + B :=
  sum_bimap id f.

Definition sum_assoc_r {A B C} (abc : (A + B) + C) : A + (B + C) :=
  match abc with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition sum_comm {A B} : A + B -> B + A :=
  sum_elim inr inl.

Definition sum_assoc_l {A B C} (abc : A + (B + C)) : (A + B) + C.
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

Notation eq_den_ d1 d2 := (forall a, eutt eq (d1 a) (d2 a)).

Definition eq_den {E A B} (d1 d2 : A -> itree E B) :=
  (forall a, eutt eq (d1 a) (d2 a)).

(* Sequential composition of den. *)
Definition seq_den {A B C} (ab : den A B) (bc : den B C) : den A C :=
  fun a => ab a >>= bc.

Infix ">=>" := seq_den (at level 40).

Definition id_den {A} : den A A := fun a => Ret a.

Definition lift_den {A B} (f : A -> B) : den A B := fun a => Ret (f a).

Definition den_sum_map_r {A B C} (ab : den A B) : den (C + A) (C + B) :=
  sum_elim (lift_den inl) (ab >=> lift_den inr).

Definition den_sum_bimap {A B C D} (ab : den A B) (cd : den C D) :
  den (A + C) (B + D) :=
  sum_elim (ab >=> lift_den inl) (cd >=> lift_den inr).

(* Denotation of [bks] *)
Axiom denote_b : forall {A B}, bks A B -> den A B.

(* Denotation of [asm] *)
Definition denote_asm {A B} : asm A B -> den A B :=
  fun s => seq_den (lift_den inl) (loop (denote_b (code s))).

(* A denotation of an asm program can be viewed as a circuit/diagram
   where wires correspond to jumps/program links.

   A [box : den A (A + B)] is a circuit, drawn below as ###,
   with one input wire labeled by A, and two output wires labeled
   by A and B.

   The [loop : den A (A + B) -> den A B] combinator closes the
   circuit, linking the box with itself by plugging the A output
   back into the output.

     +-----+
     | ### |
  A--+-###-+
       ###----B
       ###

 *)

(* Denotation of [cat_b] *)
Definition cat_den {A B C D} :
    (den A B) ->
    (den C D) ->
    (den (A + C) (B + D)) := den_sum_bimap.

(* Denotation of [rewire_b] *)
Definition rewire_den {A B C D} (f : C -> A) (g : B -> D)
           (ab : den A B) : den C D :=
  fun a => ITree.map g (ab (f a)).

Lemma unfold_rewire_den {A B C D} (f : C -> A) (g : B -> D)
      (ab : den A B) :
  eq_den (rewire_den f g ab)
         (lift_den f >=> ab >=> lift_den g).
Proof.
Admitted.

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

(* Unused but should go to FixFacts *)
Instance eutt_loop {E A B} :
  Proper ((eq ==> eutt eq) ==> eq ==> eutt eq) (@loop E A B).
Proof.
Admitted.

Instance eutt_loop' {E A B} :
  Proper (eq_den ==> eq_den) (@loop E A B).
Proof.
Admitted.

Instance eutt_rewire_den {A B C D} :
  Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq_den ==> eq_den)
         (@rewire_den A B C D).
Proof.
Admitted.

Instance eutt_seq_den {A B C} :
  Proper (eq_den ==> eq_den ==> eq_den) (@seq_den A B C).
Proof.
Admitted.

Instance Equivalence_eq_den {E A B} : Equivalence (@eq_den E A B).
Proof.
Admitted.

Lemma seq_den_assoc {A B C D}
      (ab : den A B) (bc : den B C) (cd : den C D) :
  eq_den ((ab >=> bc) >=> cd)
         (ab >=> (bc >=> cd)).
Proof.
Admitted.

Lemma seq_loop_l {A B C}
      (ab : den A (A + B)) (bc : den B C) :
  eq_den (loop ab >=> bc)
         (lift_den inl >=> loop (den_sum_bimap ab bc)).
Proof.
Admitted.

Lemma seq_loop_l_seq {A B C}
      (ab : den A (A + B)) (bc : den B C) :
  eq_den (loop ab >=> bc)
         (loop (ab >=> den_sum_map_r bc)).
Proof.
Admitted.

(*
Lemma seq_loop_r {A B C}
      (ab : den A B) (bc : den B (B + C)) :
  eq_den (ab >=> loop bc)
         (loop (
*)

Instance eutt_elim {E A B C} :
  Proper (eq_den ==> eq_den ==> eq_den) (@sum_elim A B (itree E C)).
Proof.
  repeat intro. destruct a; unfold sum_elim; auto.
Qed.

(*

loop_loop (f : A -> B) (box : den B (B + (A + C))):

These two loops (where wires represent jumps):

        +------------+
        |   +-----+  |
        |   | ### |  |
        | f-+-###-+B |
     A--+-+   ###----+A
              ###-------C
              ###

Can be rewired as:

            +---------+
            | ###     |
          +-+-###--+--+B
     A----+f  ###--+f    <- A
              ###------C
              ###

*)
Lemma loop_loop {A B C}
      (f : A -> B) (bc : den B (B + (A + C))) :
  eq_den (loop (lift_den f >=> loop bc))
         (lift_den f
             >=> loop (bc >=> lift_den (sum_elim inl (sum_elim (inl ∘ f) inr)))).
Proof.
Admitted.

Lemma sum_elim_loop {A B C BD}
      (f : B -> BD)
      (ac : den A C) (bc : den BD (BD + C)) :
  eq_den (sum_elim ac
                   (lift_den f >=> loop bc))
         (lift_den (sum_map_r f)
            >=> loop (sum_elim (ac >=> lift_den inr)
                               (bc >=> lift_den (sum_map_l inr)))).
Proof.
Admitted.

Theorem seq_correct {A B C} (ab : asm A B) (bc : asm B C) :
  eq_den (denote_asm (seq_asm ab bc))
         (seq_den (denote_asm ab) (denote_asm bc)).
Proof.
  unfold denote_asm, seq_asm; simpl.
  unfold seq_bks.
  rewrite rewire_correct.
  rewrite cat_correct.
  unfold cat_den.
  rewrite unfold_rewire_den.
  rewrite (seq_den_assoc (_ inl)).
  rewrite seq_loop_l.
  unfold den_sum_bimap.
  rewrite (seq_den_assoc (_ inl)).
  rewrite seq_loop_l_seq.
  unfold den_sum_map_r.
  rewrite sum_elim_loop.
  rewrite loop_loop.

Arguments loop : clear implicits.

Qed.
Admitted.
