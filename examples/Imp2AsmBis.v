From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import ITree FixFacts.

Require Import Program.Basics. (* ∘ *)

Require Import sum.
Require Import Asm.

Variable E0 : Type -> Type.
Notation den := (@den E0).

Definition cat_b {A B C D}:
    (bks A B) ->
    (bks C D) ->
    (bks (A + C) (B + D)) :=
  fun ab cd oac =>
    match oac with
    | inl a => fmap_block inl (ab a)
    | inr c => fmap_block inr (cd c)
    end.

Definition rewire_b {A B C D}:
  (C -> A) ->
  (B -> D) ->
  (bks A B) ->
  (bks C D) :=
  fun f g ab c =>
    fmap_block g (ab (f c)).

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

Opaque compose.
Opaque id.
Opaque sum_elim.

Definition rw {A I B J C} : ((A + I) + B) + ((B + J) + C) ->
      ((A + (I + (B + J))) + C) :=
  Eval compute in resum.

Transparent compose.
Transparent id.
Transparent sum_elim.

Definition corw {A I B J} : (A + (I + (B + J))) -> (A + I) + (B + J) :=
  sum_assoc_l.

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
  repeat intro.
  subst.
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

Lemma loop_relabel {A B C}
      (f : A -> B) {f' : B -> A}
      {ISO_f : Iso f f'}
      (ac : den A (A + C)) :
  eq_den (loop ac)
         (lift_den f >=> loop (lift_den f' >=> ac >=> lift_den (sum_map_l f))).
Proof.
Admitted.

Lemma seq_lift_den {A B C} (ab : A -> B) (bc : B -> C) :
  eq_den (lift_den ab >=> lift_den bc)
         (lift_den (bc ∘ ab)).
Proof.
Admitted.

Instance eq_lift_den {A B} :
  Proper (eqeq ==> eq_den) (@lift_den A B).
Proof.
  repeat intro.
Admitted.

Lemma seq_sum_elim {A B C D} (ac : den A C) (bc : den B C) (cd : den C D) :
  eq_den (sum_elim ac bc >=> cd)
         (sum_elim (ac >=> cd) (bc >=> cd)).
Proof.
Admitted.

Opaque eutt.

Lemma lift_sum_elim {A B C} (ac : A -> C) (bc : B -> C) :
  eq_den (sum_elim (lift_den ac) (lift_den bc))
         (lift_den (sum_elim ac bc)).
Proof. intros []; reflexivity. Qed.

Hint Rewrite @lift_sum_elim : lift_den.
Hint Rewrite @seq_lift_den : lift_den.

Lemma lift_den_lift_den: forall {A B C} (f: A -> B) (g: B -> C),
      eq_den (lift_den f >=> lift_den g) (lift_den (g ∘ f)).
Proof.
  intros; intros a. 
  unfold lift_den, seq_den.
  rewrite ret_bind.
  reflexivity.
Qed.

Lemma lift_den_assoc: forall {A B C D} (f: A -> B) (g: B -> C) (k: den C D),
      eq_den (lift_den f >=> (lift_den g >=> k)) (lift_den f >=> lift_den g >=> k).
Proof.
  intros; intros a.
  unfold lift_den, seq_den.
  repeat rewrite ret_bind; reflexivity.
Qed.

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
  rewrite lift_den_assoc, lift_den_lift_den.
  unfold den_sum_bimap.
  rewrite (seq_den_assoc (_ inl)).
  rewrite seq_loop_l_seq.
  unfold den_sum_map_r.
  rewrite sum_elim_loop.
  rewrite loop_loop.
  rewrite lift_den_assoc, lift_den_lift_den.
  rewrite (loop_relabel sum_assoc_r).
  repeat (rewrite seq_lift_den + rewrite <- (seq_den_assoc (lift_den _) (lift_den _))).
  apply eutt_seq_den.
  { apply eq_lift_den.
    cbv; congruence. }
  apply eutt_loop'.
  unfold corw.
  repeat rewrite seq_den_assoc + rewrite seq_lift_den.
  eapply eutt_seq_den.
  { reflexivity. }
  repeat rewrite seq_sum_elim.
  repeat rewrite seq_den_assoc + rewrite seq_lift_den.
  unfold sum_map_r, sum_map_l, sum_bimap.
  rewrite unfold_sum_assoc_r.
  unfold rw.
  autorewrite with cat.
  repeat rewrite compose_assoc.
  autorewrite with sum_elim.
  autorewrite with lift_den.
  eapply eutt_elim.
  - eapply eutt_seq_den.
    + reflexivity.
    + eapply eq_lift_den.
      intros a ? []. destruct a as [[] | ]; auto.
  - eapply eutt_seq_den.
    + reflexivity.
    + eapply eq_lift_den.
      intros a ? []; destruct a as [[] | ]; auto.
Qed.
