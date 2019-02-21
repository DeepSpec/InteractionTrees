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

(** * Category of denotations *)

Variable E0 : Type -> Type.
Instance ME0 : Memory -< E0. Admitted.
Instance LE0 : Imp.Locals -< E0. Admitted.
Notation den := (@den E0).

Instance Equivalence_eq_den {E A B} : Equivalence (@eq_den E A B).
Proof.
  split.
  - intros ab a; reflexivity.
  - intros ab ab' eqAB a; symmetry; auto.
  - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
Qed.

Instance eq_den_loop {E I A B} :
  Proper (eq_den ==> eq_den) (@loop_den E I A B).
Proof.
Admitted.

Instance eq_den_cat {E A B C} :
  Proper (eq_den ==> eq_den ==> eq_den) (@cat_den E A B C).
Proof.
  intros ab ab' eqAB bc bc' eqBC.
  intro a.
  unfold cat_den.
  rewrite (eqAB a).
  apply eutt_bind; try reflexivity.
  intros []; try reflexivity.
  rewrite (eqBC b); reflexivity.
Qed.

Instance eq_den_elim {E A B C} :
  Proper (eq_den ==> eq_den ==> eq_den) (@sum_elim A B (itree E C)).
Proof.
  repeat intro. destruct a; unfold sum_elim; auto.
Qed.

(** *** [cat_den] *)

Lemma cat_den_assoc {A B C D}
      (ab : den A B) (bc : den B C) (cd : den C D) :
  eq_den ((ab >=> bc) >=> cd)
         (ab >=> (bc >=> cd)).
Proof.
  intros a.
  unfold lift_den, cat_den.
  rewrite bind_bind.
  apply eutt_bind; try reflexivity.
  intros []; try reflexivity.
  rewrite ret_bind; reflexivity.
Qed.

Lemma cat_lift_den {E A B C} (ab : A -> B) (bc : B -> C) :
  @eq_den E _ _
     (lift_den ab >=> lift_den bc)
     (lift_den (bc ∘ ab)).
Proof.
  intros a.
  unfold lift_den, cat_den.
  rewrite ret_bind.
  reflexivity.
Qed.

Instance eq_lift_den {E A B} :
  Proper (eqeq ==> eq_den) (@lift_den E A B).
Proof.
  repeat intro.
  unfold lift_den.
  erewrite (H a); reflexivity.
Qed.

Lemma lift_den_lift_den {E A B C} (f: A -> B) (g: B -> C) :
  @eq_den E _ _ (lift_den f >=> lift_den g) (lift_den (g ∘ f)).
Proof.
  intros a.
  unfold lift_den, cat_den.
  rewrite ret_bind.
  reflexivity.
Qed.

Lemma cat_lift_den_l {A B C D} (f: A -> B) (g: B -> C) (k: den C D) :
  eq_den
    (lift_den f >=> (lift_den g >=> k))
    (lift_den (g ∘ f) >=> k).
Proof.
  rewrite <- cat_den_assoc.
  rewrite cat_lift_den.
  reflexivity.
Qed.

(* For completeness. *)
Lemma cat_lift_den_r {A B C D} (f: B -> C) (g: C -> D) (k: den A B) :
  eq_den
    ((k >=> lift_den f) >=> lift_den g)
    (k >=> lift_den (g ∘ f)).
Proof.
  rewrite cat_den_assoc.
  rewrite cat_lift_den.
  reflexivity.
Qed.

(* Low-level *)
Lemma lift_cat_den {A B C}: forall (f:A -> B) (bc: den B C),
      eq_den (lift_den f >=> bc) (fun a => bc (f a)).
Proof.
  intros; intro a.
  unfold lift_den, cat_den.
  rewrite ret_bind; reflexivity.
Qed.

Lemma cat_den_lift {A B C}: forall (ab: den A B) (g:B -> C),
      eq_den (ab >=> lift_den g)
             (fun a => ITree.map (sum_bimap g id) (ab a)).
Proof.
  intros; intro a.
  unfold cat_den.
  unfold ITree.map.
  apply eutt_bind.
  reflexivity.
  intros []; reflexivity.
Qed.

(** *** [juxta] lemmas *)

Lemma juxta_swap {A B C D} (ab : den A B) (cd : den C D) :
  eq_den (juxta_den ab cd)
         (lift_den sum_comm >=> juxta_den cd ab >=> lift_den sum_comm).
Proof.
  unfold juxta_den.
  rewrite !(cat_den_lift cd), !(cat_den_lift ab), !lift_cat_den, !cat_den_lift.
  intros []; cbn; rewrite map_map; cbn;
    apply eutt_map; try intros []; reflexivity.
Qed.

(* Unused but should go to FixFacts *)
Instance eutt_loop {E A B} :
  Proper ((eq ==> eutt eq) ==> eq ==> eutt eq) (@aloop E A B).
Proof.
Admitted. 

Instance eutt_loop' {E A B} :
  Proper (eq_den ==> eq_den) (@aloop E A B).
Proof.
Admitted.

Lemma juxta_id_lift {E A B C} (f : B -> C) :
  eq_den (juxta_den (@id_den E A) (lift_den f))
         (lift_den (sum_bimap id f)).
Proof.
Admitted.

Lemma juxta_lift_id {E A B C} (f : A -> B) :
  eq_den (juxta_den (lift_den f) (@id_den E C))
         (lift_den (sum_bimap f id)).
Proof.
Admitted.

Hint Rewrite @cat_den_assoc : lift_den.
Hint Rewrite @lift_den_lift_den : lift_den.
Hint Rewrite @cat_lift_den_l : lift_den.
Hint Rewrite @juxta_id_lift : lift_den.
Hint Rewrite @juxta_lift_id : lift_den.

(** *** [sum_elim] lemmas *)

Lemma cat_sum_elim {A B C D} (ac : den A C) (bc : den B C) (cd : den C D) :
  eq_den (sum_elim ac bc >=> cd)
         (sum_elim (ac >=> cd) (bc >=> cd)).
Proof.
Admitted.

Opaque eutt.

Lemma lift_sum_elim {E A B C} (ac : A -> C) (bc : B -> C) :
  @eq_den E _ _
    (sum_elim (lift_den ac) (lift_den bc))
    (lift_den (sum_elim ac bc)).
Proof. intros []; reflexivity. Qed.

Hint Rewrite @lift_sum_elim : lift_den.
Hint Rewrite @cat_lift_den : lift_den.

(* Denotation of [rewire_b] *)
Definition rewire_den {A B C D} (f : C -> A) (g : B -> D)
           (ab : den A B) : den C D :=
  fun a => ITree.map (sum_map_l g) (ab (f a)).

Notation rewire_den' f g ab := (lift_den f >=> ab >=> lift_den g)%den
  (only parsing).

Lemma unfold_rewire_den {A B C D} (f : C -> A) (g : B -> D)
      (ab : den A B) :
  eq_den (rewire_den f g ab)
         (rewire_den' f g ab).
Proof.
  rewrite lift_cat_den, cat_den_lift.
  reflexivity.
Qed.

Instance eq_den_rewire_den {A B C D} :
  Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq_den ==> eq_den)
         (@rewire_den A B C D).
Proof.
  intros f f' eqf g g' eqg ab ab' eqAB.
  do 2 rewrite unfold_rewire_den.
  rewrite eqf, eqg, eqAB; reflexivity.
Qed.

Lemma seq_loop_l {I A B C}
      (ab : den (I + A) (I + B)) (bc : den B C) :
  eq_den (loop_den ab >=> bc)
         (loop_den (rewire_den' (sum_assoc_r ∘ sum_bimap sum_comm id)
                                sum_comm
                                (juxta_den bc ab))).
Proof.
Admitted.

Lemma seq_loop_r {I A B C}
      (ab : den A B) (bc : den (I + B) (I + C)) :
  eq_den (ab >=> loop_den bc)
         (loop_den (rewire_den' sum_comm
                                (sum_bimap sum_comm id ∘ sum_assoc_l)
                                (juxta_den ab bc))).
Proof.
Admitted.

(* Should be a consequence of the others. *)
Lemma seq_loop_l_seq {A B C I}
      (ab : den (I + A) (I + B)) (bc : den B C) :
  eq_den (loop_den ab >=> bc)
         (loop_den (ab >=> juxta_den id_den bc)).
Proof.
Admitted.

(* Should be a consequence of the others *)
Lemma seq_loop_r_seq {A B C I}
      (ab : den A B) (bc : den (I + B) (I + C)) :
  eq_den (ab >=> loop_den bc)
         (loop_den (juxta_den id_den ab >=> bc)).
Proof.
Admitted.

(* [loop_loop]:

These two loops:

[[
    +----------+
    | +-----+  |
    | | ### |  |
    | +-###-+I |
    +---###----+J
  A-----###-------B
        ###
]]

... can be rewired as a single one:


[[
     +-------+
     |  ###  |
     +--###--+(I+J)
     +--###--+
  A-----###-----B
        ###
]]

*)
Lemma loop_loop {I J A B}
      (ab : den (I + (J + A)) (I + (J + B))) :
  eq_den (loop_den (loop_den ab))
         (loop_den (rewire_den' sum_assoc_r sum_assoc_l ab)).
Proof.
Admitted.

Lemma juxta_den_loop {I A B C D}
      (ab : den (I + A) (I + B)) (cd : den C D) :
  eq_den (juxta_den (loop_den ab) cd)
         (loop_den (rewire_den' sum_assoc_l sum_assoc_r
                                (juxta_den ab cd))).
Proof.
Admitted.

Lemma loop_relabel {I J A B}
      (f : I -> J) {f' : J -> I}
      {ISO_f : Iso f f'}
      (ab : den (I + A) (I + B)) :
  eq_den (loop_den ab)
         (loop_den (rewire_den' (sum_bimap f' id) (sum_bimap f id) ab)).
Proof.
Admitted.

(**)

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

(* Correctness of [cat_b] and [rewire_b] (easy)
   YZ: Those depend on the implementation. Should they be assumed by the theory?
 *)

Lemma cat_correct {A B C D} (ab : bks A B) (cd : bks C D) :
  eq_den (denote_b E0 (cat_b ab cd))
         (juxta_den (denote_b _ ab) (denote_b E0 cd)).
Admitted.

Lemma rewire_correct {A B C D} (f : C -> A) (g : B -> D) (ab : bks A B) :
  eq_den (denote_b _ (rewire_b f g ab))
         (rewire_den' f g (denote_b _ ab)).
Admitted.

Opaque compose.
Opaque id.
Opaque sum_elim.

Definition rw {I B J C} :
  (I + B) + (J + C) -> (I + J + B) + C :=
  Eval compute in resum.

Definition corw {A I B J} : (I + J + B) + A -> (I + A) + (J + B) :=
  Eval compute in resum.

Transparent compose.
Transparent id.
Transparent sum_elim.


(* Sequential composition of bks. *)
Definition seq_bks {A I B J C}
           (ab : bks (I + A) (I + B))
           (bc : bks (J + B) (J + C)) :
  bks ((I + J + B) + A) ((I + J + B) + C) :=
  rewire_b corw rw (cat_b ab bc).

(* Sequential composition of asm. *)
Definition seq_asm {A B C} (ab : asm A B) (bc : asm B C) : asm A C :=
  {| code := seq_bks (code ab) (code bc) |}.

Theorem seq_correct {A B C} (ab : asm A B) (bc : asm B C) :
  @eq_den E0 _ _
    (denote_asm (seq_asm ab bc))
    (cat_den (denote_asm ab) (denote_asm bc)).
Proof.
  unfold denote_asm, seq_asm; simpl.
  unfold seq_bks.
  rewrite rewire_correct.
  rewrite cat_correct.
  rewrite seq_loop_l.
  rewrite juxta_den_loop.
  rewrite seq_loop_r_seq.
  rewrite seq_loop_l_seq.
  rewrite loop_loop.
  rewrite (juxta_swap (_ (code bc))).
  rewrite (loop_relabel (sum_bimap sum_comm id ∘ sum_assoc_l)).
  autorewrite with lift_den.
  (* Now everything matches except [lift_den] *)
  apply eq_den_loop.
  apply eq_den_cat.
  - apply eq_lift_den.
    intros [[[] | ] | ] ? []; auto.
  - apply eq_den_cat.
    + reflexivity.
    + apply eq_lift_den.
      intros [[] | [] ] ? []; auto.
Qed.
