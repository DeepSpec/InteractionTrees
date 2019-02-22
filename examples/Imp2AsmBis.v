From Coq Require Import
     Program
     Lia
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     ITree
     FixFacts
     Basics_Functions.

Require Import Program.Basics. (* ∘ *)

Require Import Den.

Section Linking.

  Variable E0 : Type -> Type.
  Notation den := (@den E0).

  (* Definition cat_b {A B C D}: *)
  (*   (bks A B) -> *)
  (*   (bks C D) -> *)
  (*   (bks (A + C) (B + D)) := *)
  (*   fun ab cd oac => *)
  (*     match oac with *)
  (*     | inl a => fmap_block inl (ab a) *)
  (*     | inr c => fmap_block inr (cd c) *)
  (*     end. *)

  (* Definition rewire_b {A B C D}: *)
  (*   (C -> A) -> *)
  (*   (B -> D) -> *)
  (*   (bks A B) -> *)
  (*   (bks C D) := *)
  (*   fun f g ab c => *)
  (*     fmap_block g (ab (f c)). *)

  (*  
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
   *)

  (* Opaque compose. *)
  (* Opaque id. *)
  (* Opaque sum_elim. *)

  (* Definition rw {I B J C} : *)
  (*   (I + B) + (J + C) -> (I + J + B) + C := *)
  (*   Eval compute in resum. *)

  (* Definition corw {A I B J} : (I + J + B) + A -> (I + A) + (J + B) := *)
  (*   Eval compute in resum. *)

  (* Transparent compose. *)
  (* Transparent id. *)
  (* Transparent sum_elim. *)


  (* Sequential composition of bks. *)

(*
  Definition rw {I B J C} :
    (I + B) + (J + C) -> (I + J + B) + C :=
    Eval compute in resum.

  Definition corw {A I B J} : (I + J + B) + A -> (I + A) + (J + B) :=
    Eval compute in resum.


  Definition rewire_b {A B C D}:
    (C -> A) ->
    (B -> D) ->
    (bks A B) ->
    (bks C D) :=
    fun f g ab c =>
      fmap_block g (ab (f c)).

  Definition cat_b {A B C D}:
    (bks A B) ->
    (bks C D) ->
    (bks (A + C) (B + D)) :=
    fun ab cd oac =>
      match oac with
      | inl a => fmap_block inl (ab a)
      | inr c => fmap_block inr (cd c)
      end.

  Definition seq_bks {A I B J C}
             (ab : bks (I + A) (I + B))
             (bc : bks (J + B) (J + C)) :
    bks ((I + J + B) + A) ((I + J + B) + C) :=
    rewire_b corw rw (cat_b ab bc).

*)

  (* TODO: redefine seq_den purely in term of Den.v *)
  (*
  Definition seq_den {A I B J C}
             (ab: den (I + A) (I + B))
             (bc: den (J + B) (J + C)) :=
    den ((I + J + B) + A) ((I + J + B) + C) :=
      _

  Theorem seq_correct {A B C} (ab : den A B) (bc : den B C) :
     (seq_den ab bc) ⩰ ab >=> bc.
  Proof.
    unfold denote_asm, seq_asm; simpl.
    unfold seq_bks.
*)

(*    
      Can we prove this without rewire?
      In particular, need loop_loop
      
    (* rewrite rewire_correct. *)
    (* rewrite cat_correct. *)
    rewrite seq_loop_l.
    rewrite tensor_den_loop.
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
 *)

  (* Qed. *)
