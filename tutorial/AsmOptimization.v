(* begin hide *)
Require Import Asm Utils_tutorial.

Require Import Psatz.

From Coq Require Import
     Lists.List
     Strings.String
     Morphisms
     ZArith
     Setoid
     RelationClasses.

From ITree Require Import
     ITree
     ITreeFacts
     Events.StateFacts
     Events.Map.

Import ITreeNotations.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Programming.Show
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.
(* end hide *)


Definition optimization {A B} := asm A B -> asm A B.


Definition optimization_correct (opt:optimization) :=
  forall (p : asm unit void),
    AsmEval p ≈ AsmEval (opt p).


(* peephole optimizations *)

Definition peephole_optimization := instr -> list instr.

Fixpoint blk_append {lbl} (l:list instr) (b:block lbl) : block lbl :=
  match l with
  | [] => b
  | i :: l' => bbi i (blk_append l' b)
  end.

(* TODO: generalize effect type *)
Fixpoint denote_instr_list (l:list instr) : itree (Imp.Locals +' Memory +' Exit) unit :=
  match l with
  | [] => ret tt
  | i::l' => denote_instr i ;; denote_instr_list l'
  end.

Lemma denote_blk_append : forall lbl (l:list instr) (b:block lbl),
    denote_block (blk_append l b) ≈ (x <- denote_instr_list l ;; denote_block b).
Proof.
  intros lbl.
  induction l; intros b; simpl.
  - rewrite bind_ret. reflexivity.
  - rewrite bind_bind.
    apply eutt_bind. red. intros. apply IHl. reflexivity.
Qed.    

Fixpoint peephole_optimize_block {lbl} (ph : peephole_optimization) (b:block lbl) : block lbl :=
  match b with
  | bbi i k => blk_append (ph i) (peephole_optimize_block ph k)
  | bbb l => bbb l
  end.

Definition peephole_optimize_bks {A B} (ph : peephole_optimization) (bs : A -> block B) :=
  fun (a:A) => peephole_optimize_block ph (bs a).

Definition peephole_optimize_asm {A B} (ph : peephole_optimization) (p : asm A B) : asm A B :=
  Build_asm A B (p.(internal)) (peephole_optimize_bks ph (p.(code))).

About Exit.
Print Exit.

Definition h : Handler (Imp.Locals +' Memory +' Exit)  ((mapE Imp.var Imp.value) +' ((mapE Imp.value Imp.value) +' Exit)) :=
  (bimap Imp.evalLocals (bimap evalMemory (id_ _))).

Definition ph_correct (ph : peephole_optimization) :=
  forall i, interp h (denote_instr i) ≈ interp h (denote_instr_list (ph i)).

Lemma ph_correct_append : forall (ph : peephole_optimization) (H : ph_correct ph)
  lbl b1 b2 i,
    interp h (denote_block b1) ≈ interp h ((denote_block b2) : itree (Imp.Locals +' Memory +' Exit) lbl)  ->
    interp h (denote_instr i ;; denote_block b1) ≈ interp h (denote_block (blk_append (ph i) b2)).
Proof.
  intros ph H lbl b1 b2 i HP.
  rewrite denote_blk_append.
  unfold ph_correct in H.
  rewrite interp_bind.
  rewrite H.
  rewrite interp_bind.
  apply eutt_bind. red.  intros. apply HP.
  reflexivity.
Qed.  


Lemma peephole_block_correct : 
  forall (ph : peephole_optimization)
    (H : ph_correct ph)
    lbl
    (b : block lbl),
          (interp h ((denote_block b) : itree (Imp.Locals +' Memory +' Exit) lbl)) ≈
          (interp h (denote_block (peephole_optimize_block ph b) : itree (Imp.Locals +' Memory +' Exit) lbl)).
Proof.
  intros ph H lbl b.
  induction b.
  - unfold h in *.
    simpl.
    rewrite ph_correct_append.
    reflexivity.
    assumption.
    apply IHb.
  - reflexivity.
Qed.    

Lemma peephole_optimization_correct : forall (ph : peephole_optimization) (H : ph_correct ph),
    optimization_correct (peephole_optimize_asm ph).
Proof.
  intros ph H.
  unfold optimization_correct.
  intros p.
  destruct p.
  unfold peephole_optimize_asm.
  simpl.
  unfold peephole_optimize_bks.
  simpl.
  unfold AsmEval.
  apply eutt_interp_state; auto.
  apply eutt_interp_state; auto.
  unfold denote_asm.
  rewrite interp_loop.
  rewrite interp_loop.
  apply eutt_loop.
  simpl. red. intros. 
  unfold denote_b.
  apply peephole_block_correct.
  assumption.
Qed.


(* concrete optimizations --------------------------------------------------- *)

Definition simple (i:instr) : list instr :=
  match i with
  | Imov dest (Ovar src) =>
    if dest =? src then [] else [i]
  | _ => [i]
  end.


Lemma interp_h_ret_tt : forall (t : itree (Imp.Locals +' Memory +' Exit) unit),
    interp h t ≈ interp h (t ;; Ret tt).
Proof.
  intros t.
  rewrite interp_bind.
  rewrite <- bind_ret2 at 1.
  apply eutt_bind. red.  intros. destruct a. rewrite interp_ret. reflexivity.
  reflexivity.  
Qed.



Lemma simple_correct : ph_correct simple.
Proof.
  unfold ph_correct.
  intros i.
  destruct i; simpl.
  - destruct src.
    + simpl. rewrite bind_ret. apply interp_h_ret_tt. 
    + simpl.
      destruct (string_dec dest v).
      * subst.
        rewrite String.eqb_refl.
        simpl. 
        rewrite interp_ret.
        rewrite interp_bind.
        rewrite interp_trigger.
        rewrite bind_tau.
        rewrite tau_eutt.
        unfold h.
        (* SAZ: Not sure what the right way to progress here is. *)
        SearchAbout bimap.
        admit.
        
      * apply String.eqb_neq in n. rewrite n.
        simpl. apply interp_h_ret_tt.
  - apply interp_h_ret_tt.
  - apply interp_h_ret_tt.
  - apply interp_h_ret_tt.
  - apply interp_h_ret_tt.
  - apply interp_h_ret_tt.    
Admitted.    
