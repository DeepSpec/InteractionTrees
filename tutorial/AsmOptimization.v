(* begin hide *)
Require Import Label Asm AsmCombinators Imp2AsmCorrectness Utils_tutorial.

Require Import Psatz.

From Coq Require Import
     Lists.List
     Strings.String
     Morphisms
     ZArith
     Setoid
     RelationClasses.

From ITree Require Import
     Basics.Category
     Basics.MonadTheory
     ITree
     ITreeMonad
     ITreeFacts
     Events.StateFacts
     Events.Map
     Events.State
     SubKTree.

Import ITreeNotations.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Programming.Show
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.

Import CatNotations.
Open Scope cat_scope.

(* end hide *)




(* optimizations ------------------------------------------------------------ *)

(** A (simple) optimization is just a function from asm units to asm units. *)

Definition optimization {A B} := asm A B -> asm A B.

(** An optimization is correct if it yields an equivalent computation.

    - Note that eq_asm requires that resulting register environment and 
      the resulting heap must be equivalent, so this formulation of
      correctness does not permit the elimination of local variables or
      differences in the state.  Those optimizations would require
      more contextual information.
*)
Definition optimization_correct A B (opt:optimization) :=
  forall (p : asm A B),
    eq_asm p (opt p).


(* peephole optimizations --------------------------------------------------- *)

(** A (simple) peephole optmization transforms one instruction into a 
   (possibly empty) list of equivalent instructions. *)
Definition peephole_optimization := instr -> list instr.

(** We lift peephole optimizations to _asm_ pointwise through the structures. *) 
Fixpoint peephole_optimize_block {lbl} (ph : peephole_optimization) (b:block lbl) : block lbl :=
  match b with
  | bbi i k => blk_append (ph i) (peephole_optimize_block ph k)
  | bbb l => bbb l
  end.

Definition peephole_optimize_bks {A B} (ph : peephole_optimization) (bs : A -> block B) :=
  fun (a:A) => peephole_optimize_block ph (bs a).

Definition peephole_optimize_asm {A B} (ph : peephole_optimization) (p : asm A B) : asm A B :=
  Build_asm A B (p.(internal)) (peephole_optimize_bks ph (p.(code))).


(* peephole correctness ----------------------------------------------------- *)

Section Correctness.

  (** A peephole optimizer is correct if it replaces an instruction with 
    a semantically equivalent sequence of instructions. *)
  Definition ph_correct (ph : peephole_optimization) :=
  forall (i:instr),
    @eq_asm_denotations Exit unit _ (fun _ => denote_instr i) (fun _ => denote_list (ph i)).

  Lemma ph_blk_append_correct : forall (ph : peephole_optimization) (H : ph_correct ph)
    lbl1 lbl2 b1 b2 i,
    (@eq_asm_denotations Exit (F lbl1) (F lbl2) (fun _ => denote_block b1) (fun _ => denote_block b2)) ->
    (@eq_asm_denotations Exit (F lbl1) (F lbl2)
                         (fun _ => denote_instr i ;; denote_block b1)
                         (fun _ => denote_block (blk_append (ph i) b2))).
  Proof.
    intros ph H lbl1 lbl2 b1 b2 i HP.
    unfold eq_asm_denotations.
    intros a mem regs. 
    rewrite denote_blk_append.
    unfold ph_correct in H.
    unfold eq_asm_denotations in H.
    specialize H with (i:=i).
    pose proof (H tt) as H2.
    do 2 rewrite interp_asm_bind.
    eapply eutt_clo_bind.
    apply H2.
    intros. subst.
    destruct u2 as [g [l ?]].
    apply HP.
    exact a.
  Qed.  


Lemma peephole_block_correct : 
  forall (ph : peephole_optimization)
    (H : ph_correct ph)
    (lbl1 lbl2 : nat)
    (b : block (F lbl2)),
    @eq_asm_denotations Exit (F lbl1) (F lbl2)
                        (fun _ => denote_block b)
                        (fun _ => denote_block (peephole_optimize_block ph b)).
Proof.
  intros ph H lbl1 lbl2 b.
  induction b.
  - simpl.
    unfold eq_asm_denotations.
    intros.
    eapply ph_blk_append_correct. assumption. exact IHb. assumption.
  - unfold eq_asm_denotations.
    intros. reflexivity.
Qed.    

Lemma peephole_optimization_correct : forall A B (ph : peephole_optimization) (H : ph_correct ph),
    optimization_correct A B (peephole_optimize_asm ph).
Proof.
  intros A B ph H.
  unfold optimization_correct.
  intros p.
  unfold eq_asm, eq_asm_denotations, denote_asm.
  intros a mem regs.
  unfold interp_asm, run_map.
  repeat setoid_rewrite interp_bind.
  repeat rewrite interp_state_bind.
  eapply eutt_clo_bind.
  { reflexivity. }
  intros. simpl in *.
  rewrite H0.
  destruct u2 as [mem' [regs' z]].
  simpl.
  unfold denote_b.
  unfold iter, Iter_sktree.
  repeat rewrite interp_iter.
  unfold KTree.iter, Iter_ktree.
  cbn. 
  pose proof @interp_state_aloop'.
  red in H1.
  repeat rewrite H1.
  unfold aloop, ALoop_stateT0, aloop, ALoop_itree.
  repeat rewrite H1.
  unfold aloop, ALoop_stateT0, aloop, ALoop_itree.
  eapply (@eutt_aloop'  _ _ _ _ _ eq); auto.
  intros j1 j2 Heq.
  rewrite Heq.
  destruct j2 as [mem'' [regs'' [ll | rr]]]; cbn.
  - constructor.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    eapply eutt_clo_bind.
    + eapply eutt_clo_bind.
      * unfold peephole_optimize_bks.
        pose proof @peephole_block_correct.
        unfold eq_asm_denotations, interp_asm, run_map in H2.    
        eapply H2.
        apply H.
        apply ll.
      * intros.
        rewrite H2.
        reflexivity.
    + intros.
      rewrite H2.
      reflexivity.
  - constructor. reflexivity.
Qed.    


(* concrete optimizations --------------------------------------------------- *)

Definition simple (i:instr) : list instr :=
  match i with
  | Imov dest (Oreg src) =>
    if Nat.eqb dest src then [] else [i]
  | _ => [i]
  end.


Lemma interp_asm_ret_tt : forall (t : itree (Reg +' Memory +' Exit) unit) mem regs,
    interp_asm t mem regs ≈ interp_asm (t ;; Ret tt) mem regs.
Proof.
  intros t mem regs.
  rewrite interp_asm_bind.
  rewrite <- bind_ret2 at 1.
  eapply eutt_clo_bind. reflexivity.
  intros. subst. unfold interp_asm.
  destruct u2 as [g [l x]].
  unfold run_map.
  rewrite interp_ret.
  do 2 rewrite interp_state_ret.
  destruct x.
  reflexivity.
Qed.


Lemma simple_correct : ph_correct simple.
Proof.
  unfold ph_correct.
  intros i.
  unfold eq_asm_denotations. intros. 
  destruct i; simpl; try apply interp_asm_ret_tt.
  - destruct src.
    + simpl. rewrite bind_ret.
      apply interp_asm_ret_tt. 
    + simpl.
      destruct (Nat.eq_dec dest r).
      * subst. 
        rewrite Nat.eqb_refl.
        simpl.
        unfold interp_asm, run_map.
        rewrite interp_ret.
        do 2 rewrite interp_state_ret.
        rewrite interp_bind.
        rewrite interp_trigger.
        rewrite bind_tau.
        rewrite tau_eutt.
        do 2 rewrite interp_state_bind.
        cbn.
        unfold CategoryOps.cat, Cat_Handler, Handler.cat. simpl.
        unfold lookup_def.
        repeat rewrite interp_bind.
        setoid_rewrite interp_ret.
        repeat rewrite interp_state_bind.
        repeat rewrite bind_bind.        
        repeat setoid_rewrite interp_state_ret.

        unfold Map.lookup.
        unfold embed, Embeddable_itree, Embeddable_forall, inl_, embed.
        rewrite interp_trigger. rewrite tau_eutt.
        unfold Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
        rewrite interp_state_trigger. rewrite tau_eutt.
        cbn.
        rewrite interp_state_ret.
        repeat rewrite bind_ret.
        simpl.
        rewrite interp_trigger.
        rewrite tau_eutt.
        cbn. 
        unfold CategoryOps.cat, resum, ReSum_id, id_, eval_reg, inl_. cbn.
        setoid_rewrite interp_trigger. rewrite tau_eutt.
        rewrite interp_state_trigger.
        rewrite tau_eutt.
        cbn.
        rewrite interp_state_ret.

        (* SAZ: need to propagate an equivalence relation on the register state. *)

        
Admitted.    


End Correctness.