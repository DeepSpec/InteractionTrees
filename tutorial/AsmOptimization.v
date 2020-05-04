(* begin hide *)
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
     Basics.Monad
     ITree
     ITreeMonad
     ITreeFacts
     Events.StateFacts
     Events.MapDefault
     Events.MapDefaultFacts
     Events.State.

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

Require Import Fin Asm AsmCombinators Utils_tutorial.
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

(** We define an appropriate notion of equivalence on these state components.
    This will be useful for defining optimizations at the [Asm] level. *)

Definition EQ_registers (d:value) (regs1 regs2 : registers) : Prop :=
  @eq_map _ _ _ _ d regs1 regs2.

Global Instance EQ_registers_refl {d} : Reflexive (EQ_registers d).
unfold EQ_registers. typeclasses eauto.
Qed.

Global Instance EQ_registers_sym {d} : Symmetric (EQ_registers d).
unfold EQ_registers. typeclasses eauto.
Qed.

Global Instance EQ_registers_trans {d} : Transitive (EQ_registers d).
unfold EQ_registers. typeclasses eauto.
Qed.

Global Instance EQ_registers_eqv {d} : Equivalence (EQ_registers d).
constructor; typeclasses eauto.
Qed.



Definition EQ_memory (mem1 mem2 : memory) : Prop :=
  @eq_map _ _ _ _ 0 mem1 mem2.

Global Instance EQ_memory_refl : Reflexive (EQ_memory).
unfold EQ_memory. typeclasses eauto.
Qed.

Global Instance EQ_memory_sym : Symmetric (EQ_memory).
unfold EQ_memory. typeclasses eauto.
Qed.

Global Instance EQ_memory_trans : Transitive (EQ_memory).
unfold EQ_memory. typeclasses eauto.
Qed.

Global Instance EQ_memory_eqv : Equivalence (EQ_memory).
constructor; typeclasses eauto.
Qed.

Definition rel_asm {B} : memory * (registers * B) -> memory * (registers * B) -> Prop :=
  prod_rel EQ_memory (prod_rel (EQ_registers 0) eq).

Hint Unfold rel_asm: core.

(** The definition [interp_asm] also induces a notion of equivalence (open)
    _asm_ programs, which is just the equivalence of the ktree category *)
Definition eq_asm_denotations_EQ {E A B} (t1 t2 : Kleisli (itree (Reg +' Memory +' E)) A B) : Prop :=
  forall a mem1 mem2 regs1 regs2,
    EQ_memory mem1 mem2 ->
    EQ_registers 0 regs1 regs2 ->
    (eutt rel_asm)
      (interp_asm (t1 a) mem1 regs1)
      (interp_asm (t2 a) mem2 regs2).

Definition eq_asm_EQ {A B} (p1 p2 : asm A B) : Prop :=
  eq_asm_denotations_EQ (denote_asm p1) (denote_asm p2).

Definition optimization_correct A B (opt:optimization) :=
  forall (p : asm A B),
    eq_asm_EQ p (opt p).

Definition EQ_asm {E A} (f g : memory -> registers -> itree E (memory * (registers * A))) : Prop :=
  forall mem1 mem2 regs1 regs2,
    EQ_memory mem1 mem2 ->
    EQ_registers 0 regs1 regs2 ->
    eutt (@rel_asm A) (f mem1 regs1) (g mem2 regs2).

Infix "≡" := EQ_asm (at level 70).

Lemma interp_asm_ret_tt : forall (t : itree (Reg +' Memory +' Exit) unit),
    (interp_asm t) ≡ (interp_asm (t ;; Ret tt)).
Proof.
  intros t mem1 mem2 regs1 regs2 H1 H2.
  rewrite interp_asm_bind.
  rewrite <- bind_ret_r at 1.
  apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).
  { unfold interp_asm.
    unfold rel_asm.
    eapply interp_map_proper; try typeclasses eauto; auto.
    eapply interp_map_proper; try typeclasses eauto; auto.
    reflexivity.
  }
  intros.
  inversion H; subst.
  inversion H3. subst.
  unfold interp_asm.
  unfold interp_map.
  rewrite interp_ret.
  do 2 rewrite interp_state_ret.
  apply eqit_Ret. constructor. auto. destruct b3.
  assumption.
Qed.

Lemma interp_asm_ret {E A} (x:A) mem reg :
  interp_asm (Ret x) mem reg ≈ (Ret (mem, (reg, x)) : itree E _).
Proof.
  unfold interp_asm, interp_map.
  rewrite interp_ret.
  repeat rewrite interp_state_ret.
  reflexivity.
Qed.

Lemma interp_asm_GetReg {E A} f r mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (val <- trigger (GetReg r) ;; f val) mem reg)
       ((interp_asm (f (lookup_default r 0 reg))) mem reg).
Proof.
  unfold interp_asm, interp_map.
  rewrite interp_bind.
  setoid_rewrite interp_trigger.
  repeat rewrite interp_state_bind. cbn.
  unfold subevent, resum, ReSum_inl, resum, ReSum_id, id_.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold lookup_def.
  unfold embed, Embeddable_forall, embed, Embeddable_itree.
  unfold trigger. rewrite interp_vis. setoid_rewrite interp_ret.
  unfold subevent, resum.
  repeat rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_ret.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  rewrite interp_state_trigger_eqit. cbn.
  rewrite !bind_ret_l, !tau_eutt.
  rewrite interp_state_ret.
  rewrite !bind_ret_l, !tau_eutt.
  rewrite !interp_state_ret; cbn.
  rewrite bind_ret_l; cbn.
  reflexivity.
Qed.

Lemma interp_asm_SetReg {E A} f r v mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (trigger (SetReg r v) ;; f) mem reg)
       ((interp_asm f) mem (Maps.add r v reg)).
Proof.
  unfold interp_asm, interp_map.
  rewrite interp_bind.
  unfold trigger.
  rewrite interp_vis.
  unfold subevent, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  setoid_rewrite interp_ret.
  rewrite bind_bind.
  setoid_rewrite tau_eutt.
  setoid_rewrite bind_ret_l.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold insert.
  setoid_rewrite interp_trigger.
  repeat rewrite interp_state_trigger_eqit.  cbn.
  rewrite bind_ret_l, tau_eutt.
  setoid_rewrite interp_state_ret.
  rewrite bind_ret_l. cbn.
  reflexivity.
Qed.

Lemma interp_asm_Load {E A} f a mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (val <- trigger (Load a) ;; f val) mem reg)
       ((interp_asm (f (lookup_default a 0 mem))) mem reg).
Proof.
  unfold interp_asm, interp_map.
  rewrite interp_bind.
  rewrite interp_trigger.
  unfold subevent, resum, ReSum_inr, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
  unfold lookup_def.
  repeat (setoid_rewrite interp_trigger; rewrite tau_eutt).
  repeat rewrite interp_state_trigger_eqit.
  cbn. unfold pure_state, embed, Embeddable_forall, embed, Embeddable_itree, trigger.
  do 2 rewrite interp_vis, bind_vis.
  rewrite interp_state_vis. cbn. rewrite bind_vis, interp_state_vis. cbn.
  rewrite !bind_ret_l, !tau_eutt. rewrite !interp_ret, !interp_state_ret.
  rewrite bind_ret_l; cbn.
  reflexivity.
Qed.

Lemma interp_asm_Store {E A} f a v mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (trigger (Store a v) ;; f) mem reg)
       ((interp_asm f) (Maps.add a v mem) reg).
Proof.
  unfold interp_asm, interp_map.
  rewrite interp_bind.
  rewrite interp_trigger.
  unfold subevent, resum, ReSum_inr, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
  unfold insert, embed, Embeddable_forall, embed, Embeddable_itree.
  rewrite interp_trigger.
  setoid_rewrite interp_trigger.
  rewrite interp_state_trigger_eqit. cbn.
  cbn. unfold pure_state, embed, Embeddable_forall, embed, Embeddable_itree, trigger.
  rewrite bind_vis, interp_state_vis. cbn. rewrite !bind_ret_l, !tau_eutt.
  rewrite interp_state_ret, bind_ret_l; cbn.
  reflexivity.
Qed.

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
    @eq_asm_denotations_EQ Exit unit _ (fun _ => denote_instr i) (fun _ => denote_list (ph i)).

  Lemma ph_blk_append_correct : forall (ph : peephole_optimization) (H : ph_correct ph)
    lbl1 lbl2 b1 b2 i,
    (@eq_asm_denotations_EQ Exit (fin lbl1) (fin lbl2) (fun _ => denote_bk b1) (fun _ => denote_bk b2)) ->
    (@eq_asm_denotations_EQ Exit (fin lbl1) (fin lbl2)
                         (fun _ => denote_instr i ;; denote_bk b1)
                         (fun _ => denote_bk (blk_append (ph i) b2))).
  Proof.
    intros ph H lbl1 lbl2 b1 b2 i HP.
    unfold eq_asm_denotations_EQ.
    intros a mem1 mem2 regs1 regs2 EQ_mem EQ_reg.
    rewrite denote_blk_append.
    unfold ph_correct in H.
    unfold eq_asm_denotations_EQ in H.
    specialize H with (i:=i).
    pose proof (H tt) as H2.
    do 2 rewrite interp_asm_bind.
    eapply eutt_clo_bind.
    apply H2; auto.
    intros.
    inversion H0; subst. inversion H3; subst.
    apply HP; auto.
  Qed.


Lemma peephole_block_correct :
  forall (ph : peephole_optimization)
    (H : ph_correct ph)
    (lbl1 lbl2 : nat)
    (b : block (fin lbl2)),
    @eq_asm_denotations_EQ Exit (fin lbl1) (fin lbl2)
                        (fun _ => denote_bk b)
                        (fun _ => denote_bk (peephole_optimize_block ph b)).
Proof.
  intros ph H lbl1 lbl2 b.
  induction b.
  - simpl.
    unfold eq_asm_denotations_EQ.
    intros.
    eapply ph_blk_append_correct; try assumption. exact IHb. assumption.
  - unfold eq_asm_denotations_EQ.
    intros.
    destruct b; simpl.
    + unfold interp_asm.
      rewrite interp_ret.
      unfold interp_map.
      repeat rewrite interp_state_ret.
      apply eqit_Ret. constructor; auto.
    + setoid_rewrite interp_asm_GetReg.
      rewrite H1.
      unfold value in *.
      remember (lookup_default r 0 regs2) as x.
      destruct x.
      repeat rewrite interp_asm_ret.
      apply eqit_Ret. constructor; auto.
      repeat rewrite interp_asm_ret.
      apply eqit_Ret. constructor; auto.
    + unfold interp_asm, interp_map.
      unfold id_, Id_Handler, Handler.id_.
      unfold exit.
      rewrite interp_vis.
      cbn. rewrite interp_state_bind.
      unfold CategoryOps.cat, Cat_Handler, Handler.cat, inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
      setoid_rewrite interp_trigger.
      unfold inr_.
      rewrite interp_trigger.
      rewrite interp_state_trigger_eqit.
      rewrite interp_state_bind.
      cbn. unfold pure_state.
      rewrite bind_vis, interp_state_vis. cbn.
      repeat rewrite bind_vis.
      rewrite interp_state_bind.
      rewrite interp_state_trigger_eqit. cbn.
      rewrite !bind_vis, interp_state_vis. cbn.
      rewrite bind_vis.
      apply eqit_Vis; intros [].
Qed.


Lemma peephole_optimization_correct : forall A B (ph : peephole_optimization) (H : ph_correct ph),
    optimization_correct A B (peephole_optimize_asm ph).
Proof.
  intros A B ph H.
  unfold optimization_correct.
  intros p.
  unfold eq_asm, eq_asm_denotations, denote_asm.
  intros a mem1 mem2 regs1 regs2 H1 H2.
  unfold interp_asm, interp_map.
  repeat setoid_rewrite interp_bind.
  repeat rewrite interp_state_bind.
  apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).

  { apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).
    -  unfold inr_, Inr_Kleisli, lift_ktree_.
       unfold ret, Monad_itree.
       repeat rewrite interp_ret.
       repeat rewrite interp_state_ret.
       apply eqit_Ret. constructor; auto.
    -  intros. inversion H0.
       subst. cbn.
       unfold CategorySub.from_bif, FromBifunctor_ktree_fin.
       repeat rewrite interp_ret.
       repeat rewrite interp_state_ret.
       apply eqit_Ret.
       inversion H4; subst.
       constructor; auto. }

  intros.
  inversion H0; subst.
  simpl in *.
  unfold denote_bks.
  unfold iter, CategorySub.Iter_sub.
  repeat rewrite interp_iter.
  unfold iter, Iter_Kleisli.
  cbn.
  pose proof @interp_state_iter'.
  red in H5.
  unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *.
  cbn in *.
  repeat rewrite H5.

  eapply eutt_iter' with (RI := rel_asm); cbn.
  2: destruct H4; auto.
  intros j1 j2 [ ? ? ? ? ? [? ? ? ? ? []]]; cbn.
  rewrite !interp_bind, !interp_state_bind, !bind_bind. (* Slow! *)

  apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm);
    [|intros ? ? [? ? ? ? ? [? ? ? ? ? []]]]; cbn.
  { eapply @peephole_block_correct; eauto. }

  unfold CategorySub.to_bif, ToBifunctor_ktree_fin.
  apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm);
    [|intros ? ? [? ? ? ? ? [? ? ? ? ? []]]]; cbn.
  {
    rewrite bind_ret_l.
    unfold case_, Case_sum1, Case_Kleisli, case_sum.
    unfold CategoryOps.cat, CategorySub.Cat_sub, CategoryOps.cat, Cat_Kleisli.
    unfold inl_, CategorySub.Inl_sub, inl_, Inl_Kleisli, lift_ktree_.
    unfold inr_, CategorySub.Inr_sub, inr_, Inr_Kleisli, lift_ktree_.
    unfold id_, CategorySub.Id_sub, id_, Id_Kleisli, lift_ktree_.
    cbn.
    unfold CategorySub.from_bif, FromBifunctor_ktree_fin.
    destruct split_fin_sum.
    all: rewrite !bind_ret_l, interp_ret, !interp_state_ret.
    all: apply eqit_Ret; auto.
  }

  rewrite interp_ret, !interp_state_ret, !bind_ret_l.
  rewrite !interp_state_ret, !bind_ret_l; cbn.
  apply eqit_Ret.
  destruct split_fin_sum; auto.
Qed.


(* concrete optimizations --------------------------------------------------- *)

Definition simple (i:instr) : list instr :=
  match i with
  | Imov dest (Oreg src) =>
    if Nat.eqb dest src then [] else [i]
  | _ => [i]
  end.

(* SAZ: Belongs in the utilities? (but depends on EQ_registers)
   EQ_Registers is now just an alias for eq_map, so this can be moved to MapDefaultFacts.
*)
Lemma EQ_registers_add:
  forall (r : reg) (d:value) (regs1 regs2 : registers),
    EQ_registers d regs1 regs2 ->
    EQ_registers d (alist_add r (lookup_default r d regs1) regs1) regs2.
Proof.
  intros r d regs1 regs2 H.
  unfold EQ_registers.
  unfold eq_map.
  intros.
  unfold lookup_default at 1, lookup, Map_alist.
  destruct (Nat.eq_dec k r).
  - subst. rewrite In_add_eq.
    apply H.
  - unfold lookup_default, lookup, Map_alist.
    rewrite alist_find_neq; auto.
    apply H.
Qed.

Lemma simple_correct : ph_correct simple.
Proof.
  unfold ph_correct.
  intros i.
  unfold eq_asm_denotations_EQ.
  intros.
  destruct i; simpl; try apply interp_asm_ret_tt; auto; try reflexivity.

  destruct src.
  + simpl. rewrite !bind_ret_l.
    apply interp_asm_ret_tt; auto; try reflexivity.

  + simpl.
    destruct (Nat.eq_dec dest r).
    * subst.
      rewrite Nat.eqb_refl.
      simpl.
      rewrite interp_asm_ret.
      rewrite interp_asm_GetReg.

      unfold trigger.
      unfold interp_asm, interp_map.
      rewrite interp_vis.
      cbn.
      repeat rewrite interp_state_bind.
      unfold CategoryOps.cat, Cat_Handler, Handler.cat. simpl.
      unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
      unfold insert.
      unfold embed, Embeddable_itree, Embeddable_forall, inl_, embed.
      rewrite interp_trigger.
      rewrite interp_state_trigger_eqit.
      cbn.
      rewrite bind_ret_l, tau_eutt.
      rewrite interp_state_ret, bind_ret_l, interp_ret. cbn.
      rewrite tau_eutt, 2 interp_state_ret.
      apply eqit_Ret. auto using EQ_registers_add.
    * apply Nat.eqb_neq in n.
      rewrite n.
      apply interp_asm_ret_tt; auto.
Qed.

End Correctness.
