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

(** We define an appropriate notion of equivalence on these state components.
    This will be useful for defining optimizations at the [Asm] level. *)
Definition EQ_registers (regs1 regs2 : registers) : Prop :=
  forall k v, alist_In k regs1 v <-> alist_In k regs2 v.

Definition EQ_memory (mem1 mem2 : memory) : Prop :=
  forall k v, alist_In k mem1 v <-> alist_In k mem2 v.

Global Instance EQ_registers_refl : Reflexive EQ_registers.
  Proof.
    red. intros. unfold EQ_registers. tauto.
  Qed.    

Global Instance EQ_registers_sym : Symmetric EQ_registers.
  Proof.
    repeat intro. 
    split; intros; apply H; assumption.
  Qed.

Global Instance EQ_registers_trans : Transitive EQ_registers.
  Proof.
    repeat intro. 
    unfold EQ_registers in *.
    split; intros.
    - apply H0. apply H. assumption.
    - apply H. apply H0. assumption.
  Qed.
  
Global Instance EQ_registers_eqv : Equivalence EQ_registers.
constructor; typeclasses eauto. 
  
  
Global Instance EQ_memory_refl : Reflexive EQ_memory.
Proof.
  red. intros. unfold EQ_memory. tauto.
Qed.    

Global Instance EQ_memory_sym : Symmetric EQ_memory.
  Proof.
    repeat intro. 
    split; intros; apply H; assumption.
  Qed.

Global Instance EQ_memory_trans : Transitive EQ_memory.
  Proof.
    repeat intro. 
    unfold EQ_registers in *.
    split; intros.
    - apply H0. apply H. assumption.
    - apply H. apply H0. assumption.
  Qed.

Global Instance EQ_memory_eqv : Equivalence EQ_memory.
Proof.
constructor; typeclasses eauto. 
Qed.

Inductive rel_asm {B} : memory * (registers * B) -> memory * (registers * B) -> Prop :=
|rel_asm_ctr : forall b mem1 mem2 regs1 regs2
                 (HMem : EQ_memory mem1 mem2)
                 (HReg : EQ_registers regs1 regs2),
    rel_asm (mem1, (regs1, b)) (mem2, (regs2, b)).

Global Instance rel_asm_refl {B} : Reflexive (@rel_asm B).
Proof.
  repeat intro.
  destruct x as [m [r b]].
  constructor; reflexivity.
Qed.  

Global Instance rel_asm_sym {B} : Symmetric (@rel_asm B).
Proof.
  repeat intro.
  inversion H.
  subst.
  constructor; symmetry; assumption.
Qed.  

Global Instance rel_asm_trans {B} : Transitive (@rel_asm B).
Proof.
  repeat intro.
  inversion H.
  inversion H0.
  subst. inversion H3. subst.
  constructor; eapply transitivity; eassumption.
Qed.

Global Instance rel_asm_eqv {B} : Equivalence (@rel_asm B).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance eutt_rel_asm_refl {E R} {r : R -> R -> Prop} `{Reflexive _ r} : Reflexive (@eutt E R R r).
Proof.
  (* SAZ: Should this be in the library? *)
Admitted.

Global Instance eutt_rel_asm_sym {E R} {r : R -> R -> Prop} `{Symmetric _ r} : Symmetric (@eutt E R R r).
Proof.
  (* SAZ: Should this be in the library? *)
Admitted.

Global Instance eutt_rel_asm_trans {E R} {r : R -> R -> Prop} `{Transitive _ r} : Transitive (@eutt E R R r).
Proof.
  (* SAZ: Should this be in the library? *)
Admitted.

Global Instance eutt_rel_asm_equiv {E R} {r : R -> R -> Prop} `{Equivalence _ r} : Equivalence (@eutt E R R r).
Proof.
  constructor; typeclasses eauto.
Qed.


(** The definition [interp_asm] also induces a notion of equivalence (open)
    _asm_ programs, which is just the equivalence of the ktree category *)
Definition eq_asm_denotations_EQ {E A B} (t1 t2 : Kleisli (itree (Reg +' Memory +' E)) A B) : Prop :=
  forall a mem1 mem2 regs1 regs2,
    EQ_memory mem1 mem2 ->
    EQ_registers regs1 regs2 ->
    (eutt rel_asm)
      (interp_asm (t1 a) mem1 regs1)
      (interp_asm (t2 a) mem2 regs2).

Definition eq_asm_EQ {A B} (p1 p2 : asm A B) : Prop :=
  eq_asm_denotations_EQ (denote_asm p1) (denote_asm p2).

Definition optimization_correct A B (opt:optimization) :=
  forall (p : asm A B),
    eq_asm_EQ p (opt p).

Definition EQ_asm {E A} (f g : memory -> registers -> itree E _) : Prop :=
  forall mem1 mem2 regs1 regs2,
    EQ_memory mem1 mem2 ->
    EQ_registers regs2 regs2 ->
    eutt (@rel_asm A) (f mem1 regs1) (g mem2 regs2).

Infix "≡" := EQ_asm (at level 70).


(* SAZ: I'm not sure that this can be proved without coinduction on t.
   It probably belongs in the state part of the library, along with the
   appropriate definition of eutt, etc.

   It also depends crucially on the fact that the handlers respect
   the equivalence on the state maps.     
*)
Lemma interp_asm_id:
  forall (t : itree (Reg +' Memory +' Exit) unit),
    (interp_asm t) ≡ (interp_asm t).
Proof.
  intros t mem1 mem2 regs1 regs2 H1 H2.
  unfold interp_asm.
  unfold run_map.
  unfold interp_state.
  pose proof @eutt_interp.
Admitted.    


Lemma interp_asm_ret_tt : forall (t : itree (Reg +' Memory +' Exit) unit),
    (interp_asm t) ≡ (interp_asm (t ;; Ret tt)).
Proof.
  intros t mem1 mem2 regs1 regs2 H1 H2.
  rewrite interp_asm_bind.
  rewrite <- bind_ret2 at 1.
  eapply eutt_clo_bind.
  { apply interp_asm_id; auto. }
  intros.
  inversion H; subst.

  unfold interp_asm.
  unfold run_map.
  rewrite interp_ret.
  do 2 rewrite interp_state_ret.
  apply eqit_Ret. destruct b. assumption.
Qed.

Definition lookup_default {K V} `{Map K V} k v m :=
  match Maps.lookup k m with
  | Some v' => v'
  | None => v
  end.

Lemma interp_asm_ret {E A} (x:A) mem reg :
  interp_asm (Ret x) mem reg ≈ (Ret (mem, (reg, x)) : itree E _).
Proof.
  unfold interp_asm, run_map.
  rewrite interp_ret.
  repeat rewrite interp_state_ret.
  reflexivity.
Qed.

Lemma interp_asm_GetReg {E A} f r mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (val <- trigger (GetReg r) ;; f val) mem reg)
       ((interp_asm (f (lookup_default r 0 reg))) mem reg).
Proof.
  unfold interp_asm, run_map.
  rewrite interp_bind.
  unfold trigger.
  rewrite interp_vis. rewrite tau_eutt.
  unfold subevent, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  setoid_rewrite interp_ret.
  rewrite bind_bind.
  setoid_rewrite bind_ret.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold lookup_def.
  rewrite interp_bind.
  setoid_rewrite interp_trigger. rewrite tau_eutt.
  setoid_rewrite interp_ret.
  repeat rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_ret.
  rewrite interp_state_trigger. rewrite tau_eutt.
  cbn .
  rewrite interp_state_ret.
  repeat rewrite bind_ret.
  cbn.
  unfold lookup_default.
  unfold lookup, Map_alist. reflexivity.
Qed.  

Lemma interp_asm_SetReg {E A} f r v mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (trigger (SetReg r v) ;; f) mem reg)
       ((interp_asm f) mem (Maps.add r v reg)).
Proof.
  unfold interp_asm, run_map.
  rewrite interp_bind.
  unfold trigger.
  rewrite interp_vis. rewrite tau_eutt.
  unfold subevent, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  setoid_rewrite interp_ret.
  rewrite bind_bind.
  setoid_rewrite bind_ret.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold insert.
  setoid_rewrite interp_trigger. rewrite tau_eutt.
  repeat rewrite interp_state_trigger.  cbn.
  rewrite tau_eutt.
  setoid_rewrite interp_state_ret.
  rewrite bind_ret. cbn.
  reflexivity.
Qed.  

Lemma interp_asm_Load {E A} f a mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (val <- trigger (Load a) ;; f val) mem reg)
       ((interp_asm (f (lookup_default a 0 mem))) mem reg).
Proof.
  unfold interp_asm, run_map.
  rewrite interp_bind.
  rewrite interp_trigger. rewrite tau_eutt.
  unfold subevent, resum, ReSum_inr, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
  unfold lookup_def.
  rewrite interp_bind.
  setoid_rewrite interp_trigger. rewrite tau_eutt.
  setoid_rewrite interp_ret.
  rewrite interp_bind. repeat rewrite interp_trigger. rewrite tau_eutt.
  setoid_rewrite interp_ret.
  repeat rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_ret.
  repeat rewrite interp_state_trigger. rewrite tau_eutt.
  cbn. unfold pure_state. rewrite interp_state_vis. cbn.  rewrite tau_eutt.
  rewrite bind_ret. rewrite interp_state_ret.
  repeat rewrite bind_ret. cbn. 
  unfold lookup_default.
  unfold lookup, Map_alist. reflexivity.
Qed.  

Lemma interp_asm_Store {E A} f a v mem reg :
  @eutt E _ _ (@rel_asm A)
       (interp_asm (trigger (Store a v) ;; f) mem reg)
       ((interp_asm f) (Maps.add a v mem) reg).
Proof.
  unfold interp_asm, run_map.
  rewrite interp_bind.
  rewrite interp_trigger. rewrite tau_eutt.
  unfold subevent, resum, ReSum_inr, resum, ReSum_inl, resum, ReSum_id, id_. cbn.
  repeat rewrite interp_state_bind.
  unfold Id_IFun.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold CategoryOps.cat, Cat_Handler, Handler.cat. cbn.
  unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
  unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
  unfold insert, embed, Embeddable_forall, embed, Embeddable_itree. 
  rewrite interp_trigger. rewrite tau_eutt.
  setoid_rewrite interp_trigger. rewrite tau_eutt.
  rewrite interp_state_trigger. rewrite tau_eutt. cbn.
  unfold pure_state. rewrite interp_state_vis. cbn.  rewrite tau_eutt.
  rewrite bind_ret. rewrite interp_state_ret.
  repeat rewrite bind_ret. cbn. 
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
    (@eq_asm_denotations_EQ Exit (F lbl1) (F lbl2) (fun _ => denote_block b1) (fun _ => denote_block b2)) ->
    (@eq_asm_denotations_EQ Exit (F lbl1) (F lbl2)
                         (fun _ => denote_instr i ;; denote_block b1)
                         (fun _ => denote_block (blk_append (ph i) b2))).
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
    inversion H0.
    apply HP; auto.
  Qed.  

  Lemma EQ_registers_lookup : forall regs1 regs2 r ,
      EQ_registers regs1 regs2 ->
      lookup r regs1 = lookup r regs2.
  Proof.
    intros. unfold EQ_registers, alist_In in H.
    unfold lookup, Map_alist.
    remember (alist_find r regs1) as x.
    destruct x.
    - symmetry in Heqx. rewrite H in Heqx. rewrite Heqx. reflexivity.
    - remember (alist_find r regs2) as x.
      destruct x.
      symmetry in Heqx0. rewrite <- H in Heqx0. rewrite Heqx0 in Heqx. inversion Heqx.
      reflexivity.
 Qed.
    
Lemma EQ_registers_lookup_default : forall regs1 regs2 r v,
      EQ_registers regs1 regs2 ->
      lookup_default r v regs1 = lookup_default r v regs2.
Proof.
  intros regs1 regs2 r v H.
  unfold lookup_default.
  erewrite EQ_registers_lookup. reflexivity. assumption.
Qed.
  

Lemma peephole_block_correct : 
  forall (ph : peephole_optimization)
    (H : ph_correct ph)
    (lbl1 lbl2 : nat)
    (b : block (F lbl2)),
    @eq_asm_denotations_EQ Exit (F lbl1) (F lbl2)
                        (fun _ => denote_block b)
                        (fun _ => denote_block (peephole_optimize_block ph b)).
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
      unfold run_map.
      repeat rewrite interp_state_ret.
      apply eqit_Ret. constructor; auto.
    + setoid_rewrite interp_asm_GetReg.
      rewrite (EQ_registers_lookup_default _ regs2); auto.
      unfold value in *.
      remember (lookup_default r 0 regs2) as x.
      destruct x.
      repeat rewrite interp_asm_ret.
      apply eqit_Ret. constructor; auto.
      repeat rewrite interp_asm_ret.
      apply eqit_Ret. constructor; auto.
    + unfold interp_asm, run_map.
      unfold id_, Id_Handler, Handler.id_.
      unfold exit.
      rewrite interp_vis. rewrite tau_eutt.
      cbn. rewrite interp_state_bind.
      unfold CategoryOps.cat, Cat_Handler, Handler.cat, inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
      setoid_rewrite interp_trigger. rewrite tau_eutt.
      unfold inr_.
      rewrite interp_trigger. rewrite tau_eutt.
      rewrite interp_state_trigger. rewrite tau_eutt.
      rewrite interp_state_bind.
      cbn. unfold pure_state. rewrite interp_state_vis. cbn.  rewrite tau_eutt.
      repeat rewrite bind_vis.
      rewrite interp_state_bind.
      rewrite interp_state_trigger. cbn.  rewrite tau_eutt.
      rewrite bind_vis.
      rewrite interp_state_vis. rewrite tau_eutt. cbn.
      rewrite bind_vis.
      unfold resum, ReSum_id, id_, Id_IFun.
      apply eqit_Vis.
      intros. inversion u.
Qed.


Lemma peephole_optimization_correct : forall A B (ph : peephole_optimization) (H : ph_correct ph),
    optimization_correct A B (peephole_optimize_asm ph).
Proof.
  intros A B ph H.
  unfold optimization_correct.
  intros p.
  unfold eq_asm, eq_asm_denotations, denote_asm.
  intros a mem1 mem2 regs1 regs2 H1 H2.
  unfold interp_asm, run_map.
  repeat setoid_rewrite interp_bind.
  repeat rewrite interp_state_bind.
  apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).

  
  { apply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).
    -  unfold inr_, CoprodInr_Kleisli, lift_ktree_.
       unfold ret, Monad_itree.
       repeat rewrite interp_ret.
       repeat rewrite interp_state_ret.
       apply eqit_Ret. constructor; auto.
    -  intros. inversion H0.
       subst. cbn.
       repeat rewrite interp_ret.
       repeat rewrite interp_state_ret.
       apply eqit_Ret. constructor; auto. }
    
  intros. 
  inversion H0.
  subst. simpl in *.
  unfold denote_b.
  unfold iter, Iter_sktree.
  repeat rewrite interp_iter.
  unfold KTree.iter, Iter_ktree.
  cbn. 
  pose proof @interp_state_aloop'.
  red in H3.
  repeat rewrite H3.
  unfold aloop, ALoop_stateT0, aloop, ALoop_itree.
  repeat rewrite H3.
  unfold aloop, ALoop_stateT0, aloop, ALoop_itree.
  eapply (@eutt_aloop'  _ _ _ _ _ rel_asm); auto.
  intros j1 j2 Hrel.
  inversion Hrel.
  subst; cbn.
  destruct b0.
  - constructor.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    eapply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).
    + eapply (@eutt_clo_bind _ _ _ _ _ _ rel_asm).
      * unfold peephole_optimize_bks.
        pose proof @peephole_block_correct.
        unfold eq_asm_denotations_EQ, interp_asm, run_map in H4.    
        eapply H4; auto.
        apply f.
      * intros.
        inversion H4.
        subst. cbn.
        repeat rewrite bind_ret.
        unfold CategoryOps.cat, Cat_sktree, CategoryOps.cat, Cat_Kleisli. cbn.
        unfold case_, Case_sum1, CoprodCase_Kleisli, case_sum.
        destruct (split_fin_sum b0).
        -- repeat rewrite bind_ret.
           rewrite interp_ret.
           repeat rewrite interp_state_ret.
           apply eqit_Ret. constructor; auto.
        -- repeat rewrite bind_ret.
           rewrite interp_ret.
           repeat rewrite interp_state_ret.
           apply eqit_Ret. constructor; auto.
    + intros.
      inversion H4.
      subst; cbn.
      rewrite interp_ret.
      repeat rewrite interp_state_ret.
      apply eqit_Ret. constructor; auto.
  - constructor. constructor; auto.
  - constructor; auto.
Qed.    


(* concrete optimizations --------------------------------------------------- *)

Definition simple (i:instr) : list instr :=
  match i with
  | Imov dest (Oreg src) =>
    if Nat.eqb dest src then [] else [i]
  | _ => [i]
  end.


(* TODO: Move to utilities *)
Section alist_facts.

  Context {K V: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.

  Lemma alist_In_add_eq : forall m (k:K) (v n:V), alist_In k (alist_add k n m) v -> n = v.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - unfold alist_add in H.
      unfold alist_In in H. simpl in H.
      destruct (k ?[ eq ] k); inversion H; auto.
    - unfold alist_add in H.
      unfold alist_In in H.
      simpl in H.
      destruct (k ?[ eq ] k). inversion H; auto.
      pose proof (@not_In_remove K V _ _ ((k1,v1)::m)).
      unfold alist_In in H0. simpl in H0.
      apply H0 in H.
      contradiction.
  Qed.
End alist_facts.

  
(* SAZ: Belongs in the utilities? (but depends on EQ_registers) *)
Lemma EQ_registers_add:
  forall (r : reg) (regs1 regs2 : registers),
    EQ_registers regs1 regs2 ->
    EQ_registers (alist_add r (lookup_default r 0 regs1) regs1) regs2.
Proof.
  intros r regs1 regs2 H.
  unfold EQ_registers in *.
  intros.
  unfold lookup_default, lookup, Map_alist.
  remember (@alist_find reg _ RelDec_reg nat r regs1) as x.
  unfold alist_In.
  unfold alist_add.
  destruct x; simpl in *.
  unfold rel_dec, RelDec_reg; simpl.
  - destruct (Nat.eq_dec k r).
    + subst.
      split; intros.
      inversion H0. subst.
      unfold alist_In in H.
      apply H. symmetry. assumption.
      unfold alist_In in H.
      unfold value in *.
      apply H in H0.
      rewrite H0 in Heqx.
      assumption.

    + split; intros.
      unfold alist_In in H0.
Admitted.

Lemma simple_correct : ph_correct simple.
Proof.
  unfold ph_correct.
  intros i.
  unfold eq_asm_denotations_EQ.
  intros. 
  destruct i; simpl; try apply interp_asm_ret_tt; auto; try reflexivity.

  destruct src.
  + simpl. rewrite bind_ret.
    apply interp_asm_ret_tt; auto; try reflexivity.

  + simpl.
    destruct (Nat.eq_dec dest r).
    * subst. 
      rewrite Nat.eqb_refl.
      simpl.
      rewrite interp_asm_ret.      
      rewrite interp_asm_GetReg.

      unfold trigger.
      unfold interp_asm, run_map.
      rewrite interp_vis. rewrite tau_eutt.
      cbn.
      repeat rewrite interp_state_bind.
      unfold CategoryOps.cat, Cat_Handler, Handler.cat. simpl.
      unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
      unfold insert.
      unfold embed, Embeddable_itree, Embeddable_forall, inl_, embed.
      rewrite interp_trigger. rewrite tau_eutt.
      rewrite interp_state_trigger. rewrite tau_eutt.
      cbn.
      rewrite interp_state_ret.
      rewrite bind_ret.
      rewrite interp_ret.
      repeat rewrite interp_state_ret.
      cbn.
      apply eqit_Ret.
      constructor; auto.
      apply EQ_registers_add; auto.
    * apply Nat.eqb_neq in n.
      rewrite n.
      simpl.
      apply interp_asm_ret_tt; auto. reflexivity.
Qed.      

End Correctness.