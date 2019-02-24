Require Import Imp Asm.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ITree Require Import
     Basics_Functions
     Effect.Env
     ITree.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Programming.Show
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.

Section compile_assign.

  Definition gen_tmp (n: nat): string :=
    "temp_" ++ to_string n.

  Definition varOf (s : var) : var := "local_" ++ s.

  Fixpoint compile_expr (l: nat) (e: expr): list instr :=
    match e with
    | Var x => [Imov (gen_tmp l) (Ovar (varOf x))]
    | Lit n => [Imov (gen_tmp l) (Oimm n)]
    | Plus e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (S l) e2 in
      instrs1 ++ instrs2 ++ [Iadd (gen_tmp l) (gen_tmp l) (Ovar (gen_tmp (S l)))]
    end.

  Definition compile_assign (x: Imp.var) (e: expr): list instr :=
    let instrs := compile_expr 0 e in
    instrs ++ [Imov (varOf x) (Ovar (gen_tmp 0))].

End compile_assign.

Section after.
  Context {a : Type}.
  Fixpoint after (is : list instr) (blk : block a) : block a :=
    match is with
    | nil => blk
    | i :: is => bbi i (after is blk)
    end.
End after.

Section fmap_block.
  Context {a b : Type} (f : a -> b).

  Definition fmap_branch (blk : branch a) : branch b :=
    match blk with
    | Bjmp x => Bjmp (f x)
    | Bbrz v a b => Bbrz v (f a) (f b)
    | Bhalt => Bhalt
    end.

  Fixpoint fmap_block (blk : block a) : block b :=
    match blk with
    | bbb x => bbb (fmap_branch x)
    | bbi i blk => bbi i (fmap_block blk)
    end.
End fmap_block.

Definition link_seq (p1: asm unit Empty_set) (p2: asm unit Empty_set): asm unit Empty_set :=
  let transL l :=
      match l with
      | inl l => inl (inl l)
      | inr _ => inl (inr None)
      end
  in
  let transR l :=
      match l with
      | inl l => inl (inr (Some l))
      | inr l => inr l
      end
  in
  {| internal := p1.(internal) + option p2.(internal)
     ; code l :=
         match l with
         | inl (inl l) =>        (* p1's internal *)
           fmap_block transL (p1.(code) (inl l))           
         | inl (inr None) =>     (* p2's entry point *)
           fmap_block transR (p2.(code) (inr tt))       
         | inl (inr (Some l)) => (* p2's internal *)
           fmap_block transR (p2.(code) (inl l))    
         | inr tt =>             (* p1's entry point *)
           fmap_block transL (p1.(code) (inr tt))               
         end
  |}.

Definition link_if (e : list instr) (lp : asm unit Empty_set) (rp : asm unit Empty_set) : asm unit Empty_set :=
  let to_left l :=
      match l with
      | inl l => inl (inl (Some l))
      | inr l => inr l
      end
  in
  let to_right l :=
      match l with
      | inl l => inl (inr (Some l))
      | inr l => inr l
      end
  in

  {| internal  := option lp.(internal) + option rp.(internal)
     ; code l :=
         match l with
         | inr tt =>             (* Entry point to the conditional *)
           after e (bbb (Bbrz (gen_tmp 0) (inl (inl None)) (inl (inr None))))
         | inl (inl None) =>     (* Entry point to the left branch *)
           fmap_block to_left (lp.(code) (inr tt))
         | inl (inl (Some l)) => (* Inside the left branch *)
           fmap_block to_left (lp.(code) (inl l))
         | inl (inr None) =>     (* Entry point to the right branch *)
           fmap_block to_right (rp.(code) (inr tt))
         | inl (inr (Some l)) => (* Inside the right branch *)
           fmap_block to_right (rp.(code) (inl l))
         end
  |}.


Variant WhileBlocks : Set :=
| WhileTop
| WhileBottom.

Definition link_loop (e : list instr) (bp : asm unit Empty_set): asm unit Empty_set :=
  let to_body l :=
      match l with
      | inl l => inl (inr l)
      | inr l => inr l
      end
  in

  {| internal := WhileBlocks + bp.(internal)
     ; code l :=
         match l with
         | inr tt =>                (* Entry point to the loop *)
           after e (bbb (Bbrz (gen_tmp 0) (inl (inl WhileTop)) (inl (inl WhileBottom)))) 
         | inl (inl WhileTop) =>    (* Entry point to the body *)
           fmap_block to_body (bp.(code) (inr tt))                                       
         | inl (inl WhileBottom) => (* Exit point *)
           bbb Bhalt                                                                     
         | inl (inr l) =>           (* Inside the body *)
           fmap_block to_body (bp.(code) (inl l))                                        
         end
  |}.

Set Nested Proofs Allowed.

Fixpoint compile (s : stmt) {struct s} : asm unit Empty_set :=
  match s with

  | Skip =>

    {| internal  := Empty_set
       ; code := fun _ => bbb Bhalt |}

  | Assign x e =>

    {| internal  := Empty_set
       ; code := fun _ => after (compile_assign x e)
                             (bbb Bhalt) |}

  | Seq l r => link_seq (compile l) (compile r)


  | If e l r => link_if (compile_expr 0 e) (compile l) (compile r)

  | While e b => link_loop (compile_expr 0 e) (compile b)
                          
  end.

Section denote_list.

  Import MonadNotation.

  Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
    fix traverse__ l: M unit :=
      match l with
      | [] => ret tt
      | a::l => (f a;; traverse__ l)%monad
      end.

  Context {E} {EL : Locals -< E} {EM : Memory -< E}.

  Definition denote_list: list instr -> itree E unit :=
    traverse_ (denote_instr E).

  Lemma denote_after_denote_list:
    forall {label: Type} instrs (b: block label),
      denote_block E (after instrs b) ≅ (denote_list instrs ;; denote_block E b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite ret_bind; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eq_itree_eq_bind; [reflexivity | intros []; apply IH].
  Qed.

  Lemma denote_list_app:
    forall is1 is2,
      @denote_list (is1 ++ is2) ≅
                   (@denote_list is1;; denote_list is2).
  Proof.
    intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite ret_bind; reflexivity |].
    rewrite bind_bind; setoid_rewrite IH; reflexivity.
  Qed.

End  denote_list.

Section Correctness.

  (*
    Potential extensions for later:
    - Add some non-determinism at the source level, for instance order of evaluation in add, and have the compiler  an order.
    The correctness would then be a refinement.
     How to define it? Likely with respect to an oracle.
    - Add a print effect?
    - Change languages to map two notions of state at the source down to a single one at the target?
      Make the keys of the second env monad as the sum of the two initial ones.
   *)


  Import ITree.Core.

  Variable E: Type -> Type.
  Context {HasLocals: Locals -< E} {HasMemory: Memory -< E}.

  Lemma fmap_block_map:
    forall  {L L'} b (f: L -> L'),
      denote_block E (fmap_block f b) ≅ ITree.map (sum_bimap f id) (denote_block E b).
  Proof.
    induction b as [i b | br]; intros f.
    - simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_eq_bind; [reflexivity | intros []; apply IHb].
    - simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite ret_bind; reflexivity.
      + unfold ITree.map; rewrite bind_bind.
        eapply eq_itree_eq_bind; [reflexivity | intros []; rewrite ret_bind; reflexivity].
      + unfold ITree.map; rewrite ret_bind; reflexivity.
  Qed.

  Variant Rvar : var -> var -> Prop :=
  | Rvar_var v : Rvar (varOf v) v.

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, alist_In k_imp g_imp v <-> alist_In k_asm g_asm v.

  (* Let's not unfold this inside of the main proof *)
  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\            (* we don't corrupt any of the imp variables *)
      alist_In (gen_tmp n) g_asm' v /\ (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            alist_In (gen_tmp m) g_asm v <-> alist_In (gen_tmp m) g_asm' v).

End Correctness.

Section EUTT.

  Require Import Paco.paco.

  Context {E: Type -> Type}.

  Instance eq_itree_run_env {E R} {K V map} {Mmap: Maps.Map K V map}:
    Proper (@eutt (envE K V +' E) R R eq ==> eq ==> @eutt E (prod map R) (prod map R) eq)
           (run_env R).
  Proof.
  Admitted.

End EUTT.

Section GEN_TMP.

  Lemma to_string_inj: forall (n m: nat), n <> m -> to_string n <> to_string m.
  Admitted.

  Lemma gen_tmp_inj: forall n m, m <> n -> gen_tmp m <> gen_tmp n.
  Proof.
    intros n m ineq; intros abs; apply ineq.
    apply to_string_inj in ineq; inversion abs; easy.
  Qed.

  Lemma varOf_inj: forall n m, m <> n -> varOf m <> varOf n.
  Proof.
    intros n m ineq abs; inv abs; easy.
  Qed.

End GEN_TMP.

Opaque gen_tmp.
Opaque varOf.

Section Real_correctness.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Definition E := Locals +' E'.

  Definition interp_locals {R: Type} (t: itree E R) (s: alist var value): itree E' (alist var value * R) :=
    run_env _ (interp1 evalLocals _ t) s.

  Instance eq_itree_interp_locals {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (alist var value) R) (prod _ R) eq)
           interp_locals.
  Proof.
  Admitted.

  Lemma interp_locals_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (s: alist var value),
      @eutt E' _ _ eq
            (interp_locals (ITree.bind t k) s)
            (ITree.bind (interp_locals t s) (fun s' => interp_locals (k (snd s')) (fst s'))).
  Admitted.

  Set Nested Proofs Allowed.

  Ltac force_left :=
    match goal with
    | |- eutt _ ?x _ => rewrite (itree_eta x); cbn
    end.

  Ltac force_right :=
    match goal with
    | |- eutt _ _ ?x => rewrite (itree_eta x); cbn
    end.

  Ltac untau_left := force_left; rewrite tau_eutt.
  Ltac untau_right := force_right; rewrite tau_eutt.

  Arguments alist_add {_ _ _ _}.
  Arguments alist_find {_ _ _ _}.

  Ltac flatten_goal :=
    match goal with
    | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac flatten_hyp h :=
    match type of h with
    | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac flatten_all :=
    match goal with
    | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
    | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac inv h := inversion h; subst; clear h.
  Arguments alist_remove {_ _ _ _}. 

  Lemma In_add_eq {K V: Type} {RR:RelDec eq} {RRC:@RelDec_Correct _ _ RR}:
    forall k v (m: alist K V),
      alist_In k (alist_add k v m) v.
  Proof.
    intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
  Qed.

  (* A removed key is not contained in the resulting map *)
  Lemma not_In_remove:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v: V),
      ~ alist_In k (alist_remove k m) v.
  Proof.
    induction m as [| [k1 v1] m IH]; intros.
    - simpl; intros abs; inv abs. 
    - simpl; flatten_goal.
      + unfold alist_In; simpl.
        rewrite Bool.negb_true_iff in Heq; rewrite Heq.
        intros abs; eapply IH; eassumption.
      + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        intros abs; eapply IH; eauto. 
  Qed.

  (* Removing a key does not alter other keys *)
  Lemma In_In_remove_ineq:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_remove k' m) v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
    simpl.
    flatten_goal.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
      flatten_goal; auto.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
      flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
  Qed.       

  Lemma In_remove_In_ineq:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      alist_In k (alist_remove k' m) v ->
      alist_In k m v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
    simpl in IN; flatten_hyp IN.
    - unfold alist_In in *; simpl in *.
      flatten_all; auto.
      eapply IH; eauto.
    -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
     unfold alist_In; simpl. 
     flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
     exfalso; eapply not_In_remove; eauto.
     eapply IH; eauto.
  Qed.       

  Lemma In_remove_In_ineq_iff:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k (alist_remove k' m) v <->
      alist_In k m v.
  Proof.
    intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
  Qed.       

  (* Adding a value to a key does not alter other keys *)
  Lemma In_In_add_ineq {K V: Type} {RR: RelDec eq} `{RRC:@RelDec_Correct _ _ RR}:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_add k' v' m) v.
  Proof.
    intros.
    unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
    apply In_In_remove_ineq; auto.
  Qed.

  Lemma In_add_In_ineq {K V: Type} {RR: RelDec eq} `{RRC:@RelDec_Correct _ _ RR}:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k (alist_add k' v' m) v ->
      alist_In k m v. 
  Proof.
    intros k v k' v' m ineq IN.
    unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
    eapply In_remove_In_ineq; eauto.
  Qed.

  Lemma In_add_ineq_iff {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}:
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      alist_In k m v <-> alist_In k (alist_add k' v' m) v.
  Proof.
    intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
  Qed.

  (* alist_find fails iff no value is associated to the key in the map *)
  Lemma alist_find_None {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Proof.
    induction m as [| [k1 v1] m IH]; [simpl; easy |].
    simpl; split; intros H. 
    - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
      apply (H v1); left; reflexivity.
      apply IH; intros v abs; apply (H v); right; assumption.
    - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
      intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
  Qed.

  Lemma Renv_add: forall g_asm g_imp n v,
      Renv g_asm g_imp -> Renv (alist_add (gen_tmp n) v g_asm) g_imp.
  Proof.
    repeat intro.
    destruct (k_asm ?[ eq ] (gen_tmp n)) eqn:EQ.
    rewrite rel_dec_correct in EQ; subst; inv H0.
    rewrite <- neg_rel_dec_correct in EQ.
    rewrite (H _ _ H0).
    apply In_add_ineq_iff; auto.
  Qed.

  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_asm g_imp ->
      alist_find x g_imp = alist_find (varOf x) g_asm.
  Proof.
    intros.
    destruct (alist_find x g_imp) eqn:LUL, (alist_find (varOf x) g_asm) eqn:LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - erewrite <- (H (varOf x) x (Rvar_var x) v) in LUR.
      rewrite LUR in LUL; inv LUL.
  Qed.      

  Lemma sim_rel_add: forall g_asm g_imp n v,
      Renv g_asm g_imp ->
      sim_rel g_asm n (alist_add (gen_tmp n) v g_asm, tt) (g_imp, v).
  Proof.
    intros.
    split; [| split].
    - apply Renv_add; assumption.
    - apply In_add_eq.
    - intros m LT v'.
      apply In_add_ineq_iff, gen_tmp_inj; lia.
  Qed.

  Lemma sim_rel_Renv: forall g_asm n s1 v1 s2 v2,
      sim_rel g_asm n (s1,v1) (s2,v2) -> Renv s1 s2.
  Proof.
    intros ? ? ? ? ? ? H; apply H.
  Qed.

  Lemma sim_rel_find_tmp_n:
    forall g_asm n g_asm' g_imp' v,
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_In (gen_tmp n) g_asm' v.
  Proof.
    intros ? ? ? ? ? [_ [H _]]; exact H. 
  Qed.

  Lemma sim_rel_find_tmp_lt_n:
    forall g_asm n m g_asm' g_imp' v,
      m < n ->
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_find (gen_tmp m) g_asm = alist_find (gen_tmp m) g_asm'.
  Proof.
    intros ? ? ? ? ? ? ineq [_ [_ H]].
    match goal with
    | |- _ = ?x => destruct x eqn:EQ
    end.
    setoid_rewrite (H _ ineq); auto.
    match goal with
    | |- ?x = _ => destruct x eqn:EQ'
    end; [| reflexivity].
    setoid_rewrite (H _ ineq) in EQ'.
    rewrite EQ' in EQ; easy.
  Qed.

  Notation "(% x )" := (gen_tmp x) (at level 1).

  Lemma compile_expr_correct : forall e g_imp g_asm n,
      Renv g_asm g_imp ->
      eutt (sim_rel g_asm n)
           (interp_locals (denote_list (compile_expr n e)) g_asm)
           (interp_locals (denoteExpr e) g_imp).
  Proof.
    induction e; simpl; intros.
    - repeat untau_left.
      repeat untau_right.
      force_left; force_right.
      apply eutt_Ret.
      erewrite <- Renv_find; [| eassumption].
      apply sim_rel_add; assumption.
    - repeat untau_left.
      force_left.
      force_right.
      apply eutt_Ret.
      apply sim_rel_add; assumption.
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption.
      + intros [g_asm' []] [g_imp' v] HSIM.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros [g_asm'' []] [g_imp'' v'] HSIM'.
        repeat untau_left.
        force_left; force_right.
        simpl fst in *.
        apply eutt_Ret.
        {
          generalize HSIM; intros LU; apply sim_rel_find_tmp_n in LU.
          unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto; fold (alist_In (%n) g_asm'' v) in LU.
          generalize HSIM'; intros LU'; apply sim_rel_find_tmp_n in LU'.
          rewrite LU,LU'.
          split; [| split].
          {
            eapply Renv_add, sim_rel_Renv; eassumption.
          }
          {
            apply In_add_eq.
          }
          {
            intros m LT v''.
            rewrite <- In_add_ineq_iff; [| apply gen_tmp_inj; lia].
            destruct HSIM as [_ [_ HSIM]].
            destruct HSIM' as [_ [_ HSIM']].
            rewrite HSIM; [| auto with arith].
            rewrite HSIM'; [| auto with arith].
            reflexivity.
          }
        }
  Qed.

  Lemma Renv_write_local:
    forall (x : Imp.var) (a a0 : alist var value) (v : Imp.value),
      Renv a a0 -> Renv (alist_add (varOf x) v a) (alist_add x v a0).
  Proof.
    intros k m m' v.
    repeat intro.
    red in H.
    specialize (H k_asm k_imp H0 v0).
    inv H0.
    unfold alist_add, alist_In; simpl.
    do 2 flatten_goal;
      repeat match goal with
             | h: _ = true |- _ => rewrite rel_dec_correct in h
             | h: _ = false |- _ => rewrite <- neg_rel_dec_correct in h
             end; try subst.
    - tauto.
    - tauto.
    - apply varOf_inj in Heq; easy.
    - setoid_rewrite In_remove_In_ineq_iff; eauto using RelDec_string_Correct.
Qed.

  Lemma compile_assign_correct : forall e g_imp g_asm x,
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b))
           (interp_locals (denote_list (compile_assign x e)) g_asm)
           (interp_locals (v <- denoteExpr e ;; lift (SetVar x v)) g_imp).
  Proof.
    simpl; intros.
    unfold compile_assign.
    rewrite denote_list_app.
    do 2 rewrite interp_locals_bind.
    eapply eutt_bind_gen.
    eapply compile_expr_correct; eauto.
    intros.
    repeat untau_left.
    force_left.
    repeat untau_right; force_right.
    eapply eutt_Ret; simpl.
    destruct r1, r2.
    erewrite sim_rel_find_tmp_n; eauto; simpl.
    destruct H0.
    eapply Renv_write_local; eauto.
  Qed.

(*
Seq a b
a :: itree _ Empty_set
[[Skip]] = Vis Halt ...
[[Seq Skip b]] = Vis Halt ...


[[s]] :: itree _ unit
[[a]] :: itree _ L (* if closed *)
*)


Definition denote_program {e} `{Locals -< e} `{Memory -< e} {L}
           (p : program L) : p.(label) -> itree e (option L) :=
  rec (fun lbl : p.(label) =>
         next <- denote_block (_ +' e) (p.(blocks) lbl) ;;
              match next with
              | None => ret None
              | Some (inl next) => lift (Call next)
              | Some (inr next) => ret (Some next)
              end).
  Arguments denote_program {_ _ _}.

    Require Import ITree.MorphismsFacts.
    Require Import ITree.FixFacts.

Definition denote_main {e} `{Locals -< e} `{Memory -< e} {L}
           (p : program L) : itree e (option L) :=
  next <- denote_block e p.(main) ;;
   match next with
   | None => ret None
   | Some (inl next) => denote_program p next
   | Some (inr next) => ret (Some next)
   end.

Arguments denote_block {_ _ _ _} _.
Arguments interp {_ _} _ {_} _.
Lemma interp_match_option : forall {T U} (x : option T) {E F} (h : E ~> itree F) (Z : itree _ U) Y,
    interp h match x with
             | None => Z
             | Some y => Y y
             end =
match x with
| None => interp h Z
| Some y => interp h (Y y)
end.
Proof. destruct x; reflexivity. Qed.
Lemma interp_match_sum : forall {A B U} (x : A + B) {E F} (h : E ~> itree F) (Z : _ -> itree _ U) Y,
    interp h match x with
             | inl x => Z x
             | inr x => Y x
             end =
match x with
| inl x => interp h (Z x)
| inr x => interp h (Y x)
end.
Proof. destruct x; reflexivity. Qed.

Lemma translate_match_sum : forall {A B U} (x : A + B) {E F} (h : E ~> F) (Z : _ -> itree _ U) Y,
    translate h match x with
             | inl x => Z x
             | inr x => Y x
             end =
match x with
| inl x => translate h (Z x)
| inr x => translate h (Y x)
end.
Proof. destruct x; reflexivity. Qed.
Lemma translate_match_option : forall {B U} (x : option B) {E F} (h : E ~> F) (Z : itree _ U) Y,
    translate h _ match x with
             | None => Z
             | Some x => Y x
             end =
match x with
| None => translate h Z
| Some x => translate h (Y x)
end.
Proof. destruct x; reflexivity. Qed.

(*
Proper (.. ==> eutt _) (rec _)

let rec F := ... in
let rec G := ... in

let rec F := let G := ... in ... in
*)

(*
Lemma link_ok : forall p1 p2 l,
    denote_program (link_seq p1 p2) l ≈
    rec (fun l => 
           match l with
           | inl l =>
             l' <- denote_program p1 l ;;
                match l' with
                | None => Ret None
                | Some _ => denote_main p2
                end
           | inr None => denote_main p2
           | inr (Some l) => denote_program p2 l
           end) l.
*)

(* things to do?
 * 1. change the compiler to not compress basic blocks.
 *    - ideally we would write a separate pass that does that
 *    - split out each of the structures as separate definitions and lemmas
 * 2. need to prove `interp F (denote_block ...) = denote_block ...`
 * 3. link_seq_ok should be a proof by co-induction.
 * 4. clean up this file *a lot*
 * bonus: block fusion
 * bonus: break & continue
 *)

About rec.

Variant Fused {d1 d2 c1 c2 : Type} : Type -> Type :=
| Entry : Fused c2
| EnterL (_ : d1) : Fused c1
| EnterR (_ : d2) : Fused c2.
Arguments Fused : clear implicits.

Lemma rec_fuse : forall {E : Type -> Type} {dom1 codom1 dom2 codom2 : Type}
                   (f : dom1 -> itree (callE dom1 codom1 +' E) codom1)
                   (g : dom2 -> itree (callE dom2 codom2 +' E) codom2)
                   (x : dom1) (y : codom1 -> dom2),
  (l <- rec f x ;;
  rec g (y l))
  ≈
  @mrec (Fused dom1 dom2 codom1 codom2) E
  (fun _ elr =>
     match elr with
     | Entry => l <- lift (EnterL x) ;; lift (EnterR (y l))
     | EnterL x =>
       translate (fun Z x =>
                    match x with
                    | inl1 x =>
                      match x in callE _ _ z return (Fused _ _ _ _ +' _) z with
                      | Call x => inl1 (EnterL x)
                      end
                    | inr1 x => inr1 x
                    end) (f x)
     | EnterR x =>
       translate (fun Z x =>
                    match x with
                    | inl1 x =>
                      match x in callE _ _ z return (Fused _ _ _ _ +' _) z with
                      | Call x => inl1 (EnterR x)
                      end
                    | inr1 x => inr1 x
                    end) (g x)
     end) _ Entry.
Proof.
Admitted.

Variant Incl {d1 c1 T : Type} : Type -> Type :=
| EnterI : Incl T
| EnterF (_ : d1) : Incl c1.
Arguments Incl : clear implicits.


Lemma rec_fuse' : forall {E : Type -> Type} {dom1 codom1 T : Type}
                    (f : dom1 -> itree (callE dom1 codom1 +' E) codom1)
                    (k : codom1 -> itree E T)
                    (x : dom1),
  (l <- rec f x ;; k l)
  ≈
  @mrec (Incl dom1 codom1 T) E
  (fun _ elr =>
     match elr with
     | EnterI => l <- ITree.liftE (inl1 (EnterF x)) ;;
                 translate (fun _ x => inr1 x) (k l)
     | EnterF x =>
       translate (fun Z x =>
                    match x with
                    | inl1 x =>
                      match x in callE _ _ z return (Incl _ _ _ +' _) z with
                      | Call x => inl1 (EnterF x)
                      end
                    | inr1 x => inr1 x
                    end) (f x)
     end) _ EnterI.
Proof.
Admitted.

    (* 1. push translate over a match-option
     * 2. pull a rec from a continuation above the bind
     * 3. pull translate over a match-Incl
     * 4. fuse two adjacent mrec
     *)

(*
Lemma rec_k : forall {E : Type -> Type} {dom1 codom1 T : Type}
                    (f : dom1 -> itree (callE dom1 codom1 +' E) codom1)
                    (c : itree E T)
                    (k : T -> dom1),
  (l <- c ;; rec f (k l))
  ≈
  @mrec (Incl dom1 codom1 T) E
  (fun _ elr =>
     match elr with
     | EnterI => l <- translate (fun _ x => inr1 x) _ c ;;
                 ITree.liftE (inl1 (EnterF (k l)))
     | EnterF x =>
       translate (fun Z x =>
                    match x with
                    | inl1 x =>
                      match x in callE _ _ z return (Incl _ _ _ +' _) z with
                      | Call x => inl1 (EnterF x)
                      end
                    | inr1 x => inr1 x
                    end) _ (f x)
     end) _ EnterI.
Proof.
Admitted.
*)
About translate.
About mrec.


Lemma lem : forall {E : Type -> Type} {dom1 codom1 U : Type}
              (f : dom1 -> itree (Incl dom1 codom1 U +' E) codom1)
              (Z : itree (callE dom1 codom1 +' E) U)
              (l : dom1)
              ,
  @mrec (callE dom1 codom1) _
        (fun _ x =>
           match x with
           | Call x =>
             interp (E:=Incl dom1 codom1 U +' E) (F:=callE dom1 codom1 +' E)
                    (fun _ z =>
                       match z with
                       | inl1 x =>
                         match x with
                         | EnterI => Z
                         | EnterF x => ITree.liftE (inl1 (Call x))
                         end
                       | inr1 x => ITree.liftE (inr1 x)
                       end) (f x)
           end) _ (Call l)
  ≈
  @mrec (Incl dom1 codom1 U) _
        (fun _ x =>
          match x with
          | EnterI => translate (fun _ x =>
                                  match x with
                                  | inl1 x =>
                                    match x in callE _ _ X return (Incl dom1 codom1 U +' E) X with
                                    | Call x => inl1 (EnterF x)
                                    end
                                  | inr1 x => inr1 x
                                  end) Z
          | EnterF x => f x
          end) _ (EnterF l).
Abort.

(* rec_fuse' : `l <- rec ... ;; k` = rec ... *)
(* rec_k     : `l <- c ;; rec ...` = rec ... *)

(*
rec_rec : @rec T (fun x => @rec U ...) = @rec (T + U) (fun ...)
*)

Lemma lift_sum_rec : forall {A B C : Type} {E}
                    (L : A -> itree E C)
                    (R : B -> itree E C)
                    (l : A + B),
  match l with
  | inl x => L x
  | inr x => R x
  end =
  rec (A:=A + B)%type
       (fun x =>
          match x with
          | inl x => translate (fun _ x => inr1 x) (L x)
          | inr x => translate (fun _ x => inr1 x) (R x)
          end) l.
Proof. Admitted.

Variant With (T : Type) (E : Type -> Type) (t : Type) : Type :=
| WithIt (_ : T) (_ : E t) : With T E t.
Arguments WithIt {_ _ _} _ _.

Lemma lift_sum_rec_left
  : forall {B T u : Type} {D : Type -> Type} {E}
      (L : T -> D ~> itree (D +' E))
      (R : B -> itree E u)
      (f : T -> D u)
      (l : T + B),
  match l with
  | inl x => mrec (L x) _ (f x)
  | inr x => R x
  end =
  mrec (D:=(With T D +' callE B u))%type
      (fun _ x =>
         match x with
         | inl1 (WithIt t y) =>
           translate (fun _ x =>
                        match x with
                        | inl1 x => inl1 (inl1 (WithIt t x))
                        | inr1 x => inr1 x
                        end) (L t _ y)
         | inr1 x =>
           match x with
           | Call x => translate (fun _ x => inr1 x) (R x)
           end
         end) _ match l with
                | inl x => inl1 (WithIt x (f x))
                | inr x => inr1 (Call x)
                end.
Proof. Admitted.

Lemma Proper_match : forall {T U V : Type} R (f f' : T -> V) (g g' : U -> V) x,
    ((pointwise_relation _ R) f f') ->
    ((pointwise_relation _ R) g g') ->
    R
    match x with
    | inl x => f x
    | inr x => g x
    end
    match x with
    | inl x => f' x
    | inr x => g' x
    end.
Proof. destruct x; compute; eauto. Qed.

Lemma link_seq_ok : forall p1 p2 l,
    denote_program (link_seq p1 p2) l ≈
    match l with
    | inl l =>
      l' <- denote_program p1 l ;;
      match l' with
      | None => Ret None
      | Some _ => denote_main p2
      end
    | inr None => denote_main p2
    | inr (Some l) => denote_program p2 l
    end.
Proof.
  intros.
  unfold denote_program.
  rewrite Proper_match.
  2:{ red; intros.
      eapply rec_fuse'. }
  2:{ red. intros.
      instantiate (1:=fun a => match a with
  | Some l0 =>
      rec
        (fun lbl : label p2 =>
         next <- denote_block (blocks p2 lbl);;
         match next with
         | Some (inl next0) => lift (Call next0)
         | Some (inr next0) => ret (Some next0)
         | None => ret None
         end) l0
  | None => denote_main p2
  end).
      reflexivity. }
  simpl.
  rewrite lift_sum_rec_left with (f:=fun _ => EnterI).
      SearchAbout rec.
  rewrite lift_sum_rec.
  

  destruct l.
  { setoid_rewrite rec_fuse'. 
    simpl.
    setoid_rewrite translate_match_option.

  destruct l.
  { (* in the left *)
    unfold denote_program.
    rewrite rec_unfold at 1.
    repeat rewrite interp_bind.
    match goal with
    | |- ITree.bind ?X _ ≈ _ =>
      assert (X = (denote_block (blocks (link_seq p1 p2) (inl l))))
    end.
    admit.
    rewrite H.
    rewrite rec_unfold.
    repeat rewrite interp_bind.
    repeat rewrite bind_bind.
    match goal with
    | |- _ ≈ ITree.bind ?X _ =>
      assert (X = (denote_block (blocks p1 l)))
    end.
    admit.
    rewrite H0.
    simpl.
    rewrite fmap_block_map.
    unfold ITree.map.
    rewrite bind_bind.
    setoid_rewrite ret_bind.
    eapply eutt_bind_gen.
    { instantiate (1:=eq). reflexivity. }
    intros; subst.
    repeat rewrite interp_match_option.
    unfold option_map.
    destruct r2.
    { destruct s.
      - admit. 
      - destruct u. admit. }
    { admit. } }
  { unfold denote_program.
    simpl.

}
    


    Lemma denote_block_no_calls :
      interp (hBoth L id) (liftR id) = interp id e.

    Print denote_program.
    Print denote_block.
    simpl denote_block.
    Eval simpl in (denote_block (blocks (link_seq p1 p2) (inl l))).
    simpl.
   
    simpl.
    unfold denote_block at 2.
    simpl.
About denote_block.
setoid_rewrite interp_match_option.

    eapply eutt_bind_gen.
    Show Existentials.
    eapply eq_itree_interp.
    


    



    do 2 rewrite rec_unfold.

Admitted.

  Lemma true_compile_correct_program:
    forall s (g_imp g_asm : alist var value),
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b) /\ snd a = snd b)
            (interp_locals (denote_main (compile s)) g_asm)
            (interp_locals (denoteStmt s;; Ret (Some tt)) g_imp).








  Lemma true_compile_correct_program:
    forall s L (b: block L) (g_imp g_asm : alist var value),
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b) /\ snd a = snd b)
            (interp_locals (denote_main (compile s b)) g_asm)
            (interp_locals (denoteStmt s;; denote_block _ b) g_imp).
  Proof.
    induction s; intros.
    { (* assign *)
      simpl.
      unfold denote_main. simpl. unfold denote_program.
      simpl.
      rewrite denote_after_denote_list.
      rewrite bind_bind.
      rewrite interp_locals_bind.
      rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      eapply compile_assign_correct; eauto.
      simpl; intros.
      clear - H0.
      rewrite fmap_block_map.
      unfold ITree.map.
      rewrite bind_bind.
      setoid_rewrite ret_bind.
      rewrite <- (bind_ret (interp_locals _ (fst r2))).
      rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      { SearchAbout denote_block.
        instantiate (1 := fun a b => Renv (fst a) (fst b) /\ snd a = snd b).
        admit. }
      { simpl.
        intros.
        destruct r0, r3; simpl in *.
        destruct H; subst.
        destruct o0; simpl.
        { force_left.
          eapply Ret_eutt.
          simpl. tauto. }
        { force_left. eapply Ret_eutt; simpl. tauto. } } }
    { (* seq *)
      simpl.
      specialize (IHs1 _ (main (compile s2 b)) _ _ H).
      rewrite bind_bind.
      unfold denote_main; simpl.
      unfold denote_main in IHs1.
      rewrite fmap_block_map.
      unfold ITree.map. rewrite bind_bind.
      setoid_rewrite ret_bind.





        Arguments denote_program {_ _ _ _} _ _.
        Arguments denote_block {_ _ _ _} _.


  (*
    This statement does not hold. We need to handle the environment.
    We want something closer to this kind:
   *)

        (* TODO: parameterize by REnv *)
  Lemma compile_correct_program:
    forall s L (b: block L) imports g_asm g_imp,
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b))
           (interp_locals (denote_main (compile s b) imports) g_asm)
           (interp_locals (denoteStmt s;;
                           ml <- denote_block b;;
                           match ml with
                           | None => Ret tt
                           | Some l => imports l
                           end) g_imp).
  Proof.
(*    simpl.
    induction s; intros L b imports.

    - unfold denote_main; simpl.
      rewrite denote_after_denote_list; simpl.
      rewrite bind_bind.
      eapply eutt_bind.
      + apply denote_compile_assign.
      + intros ?; simpl.
        rewrite fmap_block_map, map_bind; simpl.
        eapply eutt_bind; [reflexivity|].
        intros [?|]; simpl; reflexivity.

    - simpl denoteStmt.
      specialize (IHs2 L b imports).
      unfold denote_main; simpl denote_block; rewrite fmap_block_map.
      unfold bind at 1, Monad_itree; rewrite map_bind.
      rewrite bind_bind.
      etransitivity.
      2:{
        eapply eutt_bind; [reflexivity |].
        intros ?; apply IHs2.
      }
      clear IHs2.
      unfold denote_main.
      set (imports' := (fun l => match l with
                              | inr l => imports l
                              | inl l => denote_program (compile s2 b) imports l
                              end)).
      specialize (IHs1 _ (main (compile s2 b)) imports').
      rewrite <- IHs1.
      unfold denote_main.
      apply eutt_bind; [reflexivity | ].
      intros [?|]; [| reflexivity].
      simpl option_map.
      destruct s as [s | [s | s]]; [| | reflexivity].
      + clear. subst imports'.
        simpl.
        unfold denote_program. simpl.
      + admit.

    - specialize (IHs1 L b imports).
      specialize (IHs2 L b imports).
      simpl denoteStmt.
      rewrite bind_bind.
      unfold denote_main.
      simpl.
      admit.

    - admit.

    - unfold denote_main; simpl.
      rewrite ret_bind, fmap_block_map, map_bind.
      eapply eutt_bind; [reflexivity |].
      intros [? |]; simpl; reflexivity.
*)
Admitted.

  (* note: because local temporaries also modify the environment, they have to be
   * interpreted here.
   *)
    Theorem compile_correct:
    forall s, @denote_main _ _ _ Empty_set (compile s (bbb Bhalt))
                      (fun x => match x with end) ≈ denoteStmt s.
  Proof.
(*    intros stmt.
    unfold denote_main.
    transitivity (@denoteStmt (Locals +' Memory) _ stmt;; Ret tt).
    {
      eapply eutt_bind; [reflexivity | intros []].
      simpl.
*)

  Admitted.

End Real_correctness.


(*
l: x = phi(l1: a, l2: b) ; ...
l1: ... ; jmp l
l2: ... ; jmp l

l: [x]
   ....
l1: ...; jmp[a]
l2: ...; jmp[b]
*)

(*

Section tests.

  Import ImpNotations.

  Definition ex1: stmt :=
    "x" ← 1.

  (* The result is a bit annoying to read in that it keeps around absurd branches *)
  Compute (compile ex1).

  Definition ex_cond: stmt :=
    "x" ← 1;;;
    IF "x"
    THEN "res" ← 2
    ELSE "res" ← 3.

  Compute (compile ex_cond).

End tests.


*)
