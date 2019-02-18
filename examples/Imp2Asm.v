Require Import Imp Asm.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ITree Require Import
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

Variant WhileBlocks : Set :=
| WhileTop
| WhileBottom.

(*
  Compiles a statement given a partially built continuation 'k' expressed as a block.
 *)
(* YZ: Need another generator of fresh variables to store the result of conditionals.
   Though they should never be reused if I'm not mistaken, so a unique reserved id as currently is might actually simply do the trick.
   To double check.
 *)

(* we could change this to `stmt -> program unit` and then compile the subterms
 * and then replace some of the jumps to do the actual linking.
 *
 * the type of `program` can not be printed because the type of labels is
 * exitentially quantified. it could be replaced with a finite map.
 *)
Fixpoint compile (s : stmt) {L} (k : block L) {struct s} : program L.
  refine
    match s with

    | Skip =>

      {| label  := Empty_set
         ; blocks := fun x => match x with end
         ; main   := fmap_block inr k |}

    | Assign x e =>

      {| label  := Empty_set
         ; blocks := fun x => match x with end
         ; main   := after (compile_assign x e)
                             (fmap_block inr k) |}

    | Seq l r =>

      let reassoc :=
          (fun x => match x with
                 | inl x => inl (inl x)
                 | inr (inl x) => inl (inr x)
                 | inr (inr x) => inr x
                 end)
      in
      let to_right :=
          (fun x => match x with
                 | inl x => inl (inr x)
                 | inr x => inr x
                 end)
      in

      let rc := @compile r L k in
      let lc := @compile l (sum rc.(label) L) rc.(main) in

      {| label  := lc.(label) + rc.(label)
         ; blocks := fun x =>
                         match x with
                         | inl x => fmap_block reassoc (lc.(blocks) x)
                         | inr x => fmap_block to_right (rc.(blocks) x)
                         end
         ; main   :=
             fmap_block reassoc lc.(main) |}

(*
      let lc := @compile l unit (bbb (Bjmp tt)) in
      let rc := @compile r L k in

      {| label  := option (lc.(label) + rc.(label))
       ; blocks := fun x =>
                     match x with
                     | None => fmap_block _ rc.(main)
                     | Some (inl x) => fmap_block _ (lc.(blocks) x)
                     | Some (inr x) => fmap_block _ (rc.(blocks) x)
                     end
       ; main   :=
           fmap_block _ lc.(main) |}
*)
    | If e l r =>
      let to_right := (fun x =>
                         match x with
                         | inl y => inl (inr (Some y))
                         | inr y => inr y
                         end)
      in
      let to_left := (fun x =>
                        match x with
                        | inl y => inl (inl (Some y))
                        | inr y => inr y
                        end)
      in
      let lc := @compile l L k in
      let rc := @compile r L k in

      {| label  := option lc.(label) + option rc.(label)
         ; blocks := fun x =>
                         match x with
                         | inl None =>
                           fmap_block to_left lc.(main)
                         | inl (Some x) =>
                           fmap_block to_left (lc.(blocks) x)
                         | inr None =>
                           fmap_block to_right rc.(main)
                         | inr (Some x) =>
                           fmap_block to_right (rc.(blocks) x)
                         end
         ; main   :=
             after (compile_assign "_jump_var" e)
                   (bbb (Bbrz "_jump_var"
                              (inl (inl None))
                              (inl (inr None))))
      |}

    | While e b =>
      let bc := compile b unit (bbb (Bjmp tt)) in
      {| label := WhileBlocks
                    + option bc.(label)
         ; blocks :=
             let convert x :=
                 match x with
                 | inl x => inl (inr (Some x))
                 | inr x => inl (inl WhileTop)
                 end
             in fun x =>
                  match x with
                  | inl WhileTop => (* before evaluating e *)
                    after (compile_assign "_jump_var" e)
                          (bbb (Bbrz "_jump_var"
                                     (inl (inr None))
                                     (inl (inl WhileBottom))))
                  | inl WhileBottom => (* after the loop exits *)
                    fmap_block inr k
                  | inr None =>
                    fmap_block convert bc.(main)
                  | inr (Some x) =>
                    fmap_block convert (bc.(blocks) x)
                  end
         ; main := bbb (Bjmp (inl (inl WhileTop)))
      |}

    end.
Defined.

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
  Admitted.
  
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

  Arguments denote_program {_ _ _}.

  Import ITree.Core.

  Variable E: Type -> Type.
  Context {HasLocals: Locals -< E} {HasMemory: Memory -< E}.

  Lemma fmap_block_map:
    forall  {L L'} b (f: L -> L'),
      denote_block E (fmap_block f b) ≅ ITree.map (option_map f) (denote_block E b).
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

  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, In (k_imp,v) g_imp -> In (k_asm, v) g_asm.

  (* Let's not unfold this inside of the main proof *)
  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\ (* we don't corrupt any of the imp variables *)
      In (gen_tmp n, v) g_asm' /\ (* we get the right value *)
      (forall m, m < n -> forall v, (* we don't mess with anything on the "stack" *)
            In (gen_tmp m, v) g_asm <-> In (gen_tmp m, v) g_asm').

End Correctness.

Section EUTT.

  Context {E: Type -> Type}.
  Lemma Vis_eutt: forall {R1 R2 RR} {U} (e: E U) k k',
      (forall x, @eutt E R1 R2 RR (k x) (k' x)) -> eutt RR (Vis e k) (Vis e k').
  Admitted.

  Lemma Ret_eutt: forall {R1 R2} {RR: R1 -> R2 -> Prop} x y, 
      RR x y -> @eutt E R1 R2 RR (Ret x) (Ret y).
  Admitted.

  Global Instance eutt_eq_under_rr {R1 R2 : Type} (RR: R1 -> R2 -> Prop):
    Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> iff) (eutt RR).
  Admitted.

  Global Instance reflexive_eutt {R} RR `{Reflexive _ RR}:
    Reflexive (@eutt E R R RR).
  Admitted.

  Instance eq_itree_run_env {E R} {K V map} {Mmap: Maps.Map K V map}:
    Proper (@eutt (envE K V +' E) R R eq ==> eq ==> @eutt E (prod map R) (prod map R) eq)
           (run_env R).
  Proof.
  Admitted.

  Lemma interp1_eq_eutt {F: Type -> Type} (h: E ~> itree F) R:
    @Proper (itree (E +' F) R -> itree F R) (eutt eq ==> eutt eq) (interp1 h R).
  Admitted.

End EUTT.

Section GEN_TMP.

  Lemma to_string_inj: forall (n m: nat), to_string n = to_string m -> n = m.
  Admitted.

  Lemma gen_tmp_inj: forall n m, m <> n -> gen_tmp m <> gen_tmp n.
  Proof.
    intros n m ineq; intros abs; apply ineq.
    apply to_string_inj; inversion abs; auto. 
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

  Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
    forall t1 t2,
      eutt RR t1 t2 ->
      forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
               @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
  Admitted.

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
  
  Lemma Renv_add: forall g_asm g_imp n v,
      Renv g_asm g_imp -> Renv (alist_add (gen_tmp n) v g_asm) g_imp.
  Admitted.

  Lemma In_alist_add {K V: Type} `{RelDec _ (@eq K)}:
    forall k v (m: alist K V),
      In (k,v) (alist_add k v m).
  Admitted.

  Lemma alist_find_In_iff {K V: Type} `{RR: RelDec _ (@eq K)} `{@RelDec_Correct _ _ RR}:
    forall k v (m: alist K V),
      In (k,v) m <-> alist_find k m = Some v.
  Admitted.

  Lemma alist_find_None {K V: Type} `{RR: RelDec _ (@eq K)} `{@RelDec_Correct _ _ RR}:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Admitted.

  Lemma In_add_ineq {K V: Type} `{RR: RelDec _ (@eq K)} `{@RelDec_Correct _ _ RR}:
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      In (k, v) m <-> In (k, v) (alist_add k' v' m).
  Proof.
  Admitted.

  Lemma alist_unique_key {K V: Type} `{RR: RelDec _ (@eq K)} `{@RelDec_Correct _ _ RR}:
    forall k v v' (m: alist K V),
      In (k,v) m -> In (k, v') m -> v = v'.
  Proof.
  Admitted.

  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_asm g_imp ->
      alist_find x g_imp = alist_find (varOf x) g_asm.
  Proof.
    intros.
    destruct (alist_find x g_imp) eqn:LUL, (alist_find (varOf x) g_asm) eqn:LUR; auto.
    - rewrite <- alist_find_In_iff in LUL,LUR.
      eapply H in LUL; [| constructor].
      f_equal; eapply alist_unique_key; eassumption.
    - rewrite <- alist_find_In_iff in LUL.
      eapply H in LUL; [| constructor].
      rewrite <- alist_find_None in LUR.
      exfalso; eapply LUR; eauto.
    - rewrite <- alist_find_None in LUL.
      rewrite <- alist_find_In_iff in LUR.
      (* YZ: does not hold, the invariant does not prevent the assembly stack to have more non temp variables defined than the source.
         Reinforce the invariant, or weaken this lemma.
       *)
  Admitted.

  Lemma sim_rel_add: forall g_asm g_imp n v,
      Renv g_asm g_imp ->
      sim_rel g_asm n (alist_add (gen_tmp n) v g_asm, tt) (g_imp, v).
  Proof.
    intros.
    split; [| split].
    - apply Renv_add; assumption.
    - apply In_alist_add.  
    - intros m LT v'.
      apply In_add_ineq, gen_tmp_inj; lia.
  Qed.     

  Lemma sim_rel_Renv: forall g_asm n sv1 sv2,
      sim_rel g_asm n sv1 sv2 -> Renv (fst sv1) (fst sv2).
  Proof.
    intros ? ? ? ? H; destruct sv1, sv2; apply H.
  Qed.
  
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
      apply Ret_eutt.
      erewrite <- Renv_find; [| eassumption].
      apply sim_rel_add; assumption.
    - repeat untau_left.
      force_left.
      force_right.
      apply Ret_eutt.
      apply sim_rel_add; assumption.
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption. 
      + intros.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros.
        repeat untau_left.
        force_left; force_right.
        apply Ret_eutt.
        split; [| split].
        {
          destruct r0, r3; simpl.
          admit.
        }
        {
          admit.
        }
        {
          admit.
        }
  Admitted.

(*
Seq a b
a :: itree _ Empty_set
[[Skip]] = Vis Halt ...
[[Seq Skip b]] = Vis Halt ...


[[s]] :: itree _ unit
[[a]] :: itree _ L (* if closed *)
*)

(*
Definition denote_program {e} `{Locals -< e} `{Memory -< e} {L}
           (p : program L) : p.(label) -> itree e (option L) :=
  rec (fun lbl : p.(label) =>
         next <- denote_block (_ +' e) (p.(blocks) lbl) ;;
              match next with
              | None => ret None
              | Some (inl next) => lift (Call next)
              | Some (inr next) => ret (Some next)
              end).

Definition denote_main {e} `{Locals -< e} `{Memory -< e} {L}
           (p : program L) : itree e (option L) :=
  next <- denote_block e p.(main) ;;
   match next with
   | None => ret None
   | Some (inl next) => denote_program p next
   | Some (inr next) => ret (Some next)
   end.

Lemma true_compile_correct_program:
    forall s L (b: block L) (g_imp g_asm : alist var value),
      Renv g_asm g_imp ->
      euttG (fun a b => Renv (fst a) (fst b) /\ snd a = snd b)
            (run_env _ (denote_main (compile s b)) g_asm)
            (run_env _ (denoteStmt s;; denote_block _ b) g_imp).
Proof.
  induction s.
  { admit. }
  { simpl.
    unfold denote_main. simpl.
    intros.
*)

        Arguments denote_program {_ _ _ _} _ _.
        Arguments denote_block {_ _ _ _} _.


  (*
    This statement does not hold. We need to handle the environment.
    We want something closer to this kind:
   *)

        (* TODO: parameterize by REnv *)
  Lemma compile_correct_program:
    forall s L (b: block L) imports,
      denote_main (compile s b) imports ≈
                  (denoteStmt s;; ml <- denote_block b;;
                              (match ml with
                               | None => Ret tt
                               | Some l => imports l
                               end)).
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