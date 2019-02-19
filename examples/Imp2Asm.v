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

(* this is what we need for seq *)
Definition link_seq (p1 : program unit) (p2 : program unit) : program unit.
refine
  (let transL l :=
      match l with
      | inl l => inl (inl l)
      | inr tt => inl (inr None) (* *)
      end
  in
   let transR l :=
       match l with
       | inl l => inl (inr (Some l))
       | inr tt => inr tt
       end
   in
  {| label := p1.(label) + option p2.(label)
   ; main := fmap_block transL p1.(main)
   ; blocks l :=
       match l with
       | inl l => fmap_block transL (p1.(blocks) l)
       | inr None => fmap_block transR p2.(main)
       | inr (Some l) => fmap_block transR (p2.(blocks) l)
       end
  |}).
Defined.





Definition link_if (b : block bool) (p1 : program unit) (p2 : program unit)
: program unit.
refine
  (let to_right x :=
          match x with
          | inl y => inl (inr (Some y))
          | inr y => inr y
          end
      in
      let to_left x :=
          match x with
          | inl y => inl (inl (Some y))
          | inr y => inr y
          end
      in
      let lc := p1 in
      let rc := p2 in

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
             fmap_block (fun l =>
                           match l with
                           | true => inl (inl None)
                           | false => inl (inr None)
                           end) b
      |}).

Admitted.

Definition link_while (b : block bool) (p1 : program unit)
: program unit.
Admitted.


(*
Record program2 (exports imports : Type) : Type :=
  { internal2 : Type
  ; names : exports -> internal2
  ; blocks2 : internal2 -> block (internal2 + imports) }.

Definition link2 {A B C} (p1 : program2 A (B + C)) (p2 : program2 B (A + C))
: program2 (A + B) C.

rec : program2 a (a + b) -> program a b
*)

(* we could change this to `stmt -> program unit` and then compile the subterms
 * and then replace some of the jumps to do the actual linking.
 *
 * the type of `program` can not be printed because the type of labels is
 * exitentially quantified. it could be replaced with a finite map.
 *)
Fixpoint compile2 (s : stmt) {struct s} : program unit.
  refine
    match s with

    | Skip =>

      {| label  := Empty_set
       ; blocks := fun x => match x with end
       ; main   := bbb (Bjmp (inr tt)) |}

    | Assign x e =>

      {| label  := Empty_set
         ; blocks := fun x => match x with end
         ; main   := after (compile_assign x e)
                             (bbb (Bjmp (inr tt))) |}

    | Seq l r =>

      link_seq (compile2 l) (compile2 r)

    | If e l r =>

      let to_right x :=
          match x with
          | inl y => inl (inr (Some y))
          | inr y => inr y
          end
      in
      let to_left x :=
          match x with
          | inl y => inl (inl (Some y))
          | inr y => inr y
          end
      in
      let lc := compile2 l in
      let rc := compile2 r in

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
             after (compile_expr 0 e)
                   (bbb (Bbrz (gen_tmp 0)
                              (inl (inl None))
                              (inl (inr None))))
      |}

    | While e b =>
      let bc := compile2 b in
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
                    after (compile_expr 0 e)
                          (bbb (Bbrz (gen_tmp 0)
                                     (inl (inr None))
                                     (inl (inl WhileBottom))))
                  | inl WhileBottom => (* after the loop exits *)
                    bbb (Bjmp (inr tt))
                  | inr None =>
                    fmap_block convert bc.(main)
                  | inr (Some x) =>
                    fmap_block convert (bc.(blocks) x)
                  end
         ; main := bbb (Bjmp (inl (inl WhileTop)))
      |}

    end.
Defined.



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

      {| label  := lc.(label) + option rc.(label)
       ; blocks := fun x =>
                     match x with
                     | inr None => fmap_block _ rc.(main)
                     | inl x => fmap_block _ (lc.(blocks) x)
                     | inr (Some x) => fmap_block _ (rc.(blocks) x)
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

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, alist_In k_imp g_imp v -> alist_In k_asm g_asm v.

  (* Let's not unfold this inside of the main proof *)
  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\ (* we don't corrupt any of the imp variables *)
      alist_In (gen_tmp n) g_asm' v /\ (* we get the right value *)
      (forall m, m < n -> forall v, (* we don't mess with anything on the "stack" *)
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

  (* A key is stored at most once in the map *)
  (* Oopsy daisy, though all alist operations preserve this invariant, its type does not state so *)
  (* To avoid using if possible *)
  (* Lemma alist_unique_key {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}: *)
  (*   forall k (m: alist K V) v v', *)
  (*     In (k,v) m -> In (k,v') m -> v = v'. *)
  (* Proof. *)
  (* Admitted. *)

  (* alist_find succeeds iff the same value is associated to the key in the map *)
  (* Same here, the value found is always the same only with respect to a global invariant over alist *)
  (* Lemma alist_find_In_iff {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}: *)
  (*   forall k v (m: alist K V), *)
  (*     alist_In k m v <-> alist_find k m = Some v. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma Renv_add: forall g_asm g_imp n v,
      Renv g_asm g_imp -> Renv (alist_add (gen_tmp n) v g_asm) g_imp.
  Proof.
    repeat intro.
    destruct (k_asm ?[ eq ] (gen_tmp n)) eqn:EQ.
    rewrite rel_dec_correct in EQ; subst; inv H0.
    rewrite <- neg_rel_dec_correct in EQ.
    eapply H in H1; [| eassumption].
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
    - (* YZ: does not hold, the invariant does not prevent the assembly stack to have more non temp variables defined than the source.
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
      alist_find (gen_tmp n) g_asm' = Some v.
  Admitted.

  Lemma sim_rel_find_tmp_lt_n:
    forall g_asm n m g_asm' g_imp' v,
      m < n ->
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_find (gen_tmp m) g_asm = alist_find (gen_tmp m) g_asm'.
  Admitted.

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
        apply eutt_Ret.
        split; [| split].
        {
          eapply Renv_add, sim_rel_Renv; eassumption.
        }
        {
          generalize HSIM'; intros HSIM'2; apply sim_rel_find_tmp_n in HSIM'.
          setoid_rewrite HSIM'; clear HSIM'.
          eapply sim_rel_find_tmp_lt_n with (m := n) in HSIM'2; [simpl fst in HSIM'2| auto with arith].
          apply sim_rel_find_tmp_n in HSIM; rewrite HSIM'2 in HSIM.
          setoid_rewrite HSIM.
          apply In_add_eq.
        }
        {
          simpl fst in *.
          intros m LT v''.
          rewrite <- In_add_ineq_iff; [| apply gen_tmp_inj; lia].
          admit.
        }
  Admitted.

  Lemma Renv_write_local:
    forall (x : Imp.var) (a a0 : alist var value) (v : Imp.value),
      Renv a a0 -> Renv (alist_add (varOf x) v a) (alist_add x v a0).
  Proof.
    intros x a a0 v H0.
    red in H0. red.
    intros.
    (* this should mostly come from ExtLib *)
  Admitted.

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

    Require Import ITree.MorphismsFacts.
    Require Import ITree.FixFacts.

    Lemma rec_unfold {E A B} (f : A -> itree (callE A B +' E) B) (x : A)
      : rec f x ≈ interp (fun _ e => match e with
                                  | inl1 e =>
                                    match e in callE _ _ t return _ with
                                    | Call x => rec f x
                                    end
                                  | inr1 e => lift e
                                  end) _ (f x).
    Proof.
      unfold rec. unfold mrec.
      rewrite interp_mrec_is_interp.
      repeat rewrite <- MorphismsFacts.interp_is_interp1.
      unfold MorphismsFacts.interp_match.
      unfold mrec.
      SearchAbout interp Proper.
      Definition Rhom {E F : Type -> Type} : relation (E ~> F) :=
        fun l r =>
          forall x (e : E x), l _ e = r _ e.
      Lemma eq_itree_interp:
  forall (E F : Type -> Type) (R : Type),
    Proper (@Rhom E (itree F) ==> eutt eq ==> eutt eq)
           (fun f => interp f R).
      Proof. Admitted.
      eapply eq_itree_interp.
      { red. destruct e; try reflexivity.
        destruct c.
        reflexivity. }
      reflexivity.
    Qed.


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
