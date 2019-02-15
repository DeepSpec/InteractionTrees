Require Import Imp Asm.

Require Import Coq.Strings.String.
Import ListNotations.

Section compile_assign.

  (* YZ: How to handle locals used to compute a composed expression? *)
  (*
    Simply reserve the prefix "local", carry how many have been created, and generate "local_n"?
    Rough invariant: instrs = compile_expr_aux k e -> [instrs]σ = σ' -> σ'(gen_local k) = [e]
   *)

  (* YZ: Ascii.ascii_of_nat is not what we want, unreadable *)
  Definition gen_local (n: nat): string :=
    "local_" ++ (String (Ascii.ascii_of_nat n) "").

  (* Compiling mindlessly everything to the stack. Do we want to use asm's heap? *)
  Fixpoint compile_expr_aux (l: nat) (e: expr): (list instr * nat) :=
    match e with
    | Var x => ([Imov (gen_local l) (Ovar x)], S l)
    | Lit n => ([Imov (gen_local l) (Oimm n)], S l) 
    | Plus e1 e2 =>
      let (instrs1, l1) := compile_expr_aux (S l) e1 in
      let (instrs2, l2) := compile_expr_aux l1 e2 in
      (instrs1 ++ instrs2 ++ [Iadd (gen_local l) (gen_local (S l)) (Ovar (gen_local l1))], S l2)
    end.

  Definition compile_expr e := fst (compile_expr_aux 0 e).

  Definition compile_assign (x: Imp.var) (e: expr): list instr :=
    let instrs := compile_expr e in
    instrs ++ [Imov x (Ovar (gen_local 0))].

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
Open Scope string_scope.
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

From ITree Require Import
     ITree.

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
      denote_block E (fmap_block f b) ~~ ITree.map (option_map f) (denote_block E b).
  Proof.
    induction b as [i b | br]; intros f.
    - simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eutt_bind; [reflexivity | intros []; apply IHb].
    - simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite ret_bind; reflexivity. 
      + unfold ITree.map; rewrite bind_bind.
        eapply eutt_bind; [reflexivity | intros []; rewrite ret_bind; reflexivity].
      + unfold ITree.map; rewrite ret_bind; reflexivity.
  Qed.

  Require Import ExtLib.Structures.Monad.

  Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
    fix traverse__ l: M unit :=
      match l with
      | [] => ret tt
      | a::l => f a;; traverse__ l
      end.

  Definition denote_list: list instr -> itree E unit :=
    traverse_ (denote_instr E).

  Lemma denote_after_denote_list:
    forall {label: Type} instrs (b: block label),
      denote_block E (after instrs b) ~~ (denote_list instrs ;; denote_block E b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite ret_bind; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eutt_bind; [reflexivity | intros []; apply IH].
  Qed.

  Lemma denote_compile_assign :
    forall x e,
      denote_list (compile_assign x e) ~~ ITree.bind (denoteExpr e) (fun v : Imp.value => lift (SetVar x v)).
  Proof.
    (* induction e. *)
    (* - simpl; rewrite bind_bind. *)
      (* eapply eutt_bind; [reflexivity | intros ?]. *)
      (**
         This is wrong. They are not eutt since of course the compiled program does more SetVar actions than
the source.
       **)
  Admitted.

  (* NB: I think that notations defined in Core are binding the monadic bind instead of the itree one,
   hence why they do not show up here *)

  Lemma compile_correct_program:
    forall s L (b: block L) imports,
      denote_main (compile s b) imports ~~
                  (denoteStmt s;; ml <- denote_block _ b;;
                              (match ml with
                               | None => Ret tt
                               | Some l => imports l
                               end)).
  Proof.
(*    simpl.
    induction s; intros L b imports.
    5:{
      unfold denote_main; simpl.
      rewrite ret_bind, fmap_block_map, map_bind.
      eapply eutt_bind; [reflexivity |].
      intros [? |]; simpl; reflexivity.
    }      
    {
      unfold denote_main; simpl.
      rewrite denote_after_denote_list; simpl. 
      rewrite bind_bind.
      eapply eutt_bind.
      - apply denote_compile_assign.
      - intros ?; simpl.
        rewrite fmap_block_map, map_bind; simpl.
        eapply eutt_bind; [reflexivity|].
        intros [?|]; simpl; reflexivity.
    }      
    {
     simpl denoteStmt.
     specialize (IHs2 L b imports).
     match goal with
     | |- _ ~~ ?x => generalize x
     end.
     intros t.
     match goal with
     | h: _ ~~ ?x |-  _ => revert h; generalize x
     end; intros t' h.
     unfold denote_main in *.
*)


(*
     simpl in IHs2.

     simpl bind.
     intro p; subst p.
     rewrite bind_bind.
     denote_main (compile (Seq s1 s2) b) imports =
     denote_main (compile s1 ?) ?;; denote_main (compile s2 b) imports
     rewrite <- IHs2.
     unfold denote_main. simpl.
     rewrite bind_bind.
     rewrite fmap_block_map, map_bind; simpl.
     match goal with
     | |- ITree.bind _ ?x ~~ ITree.bind _ ?y => set (goal1 := x); set (goal2 := y)
     end.
     (main (compile s2 b))).
     specialize (IHs1 _ (main (compile s2 b))).
     unfold denote_main in IHs1; simpl in IHs1.
     eapply eutt_bind.
     assert (
(fun next : option (label (compile s1 (main (compile s2 b))) + label (compile s2 b) + L) =>
     match next with
     | Some (inl next0) =>
         denote_program L
           {|
           label := label (compile s1 (main (compile s2 b))) + label (compile s2 b);
           main := fmap_block
                     (fun x : label (compile s1 (main (compile s2 b))) + (label (compile s2 b) + L) =>
                      match x with
                      | inl x0 => inl (inl x0)
                      | inr (inl x0) => inl (inr x0)
                      | inr (inr x0) => inr x0
                      end) (main (compile s1 (main (compile s2 b))));
           blocks := fun x : label (compile s1 (main (compile s2 b))) + label (compile s2 b) =>
                     match x with
                     | inl x0 =>
                         fmap_block
                           (fun x1 : label (compile s1 (main (compile s2 b))) + (label (compile s2 b) + L) =>
                            match x1 with
                            | inl x2 => inl (inl x2)
                            | inr (inl x2) => inl (inr x2)
                            | inr (inr x2) => inr x2
                            end) (blocks (compile s1 (main (compile s2 b))) x0)
                     | inr x0 =>
                         fmap_block
                           (fun x1 : label (compile s2 b) + L =>
                            match x1 with
                            | inl x2 => inl (inr x2)
                            | inr x2 => inr x2
                            end) (blocks (compile s2 b) x0)
                     end |} imports next0
     | Some (inr next0) => imports next0
     | None => Ret tt
     end) = 2).


    - simpl.
      unfold denote_main. 
      simpl denoteStmt.
      simpl main; simpl compile_assign.
      
    -
      unfold denote_main. simpl in *.
      simpl.

    intros.
    unfold denote_main.
    induction s; intros L b imports l; simpl in * |-.
    - elim l.
    - simpl denoteStmt.
      

      simpl compile.

*)
Admitted.

    Theorem compile_correct:
    forall s, @denote_main _ _ _ Empty_set (compile s (bbb Bhalt)) (fun x => match x with end) ~~ denoteStmt s.
  Proof.
(*    intros stmt.
    unfold denote_main.
    transitivity (@denoteStmt (Locals +' Memory) _ stmt;; Ret tt).
    {
      eapply eutt_bind; [reflexivity | intros []].
      simpl.
*)

  Admitted. 

End Correctness.


(*
l: x = phi(l1: a, l2: b) ; ...
l1: ... ; jmp l
l2: ... ; jmp l

l: [x]
   ....
l1: ...; jmp[a]
l2: ...; jmp[b]
*)