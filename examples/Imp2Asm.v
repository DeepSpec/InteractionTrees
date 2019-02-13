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
 If the source level is non-deterministic, for instance order of add, the compiler could pick an order and the correctness would be a refinement.
     How to define it? In term of interpreters?
     In term of oracle
   *)

  (* Add a print effect? *)

  (*
 Change languages to map two notions of state at the source down to a single one at the target?
 Make the keys of the second env monad as the sum of the two initial ones.
   *)

  (* Missing a Locals -< ImpEff instance, got me confused, I'll get back to it later. *)

  Lemma compile_correct_program:
    forall s L b imports l,
      @denote_program _ _ _ L (compile s b) imports l ~~ (denoteStmt s;; denote_block _ b;; Ret tt).
    Admitted.

  Theorem compile_correct:
    forall s, @denote_main _ _ _ Empty_set (compile s (bbb Bhalt)) (fun x => match x with end) ~~ denoteStmt s.
  Proof.
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