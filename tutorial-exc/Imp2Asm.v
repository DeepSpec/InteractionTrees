(** * Compilation of Imp to Asm *)

(** We are now ready to define our compiler.
    The compilation of [expr]essions is of little interest.
    The interesting part is in the structure of the
    compilation of instructions: we build higher level
    [asm] combinators from the primitive ones defined
    in [AsmCombinators.v]. Each of these combinator
    transcribes a control flow construct of the _Imp_
    language as a linking operation over _Asm_.
    Their correctness will be shown in the same style as
    the elementary combinators, isolating the control
    flow reasoning.
    Additionally, although naturally their choice here
    is tied to _Imp_, they are fairly generic constructs
    and could therefore be reused.
*)

(* begin hide *)

Require Import Psatz.

From Coq Require Import
     List
     String
     Morphisms
     Setoid
     Decimal
     Numbers.DecimalString
     ZArith
     RelationClasses.

From ITree Require Import
     ITree
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityAsm
     Secure.SecurityImpExc.SecurityAsmCombinators
     Secure.SecurityImp.Fin
     Secure.SecurityImp.Utils_tutorial
.

Import ListNotations.
Open Scope string_scope.
Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

(* ================================================================= *)
(** ** Compilation of expressions *)

Section compile_assign.

  (** Expressions are compiled straightforwardly.
      The argument [l] is the number of registers already introduced to compile
      the expression, and is used for the name of the next one.
      The result of the computation [compile_expr l e] always ends up stored in [l].
   *)
  Fixpoint compile_expr (l:reg) (e: expr): list instr :=
    match e with
    | Var x => [Iload l x]
    | Lit n => [Imov l (Oimm n)]
    | Plus e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Iadd l l (Oreg (1 + l))]
    | Minus e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Isub l l (Oreg (1 + l))]
    | Mult e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Imul l l (Oreg (1 + l))]
      end.

  (** Compiles the expression and then moves the result (in register [0]) to address
      [x].  Note: here we assume a one-to-one mapping of _Imp_ global variable names
      and _Asm_ addresses.
  *)
  Definition compile_assign (x: var) (e: expr): list instr :=
    let instrs := compile_expr 0 e in
    instrs ++ [Istore x (Oreg 0)].

  Definition compile_output (e : expr) : list instr :=
    let instrs := compile_expr 0 e in 
    instrs ++  [IOutput 0].

End compile_assign.

(* ================================================================= *)
(** ** Control flow combinators *)


(** Sequencing of blocks: the program [seq_asm ab bc] links the
    exit points of [ab] with the entry points of [bc].

[[
           B
   A---ab-----bc---C
]]

   ... can be implemented using just [app_asm], [relabel_asm] and [loop_asm].

  Indeed, [app_asm ab bc] can be visualized as:
[[
  A---ab---B
  B---bc---C
]]
 i.e. a [asm (A + B) (B + C)]. To link them, we need first to swap the entry points.

We obtain the following diagram:
[seq_asm ab bc]
[[
       +------+
       |      |
   A------ab--+B
       |
      B+--bc------C
]]

Which translates to:
 *)
Definition seq_asm {A B C} (ab : asm A B) (bc : asm B C)
  : asm A C :=
  loop_asm (relabel_asm swap (id_ _) (app_asm ab bc)).

Section seq_asm_exc.
Context {A B C D : nat}.
Context (ab : asm A (B + C)).
Context (bd : asm B (D + C)).
(* so what I need to do is get this to the form some swapping should get this the rest of the 
   way to the other *)
Definition comb : asm (A + B) ((B + C) + (D + C)) := app_asm ab bd.



Definition swap_and_merge : CategorySub.sub Fun fin (C + (D + C) ) (D + C) := 
  cat (cat ( cat (bimap (id_ _) (swap) ) assoc_l) (bimap merge (id_ _) )) swap.

Definition expose_linking_labels : asm (B + A) (B + (D + C) )  := relabel_asm swap (cat (cat assoc_r (id_ _)) (bimap (id_ _ ) swap_and_merge) ) comb.

Definition seq_asm_exc : asm A (D + C) := loop_asm expose_linking_labels.

End seq_asm_exc.

(** Location of temporary for [if]. *)
Definition tmp_if := 0.

(** Turns the list of instructions resulting from the conditional
    expression of a _if_ to a block with two exit points.
 *)
Definition cond_asm (e : list instr) : asm 1 2 :=
  raw_asm_block (after e (Bbrz tmp_if (fS f0) f0)).


(** Conditional branch of blocks.
    The program [if_asm e tp fp] creates a block out of [e] jumping
    either left or right.
    Using [seq_asm], this block is sequenced with the vertical
    composition [app_asm] of [tp] and [fp].
    Remains one mismatch: [app_asm] duplicates the domain of outputs,
    although they share the same. We hence use [relabel_asm] to collapse
    them together.

 [if_asm e tp fp]
[[
           true
       /ee-------tp---A\
    1--                 --A
       \ee-------fp---A/
           false
]]
 *)
Definition if_asm {A}
           (e : list instr) (tp : asm 1 A) (fp : asm 1 A) :
  asm 1 A :=
  seq_asm (cond_asm e)
          (relabel_asm (id_ _) merge (app_asm tp fp)).

  

(* Conditional looping of blocks.
   The program [while_asm e p] composes vertically two programs:
   an [if_asm] construct with [p] followed by a jump on the true branch,
   and a unique jump on the false branch.
   The loop is then closed with [loop_asm] by matching the jump from the
   true branch to the entry point.

[while_asm e p]
[[
      +-------------+
      |             |
      |    true     |
      |  e-------p--+
  1---+--e--------------1
           false
]]
*)
Definition while_asm (e : list instr) (p : asm 1 1) :
  asm 1 1 :=
  loop_asm (relabel_asm (id_ _) merge
    (app_asm (if_asm e
                (relabel_asm (id_ _) inl_ p)
                (pure_asm inr_))
            (pure_asm inl_))).




Definition pure_ret_asm : asm 1 2 :=
  pure_asm (fun _ => f0).

Definition pure_exc_asm : asm 1 2 :=
  pure_asm (fun _ => fS (f0)).


Section while_asm_exc.
  Context (e : list instr).
  Context (p : asm 1 (1 + 1) ).

  (* part of the problem is I am thinking about it wrong, because only a success signal in the body loop  gets fed back into the loop, either *)
  (*Definition direct_output_while_exc : asm (1 + 2) (1 + (1 + 2) ) := app_asm (pure_asm (id_ _)) (pure_asm inr_). *)

  Definition direct_output_while_exc : asm 1 (1 + (1 + 1)) :=
    relabel_asm (id_ _) (bimap inl_ inr_) p.
 
  Definition while_asm_exc : asm 1 2 :=
    loop_asm (relabel_asm (id_ _) merge (app_asm 
                                           (if_asm e direct_output_while_exc (pure_asm (fun _ => fS (f0)) )) 
                                           (pure_asm inl_))).

(*
  I should refactor these to just use local let definitions
*)

End while_asm_exc.
(* probably can refact seq_asm_exc to be simpler *)


Definition trycatch_asm (p : asm 1 (1 + (1 + 1) ) ) (c : asm 1 2) : asm 1 2 :=
  seq_asm (relabel_asm (id_ _) (bimap (id_ _) merge ) p)
   (relabel_asm (id_ _ ) merge (app_asm pure_ret_asm c)).


Definition raise_asm : asm 1 1:=
  {| internal := 0; code := fun _ => bbb BRaise |}.

(*
Definition while_asm_exc (e : list instr) (p : asm 1 2) : asm 1 2 :=
  loop_asm
                                                              
*)
(** Equipped with our combinators, the compiler writes itself
    by induction on the structure of the statement.
*)
Fixpoint compile_stmt (s : stmt) {struct s} : asm 1 (1 + 1) :=
  match s with
  | Skip       => pure_ret_asm
  | Assign x e => raw_asm_block (after (compile_assign x e) (Bjmp f0))
  | Output e => raw_asm_block (after (compile_output e) (Bjmp f0) )
  | Seq l r    => seq_asm_exc (compile_stmt l) (compile_stmt r)
  | If e l r   => if_asm (compile_expr 0 e) (compile_stmt l) (compile_stmt r)
  | Raise => pure_exc_asm
  | While e s => while_asm_exc (compile_expr 0 e) (compile_stmt s)
  (* | TryCatch t c => trycatch_asm (compile_stmt t) (compile_stmt c) *)
  end.

Definition compile (s : stmt) : asm 1 1 :=
  seq_asm (compile_stmt s)
          (relabel_asm (id_ _) (fun _ => f0) (app_asm id_asm raise_asm)).

(** We now consider its proof of correctness in [Imp2AsmCorrectness.v]. *)
