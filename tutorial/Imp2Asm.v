(** * Compilation of Imp to Asm *)

(** We are now ready to define our compiler.
    The compilation of [expr]essions is of no interest.
    The interesting part is in the structure of the
    compilation of instructions: we build higher level
    [asm] combinators from the primitive ones defined
    in [AsmCombinators.v]. Each of these combinator
    transcribes a control flow construct of the _Imp_
    language as a linking operation over _Asm_.
    Their correctness will be shown in the same style as
    the elementary combinators, isolating the control
    flow reasoning.
    Additionnaly, although naturally their choice here
    is tied to _Imp_, they are fairly generic constructs
    and could therefore be reused.
*)

(* begin hide *)
Require Import Imp Asm Utils_tutorial AsmCombinators.

Require Import Psatz.

From Coq Require Import
     String
     Morphisms
     Setoid
     Decimal
     Numbers.DecimalString
     Vectors.Fin
     ZArith
     RelationClasses.

From ITree Require Import
     ITree.

Import ListNotations.
Open Scope string_scope.
(* end hide *)

(* ================================================================= *)
(** ** Compilation of expressions *)

Section compile_assign.

  (** We use a simple scheme to ensure disjointness of user variables from local
  ones introduced by the compiler: the former ones get prefix by "temp_", the latter
  ones by "local_". *)

  Definition gen_tmp (n: nat): string :=
    "temp_" ++ string_of_nat n.

  Definition varOf (s : var) : var := "local_" ++ s.

  (** Expressions are compiled straightforwardly.
      The argument [l] is the number of local variables already introduced to compile
      the expression, and is used for the name of the next one.
      The result of the computation [compile_expr l e] always ends up stored in [gen_tmp l]. 
   *)
  Fixpoint compile_expr (l: nat) (e: expr): list instr :=
    match e with
    | Var x => [Imov (gen_tmp l) (Ovar (varOf x))]
    | Lit n => [Imov (gen_tmp l) (Oimm n)]
    | Plus e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Iadd (gen_tmp l) (gen_tmp l) (Ovar (gen_tmp (1 + l)))]
    | Minus e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Isub (gen_tmp l) (gen_tmp l) (Ovar (gen_tmp (1 + l)))]
    | Mult e1 e2 =>
      let instrs1 := compile_expr l e1 in
      let instrs2 := compile_expr (1 + l) e2 in
      instrs1 ++ instrs2 ++ [Imul (gen_tmp l) (gen_tmp l) (Ovar (gen_tmp (1 + l)))]
      end.

  (** Compiles the expression and then move the result (in [gen_tmp 0]) to the mangled variable. *)
  Definition compile_assign (x: Imp.var) (e: expr): list instr :=
    let instrs := compile_expr 0 e in
    instrs ++ [Imov (varOf x) (Ovar (gen_tmp 0))].

End compile_assign.

(* ================================================================= *)
(** ** Control flow combinators *)


(** Sequencing of blocks: the program [seq_asm ab bc] links the
    exit points of [ab] with the entry points of [bc].
    
[[
           B
   A---ab-----bc---C
]]

   ... can be implemented using just [app_asm], [relabel_asm] and [link_asm].

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
Definition seq_asm {A B C} (ab : asm A B) (bc : asm B C): asm A C :=
  link_asm (relabel_asm swap (id_ _) (app_asm ab bc)).


(** Location of temporary for [if]. *)
Definition tmp_if := gen_tmp 0.

(** Turns the list of instructions resulting from the conditional
    expression of a _if_ to a block with two exit points.
 *)
Definition cond_asm (e : list instr) : asm 1 2 :=
  raw_asm_block (after e (Bbrz tmp_if F1 (FS F1))).

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
   The loop is then closed with [link_asm] by matching the jump from the
   true branch to the entry point.

[while_asm e p]
[[
>>>>>>> origin/master
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
  link_asm (relabel_asm (id_ _) merge
    (app_asm (if_asm e
                (relabel_asm id inl_ p)
                (pure_asm inr_))
            (pure_asm inl_))).

(** Equipped with our combinators, the compiler writes itself
    by induction on the structure of the statement.
*)
Fixpoint compile (s : stmt) {struct s} : asm 1 1 :=
  match s with
  | Skip => id_asm
  | Assign x e => raw_asm_block (after (compile_assign x e) (Bjmp F1))
  | Seq l r => seq_asm (compile l) (compile r)
  | If e l r => if_asm (compile_expr 0 e) (compile l) (compile r)
  | While e b => while_asm (compile_expr 0 e) (compile b)
  end.

(** We now consider its proof of correctness in [Imp2AsmCorrectness.v]. *)




