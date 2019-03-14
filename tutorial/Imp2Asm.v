Require Import Imp Asm Utils_tutorial AsmCombinators.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     Setoid
     Decimal
     Numbers.DecimalString
     ZArith
     RelationClasses.

From ITree Require Import
     Basics.Category
     Basics.Function
     Effects.Env
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
    "temp_" ++ string_of_nat n.

  Definition varOf (s : var) : var := "local_" ++ s.

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

  Definition compile_assign (x: Imp.var) (e: expr): list instr :=
    let instrs := compile_expr 0 e in
    instrs ++ [Imov (varOf x) (Ovar (gen_tmp 0))].

End compile_assign.

(** Sequencing of blocks: the program [seq_asm ab bc] links the
    exit points of [ab] with the entry points of [bc].

[[
           B
   A---ab-----bc---C
]]

   ... can be implemented using just [app_asm] and [link_asm].

[[
       +------+
       |      |
   A------ab--+B
       |
      B+--bc------C
]]
*)
Definition seq_asm {A B C} (ab : asm A B) (bc : asm B C): asm A C :=
  link_asm (relabel_asm swap (id_ _) (app_asm ab bc)).

(* Location of temporary for [if]. *)
Definition tmp_if := gen_tmp 0.

(* Conditional *)
Definition cond_asm (e : list instr) : asm unit (unit + unit) :=
  raw_asm_block (after e (Bbrz tmp_if (inr tt) (inl tt))).

(** [if_asm e tp fp]
[[
           true
        ee-------tp---C
    1---ee-------fp---C
           false
]]
 *)
Definition if_asm {A}
           (e : list instr) (tp : asm unit A) (fp : asm unit A) :
  asm unit A :=
  seq_asm (cond_asm e)
          (relabel_asm (id_ _) merge (app_asm tp fp)).

(* [while_asm e p]
[[
      +-------------+
      |             |
      |    true     |
      |  e-------p--+
  1---+--e--------------1
           false
]]
*)
Definition while_asm (e : list instr) (p : asm unit unit) :
  asm unit unit :=
  link_asm (relabel_asm (id_ _) merge
    (app_asm (if_asm e
                (relabel_asm id inl p)
                (pure_asm inr))
            (pure_asm inl))).

Fixpoint compile (s : stmt) {struct s} : asm unit unit :=
  match s with
  | Skip => id_asm
  | Assign x e => raw_asm_block (after (compile_assign x e) (Bjmp tt))
  | Seq l r => seq_asm (compile l) (compile r)
  | If e l r => if_asm (compile_expr 0 e) (compile l) (compile r)
  | While e b => while_asm (compile_expr 0 e) (compile b)
  end.
