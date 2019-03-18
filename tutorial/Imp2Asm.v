Require Import Imp Asm Utils_tutorial AsmCombinators.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     Setoid
     Decimal
     Numbers.DecimalString
     Vectors.Fin
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
Definition cond_asm (e : list instr) : asm 1 2 :=
  raw_asm_block (after e (Bbrz tmp_if F1 (FS F1))).

(** [if_asm e tp fp]
[[
           true
        ee-------tp---C
    1---ee-------fp---C
           false
]]
 *)
Definition if_asm {A}
           (e : list instr) (tp : asm 1 A) (fp : asm 1 A) :
  asm 1 A :=
  seq_asm (cond_asm e)
          (relabel_asm (id_ _) merge (app_asm tp fp)).

(* [while_asm e p]
/[[
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

Fixpoint compile (s : stmt) {struct s} : asm 1 1 :=
  match s with
  | Skip => id_asm
  | Assign x e => raw_asm_block (after (compile_assign x e) (Bjmp F1))
  | Seq l r => seq_asm (compile l) (compile r)
  | If e l r => if_asm (compile_expr 0 e) (compile l) (compile r)
  | While e b => while_asm (compile_expr 0 e) (compile b)
  end.
