From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
     Events.Exception
.


From SecureExample Require Import 
     Lattice
     LabelledAsm
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section LabelledImp.

Context (Labels : Lattice).

Notation label := (@T Labels).

Definition var : Set := string.

Definition value : Type := nat.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| Output (s : label) (e : expr)
(* exceptions *)
| Raise (s : label)
| TryCatch (t c : stmt)
(* Inline *)
| AsmInline (p : asm Labels 1 1)
.

Variant ClearRegs : Type -> Type :=
  | Clear : ClearRegs unit.

Section LabelledImpInlineSemantics.
  Context {E : Type -> Type}.
  Context {HasReg : Reg -< E}.
  (* thought I might need this, but without it things get simpler *)
  (* Context {HasClearRegs : ClearRegs -< E}. *)
  Context {HasMemory : Memory -< E}.
  Context {HasIOE : LabelledImp.IOE Labels -< E}.

  Notation impExcE := (LabelledImp.impExcE Labels ).

  Notation privacy_map := LabelledImp.privacy_map.

  


  Fixpoint denote_expr (e : expr) : itree (impExcE +' E) value := 
    match e with
    | Var x => trigger (Load x)
    | Lit v => Ret v
    | Plus e1 e2 => x <- denote_expr e1;;
                   y <- denote_expr e2;;
                   Ret (x + y)
    | Minus e1 e2 => x <- denote_expr e1;;
                    y <- denote_expr e2;;
                    Ret (x - y)
    | Mult e1 e2 => x <- denote_expr e1;;
                   y <- denote_expr e2;;
                   Ret (x * y) end.


  Definition is_true (v : value) : bool :=
    Nat.ltb 0 v.

  Definition while {E} (t : itree E (unit + unit) ) : itree E unit :=
    ITree.iter (fun _ => t) tt.

  
  Definition denote_asm_inline {A B} (p : asm _ A B) : Fin.fin A -> itree (impExcE +' E) (Fin.fin B) :=
    @denote_asm _ (impExcE +' E) _ _ _ _ A B p.

  Fixpoint denote_stmt (s : stmt) : itree (impExcE +' E) unit :=
    match s with
    | Assign x e => y <- denote_expr e;; trigger (HasMemory _ (Store x y))
    | Seq s1 s2 => denote_stmt s1 ;; denote_stmt s2
    | If e c1 c2 => b <- denote_expr e;;
                   if (is_true b) 
                   then denote_stmt c1
                   else denote_stmt c2
    | Skip => Ret tt
    | Output s e => v <- denote_expr e;; trigger (inr1 (HasIOE _ (LabelledImp.LabelledPrint _ s v)) )
    | While b c => while (
                      b <- denote_expr b;;
                      if (is_true b)
                      then denote_stmt c;; Ret (inl tt)
                      else Ret (inr tt) )
    | Raise s => trigger (Throw _ s);; Ret tt
    | TryCatch t c => try_catch (denote_stmt t) (fun _ => denote_stmt c)
    | AsmInline p => denote_asm_inline p Fin.f0;; Ret tt
    end.

(* very inefficient, but not sure I really care about extraction so whatever *)
Definition map : Type := var -> value.


End LabelledImpInlineSemantics.

End LabelledImp.

Definition interp_imp_inline {E1 E2 : Type -> Type} {A : Type} : 
  itree (E1 +' Reg +' Memory +' E2) A ->
  stateT (registers * memory) (itree (E1 +' E2)) A := @interp_asm E1 E2 A.
