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
     Events.State
     Events.StateFacts
     Events.Exception
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

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
| Output (e : expr)
(* exceptions *)
| Raise.

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: nat -> expr := Lit.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: nat >-> expr.

  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Bind Scope stmt_scope with stmt.

  Notation "x '←' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';;;' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';;;' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'IF' i 'THEN' t 'ELSE' e 'FI'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'IF'  i '/' '[' 'THEN'  t  ']' '/' '[' 'ELSE'  e ']' 'FI' ']'").

  Notation "'WHILE' t 'DO' b" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' 'WHILE'  t  'DO' '/' '[v' b  ']' ']'").
(*
  Notation "'PRINT' e 'AT' s" := 
    (Write s e)
      (at level)
            *)

End ImpNotations.


Variant stateE : Type -> Type :=
  | Get (x : var) : stateE value
  | Put (x : var) (v : value) : stateE unit.

Variant IOE : Type -> Type :=
  | Print : value -> IOE unit.

Definition impExcE : Type -> Type := exceptE unit.

Fixpoint denote_expr (e : expr) : itree (impExcE +' stateE +' IOE) value := 
  match e with
  | Var x => trigger (Get x)
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

Fixpoint denote_stmt (s : stmt) : itree (impExcE +' stateE +' IOE) unit :=
  match s with
  | Assign x e => y <- denote_expr e;; trigger (Put x y)
  | Seq s1 s2 => denote_stmt s1 ;; denote_stmt s2
  | If e c1 c2 => b <- denote_expr e;;
                 if (is_true b) 
                 then denote_stmt c1
                 else denote_stmt c2
  | Skip => Ret tt
  | Output e => v <- denote_expr e;; trigger (Print v)
  | While b c => while (
                    b <- denote_expr b;;
                    if (is_true b)
                    then denote_stmt c;; Ret (inl tt)
                    else Ret (inr tt) )
  | Raise => trigger (Throw tt);; Ret tt
   end.

(* very inefficient, but not sure I really care about extraction so whatever *)
Definition map : Type := var -> value.

Definition get (x : var) (s : map) := s x.
Definition update (x : var) (v : value) (s : map) :=
  fun y => if x =? y then v else s y .

Definition handleState {E} (A : Type) (e : stateE A) : stateT map (itree E ) A :=
  match e with
  | Get x => fun s => Ret (s, get x s)
  | Put x v => fun s => Ret (update x v s, tt) end.


Definition handle_case {E1 E2 : Type -> Type} {M : Type -> Type} (hl : E1 ~> M) (hr : E2 ~> M) : (E1 +' E2) ~> M :=
  fun _ e => match e with
          | inl1 el => hl _ el
          | inr1 er => hr _ er end.

Definition handle_state_io : forall A, (stateE +' IOE) A -> stateT map (itree (impExcE +' IOE)) A :=
  fun _ e => match e with
          | inl1 el => handleState _ el
          | inr1 er => fun s => r <- ITree.trigger (inr1 er);; Ret (s, r) end. 

Definition handle_imp : forall A, (impExcE +' stateE +' IOE) A -> stateT map (itree (impExcE +' IOE) ) A :=
  fun _ e => match e with
          | inl1 el => fun s => r <- ITree.trigger (inl1 el);; Ret (s, r)
          | inr1 er => handle_state_io _ er end.

Definition interp_imp {R} (t : itree (impExcE +' stateE +' IOE) R ) : stateT map (itree (impExcE +' IOE)) R :=
  interp_state handle_imp t. 

Hint Unfold interp_imp.
Hint Unfold handle_state_io.
Hint Unfold handle_imp.
