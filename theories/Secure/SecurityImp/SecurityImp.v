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
     Events.StateFacts.

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

Variant sensitivity : Set := Public | Private.

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| Output (s : sensitivity) (e : expr)
.


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


Definition privacy_map : Set := var -> sensitivity.

Variant stateE : Type -> Type :=
  | Get (x : var) : stateE value
  | Put (x : var) (v : value) : stateE unit.

Variant IOE : Type -> Type :=
  | LabelledPrint : sensitivity -> value -> IOE unit.

Fixpoint denote_expr (e : expr) : itree (stateE +' IOE) value := 
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

Fixpoint denote_stmt (s : stmt) : itree (stateE +' IOE) unit :=
  match s with
  | Assign x e => y <- denote_expr e;; trigger (Put x y)
  | Seq s1 s2 => denote_stmt s1 ;; denote_stmt s2
  | If e c1 c2 => b <- denote_expr e;;
                 if (is_true b) 
                 then denote_stmt c1
                 else denote_stmt c2
  | Skip => Ret tt
  | Output s e => v <- denote_expr e;; trigger (LabelledPrint s v)
  | While b c => while (
                    b <- denote_expr b;;
                    if (is_true b)
                    then denote_stmt c;; Ret (inl tt)
                    else Ret (inr tt) )
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

Definition priv_imp (p : privacy_map) (A : Type) (e : (stateE +' IOE) A ) : sensitivity :=
  match e with
  | inl1 (Get x) => p x
  | inl1 (Put x _) => p x
  | inr1 (LabelledPrint s _ ) => s 
  end.




(*
Variant SecurityImpState : Type -> Type :=
  | GetPrivVar (x : var) : SecurityImpState value
  | SetPrivVar (x : var) (v : value) : SecurityImpState unit
  | GetPubVar (x : var) : SecurityImpState value
  | SetPubVar (x : var) (v : value) : SecurityImpState unit
  | PubPrint  (v : value) : SecurityImpState unit 
  | PrivPrint (v : value) : SecurityImpState unit.
*)


(* 
denote : stmt -> privacy_map -> itree Securityimpstate unit

interp ( ... ) :itree Securityimpstate unit ->
                S -> S -> itree (SecureIO) (S * S * unit)



itrees   ≈ eutt (eq up to tau)

monad  (StateT (itree E) ) equiv (m1 m2 : StateT (itree E) R)  forall s1 s2, state_equiv s1 s2 -> m1 s1 ≈ m2 s2




itrees   eqit_secure (with RR respecting privacy)


monad (...)    forall s1 s2, low_equiv s1 s2 -> eqit_secure ... low_equiv (m1 s1) (m2 s2)
*)
