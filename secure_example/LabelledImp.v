From Coq Require Import String.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
     Events.Exception
.

From SecureExample Require Import
     Lattice.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section LabelledImp.

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

Context (Labels : Lattice).

Notation label := (@T Labels).

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
.



Definition privacy_map : Type := var -> label.

Variant stateE : Type -> Type :=
  | Get (x : var) : stateE value
  | Put (x : var) (v : value) : stateE unit.

Variant IOE : Type -> Type :=
  | LabelledPrint : label -> value -> IOE unit.

Definition impExcE : Type -> Type := exceptE label.

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
  | Output s e => v <- denote_expr e;; trigger (LabelledPrint s v)
  | While b c => while (
                    b <- denote_expr b;;
                    if (is_true b)
                    then denote_stmt c;; Ret (inl tt)
                    else Ret (inr tt) )
  | Raise s => trigger (Throw s);; Ret tt
  | TryCatch t c => try_catch (denote_stmt t) (fun _ => denote_stmt c)
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


Definition priv_imp (p : privacy_map) (A : Type) (e : (impExcE +' stateE +' IOE) A ) : label :=
  match e with
  | inl1 (Throw s) => s
  | inr1 (inl1 (Get x)) => p x
  | inr1 (inl1 (Put x _)) => p x
  | inr1 (inr1 (LabelledPrint s _ )) => s
  end.

End LabelledImp.

Arguments Skip {Labels}.
Arguments Output {Labels}.
Arguments While {Labels}.
Arguments Raise {Labels}.
Arguments TryCatch {Labels}.
Arguments Assign {Labels}.
Arguments Seq {Labels}.
Arguments If {Labels}.
