(* Simple semantics for the Imp programming language (with function calls)
 * using interaction trees.
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.

From ITree Require Import
     Basics
     ITree.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(* representation of variables *)
Definition var : Set := string.

(* representation of expressions *)
Inductive expr : Set :=
| Var (_ : var)
| Lit (_ : nat)
| Plus (_ _ : expr).

Definition value : Type := nat.

Definition is_true (v : value) : bool :=
  match v with
  | 0   => false
  | S _ => true
  end.

(* representation of statements *)
Inductive stmt : Set :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
(* For Calls ********
| Call   (ls : list var) (f : string) (args : list expr)
*)
.

(* the "effect" to track local variables *)
Inductive Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

(* the "effect" to track errors *)
Inductive Error : Type -> Type :=
| RuntimeError (_ : string) : Error Empty_set.

Definition error {eff} `{Error -< eff} (msg : string) {a} : itree eff a :=
  x <- lift (RuntimeError msg) ;;
  match x : Empty_set with end.


Definition ImpEff : Type -> Type := Locals +' Error.

(* For Calls *********
Inductive External : Type -> Type :=
| CallExternal (name : string) (ls : list value) : External (list value).

Definition ImpEff : Type -> Type := Locals +' (External +' Error).
*)

Section assignMany.
  Context {eff : Type -> Type}.
  Context {HasLocals : Locals -< eff}.
  Context {HasError : Error -< eff}.

  Fixpoint assignMany (ls : list var) (vs : list value) : itree eff unit :=
    match ls , vs with
    | nil , nil => ret tt
    | x :: xs , v :: vs => lift (SetVar x v) ;; assignMany xs vs
    | nil , _ :: _ => lift (RuntimeError "insufficient binders") ;; ret tt
    | _ :: _ , nil => lift (RuntimeError "too many binders") ;; ret tt
    end.
End assignMany.

(* The meaning of an expression *)
Fixpoint denoteExpr (e : expr) : itree ImpEff value :=
  match e with
  | Var v => lift (GetVar v)
  | Lit n => ret n
  | Plus a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (l + r)
  end.

Definition while {eff} (t : itree eff bool) : itree eff unit :=
  rec (fun _ : unit =>
    continue <- translate (fun _ x => inr1 x) _ t ;;
    if continue : bool then lift (Call tt) else Monad.ret tt) tt.

(* the meaning of a statement *)
Fixpoint denoteStmt (s : stmt) : itree ImpEff unit :=
  match s with
  | Assign x e =>
    v <- denoteExpr e ;;
    lift (SetVar x v)
  | Seq a b =>
    denoteStmt a ;; denoteStmt b
  | If i t e =>
    v <- denoteExpr i ;;
    if is_true v then denoteStmt t else denoteStmt e
  | While t b =>
    while (v <- denoteExpr t ;;
	   if is_true v
           then denoteStmt b ;; ret true
           else ret false)
  | Skip => ret tt
(* For Calls ********
  | Call xs f args =>
    vals <- mapT denoteExpr args ;;
    results <- lift (CallExternal f vals) ;;
    assignMany xs results
*)
  end.

(* some simple examples *)
Eval simpl in
    denoteStmt (Seq (Assign "x" (Lit 1))
                    (Assign "y" (Var "x"))).

Eval simpl in
    denoteStmt (Seq (Assign "x" (Lit 1))
                    (While (Var "x") (Assign "x" (Var "x")))).

(* Two interpretations of local variable environments
 *)
Module ImplicitInit.
  Import ITree.Basics.Monads.

  (* Interpretation of the `Locals` effects using total maps, i.e.
   * variables are implicitly initialized to some default value.
   * This mirrors the semantics of Imp.
   *)
  Definition evalLocals {eff} : Locals ~> stateT (var -> value) (itree eff) :=
    fun _ e st =>
      match e with
      | GetVar x =>
        ret (st, st x)
      | SetVar x v =>
        ret (fun x' => if string_dec x x' then v else st x', tt)
      end.

  Definition init : var -> value :=
    fun _ => 0.

End ImplicitInit.


Module ExplicitInit.
  Import ITree.Basics.Monads.

  Definition env := list (var * value).

  Fixpoint lookup (e : env) (v : string) : option value :=
    match e with
    | nil => None
    | (var,val) :: es =>
      if string_dec var v then Some val else lookup es v
    end.

  Fixpoint set (v : string) (val : value) (e : env) : env :=
    match e with
    | nil => (v, val) :: nil
    | (var,val') :: es =>
      if string_dec var v then (var, val) :: es else (var, val') :: set v val es
    end.

  (* Interpretation of the `Locals` effects using partial maps, i.e.
   * variables must be explicitly initialized.
   * This mirrors the semantics of C.
   *)
  Definition evalLocals {eff} `{Error -< eff}: Locals ~> stateT env (itree eff) :=
    fun _ e st =>
      match e with
      | GetVar x =>
        match lookup st x with
        | None =>
          error ("variable `" ++ x ++ "` not defined")
        | Some v => ret (st, v)
        end
      | SetVar x v =>
        ret (set x v st, tt)
      end.

  Definition init : env := nil.

End ExplicitInit.

Definition evalLocals stmt :=
  interp_state (into_state ExplicitInit.evalLocals) _ (denoteStmt stmt) ExplicitInit.init.

(* For Calls ************
Definition evalLocals stmt :=
  run_state ExplicitInit.evalLocals (denoteStmt stmt) ExplicitInit.init.
*)

(* some simple examples *)
Eval simpl in
    let stmt := Seq (Assign "x" (Lit 1))
                    (Assign "y" (Var "x")) in
    evalLocals stmt.

Eval simpl in
    let stmt := Seq (Assign "x" (Lit 1))
                    (While (Var "x") (Assign "x" (Var "x"))) in
    evalLocals stmt.

(* For Calls ************
Eval simpl in
    let stmt := Seq (Call ("x" :: nil) "print" (Lit 1 :: nil))
                    (Assign "y" (Var "x")) in
    simplify 1 (evalLocals stmt).

Module ToTrace.

  Definition Event : Type := (string * list value * list value)%type.

  Section with_oracle.
    (* we could add state without much difficulty *)
    Variable oracle : string -> list value -> list value.

    Definition evalExternals {eff}
    : eff_hom_s (list Event) External eff :=
      fun _ e st =>
        match e with
        | CallExternal f ls =>
          let res := oracle f ls in
          ret (st ++ (f, ls, res) :: nil, res)%list
        end.
  End with_oracle.

End ToTrace.

Definition evalTrace {eff} {t} (oracle : _)
           (it : ITree.itree (External +' eff) t)
: ITree.itree eff (list ToTrace.Event * t) :=
  run_state (ToTrace.evalExternals oracle) it nil.

Eval simpl in
    let stmt := Seq (Call ("x" :: nil) "print" (Lit 1 :: nil))
                    (Assign "y" (Var "x")) in
    fun oracle =>
    simplify 2 (evalTrace oracle (evalLocals stmt)).
*)
