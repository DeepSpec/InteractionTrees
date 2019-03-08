(* Simple semantics for the Imp programming language (with function calls)
 * using interaction trees.
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.String.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.

From ITree Require Import
     Basics.Basics
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
.

Module ImpNotations.

  Notation "x '←' e" :=
    (Assign x e) (at level 60, e at level 50).

  Notation "a ;;; b" :=
    (Seq a b)
      (at level 80, right associativity,
       format
         "'[v ' a  ';;;' '/' '[' b ']' ']'"
      ).

  Notation "'IF' i 'THEN' t 'ELSE' e" :=
    (If i t e)
      (at level 200,
       right associativity,
       format
         "'[v ' 'IF'  i '/' '[' 'THEN'  t  ']' '/' '[' 'ELSE'  e ']' ']'").

  Notation "'WHILE' t 'DO' b" :=
    (While t b)
      (at level 200,
       right associativity,
       format
         "'[v ' 'WHILE'  t '/' '[' 'DO'  b  ']' ']'").

  Coercion Lit: nat >-> expr.
  Definition Var_coerce: string -> expr := Var.
  Coercion Var_coerce: string >-> expr.

End ImpNotations.

Import ImpNotations.

(* the "effect" to track local variables *)
Inductive Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasLocals : Locals -< eff}.

  (* The meaning of an expression *)
  Fixpoint denoteExpr (e : expr) : itree eff value :=
    match e with
    | Var v => lift (GetVar v)
    | Lit n => ret n
    | Plus a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (l + r)
    end.

  Definition while {eff} (t : itree eff bool) : itree eff unit :=
    loop 
      (fun l : unit + unit =>
         match l with
         | inr _ => ret (inl tt)
         | inl _ => continue <- t ;;
                   if continue : bool then ret (inl tt) else ret (inr tt)
         end) tt.

  (* the meaning of a statement *)
  Fixpoint denoteStmt (s : stmt) : itree eff unit :=
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
    end.

End Denote.

From ITree Require Import
     Effects.Env.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Definition evalLocals {E: Type -> Type} `{envE var value -< E}: Locals ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => env_lookupDefault x 0
    | SetVar x v => env_add x v
    end.

Definition env := alist var value.

(* Enable typeclass instances for Maps keyed by strings and values *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.

Definition ImpEval (s: stmt): itree void1 (env * unit) :=
  let p := interp evalLocals _ (denoteStmt s) in
  run_env _ p empty.
