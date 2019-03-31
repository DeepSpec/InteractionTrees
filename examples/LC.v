(* Big-step reduction of untyped lambda terms. *)

From Coq Require Import Arith.

From ExtLib.Structures Require Import
     Monad.
Import MonadNotation.
Open Scope monad_scope.

From ITree Require Import
     ITree
     Interp.Recursion.

Inductive term : Type :=
| Var : nat -> term
(* DeBruijn indexed *)

| App : term -> term -> term

| Lam : term -> term
.

Inductive headvar : Type :=
| VVar : nat -> headvar
| VApp : headvar -> value -> headvar
with value : Type :=
| VHead : headvar -> value
| VLam : term -> value
.

Fixpoint to_term (v : value) : term :=
  match v with
  | VHead hv => hv_to_term hv
  | VLam t => Lam t
  end
with hv_to_term (hv : headvar) : term :=
  match hv with
  | VVar n => Var n
  | VApp hv v => App (hv_to_term hv) (to_term v)
  end.

Fixpoint shift (n m : nat) (s : term) :=
  match s with
  | Var p =>
    if p <? m then Var (n + p)
    else Var p
  | App t1 t2 => App (shift n m t1) (shift n m t2)
  | Lam t => Lam (shift n (S m) t)
  end.

Fixpoint subst (n : nat) (s t : term) :=
  match t with
  | Var m =>
    if m <? n then Var m
    else if m =? n then shift n O s
    else Var (pred m)
  | App t1 t2 => App (subst n s t1) (subst n s t2)
  | Lam t => Lam (subst (S n) s t)
  end.

(* big-step call-by-value *)
Definition big_step : term -> itree void1 value :=
  rec (fun t =>
    match t with
    | Var n => ret (VHead (VVar n))
    | App t1 t2 =>
      t2' <- trigger (Call t2);;
      t1' <- trigger (Call t1);;
      match t1' with
      | VHead hv => ret (VHead (VApp hv t2'))
      | VLam t1'' =>
        trigger (Call (subst O (to_term t2') t1''))
      end
    | Lam t => ret (VLam t)
    end).
