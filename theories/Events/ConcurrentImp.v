Require Import String.
Require Import Arith.PeanoNat.

Open Scope string_scope.

Inductive expr : Type :=
  | Var (x : string)
  | Lit (n : nat).


Inductive stmt : Type :=
  | Assign (x : string) (e : expr) (* x = e *)
  | If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
  | Seq    (a b : stmt)            (* a ; b *)
  | Par (a b : stmt)               (* a || b *).


Notation "x '::=' n" := (Assign x n) (at level 60).
Notation "c1 ;; c2" := (Seq c1 c2) (at level 80, right associativity).
Notation "c1 ||| c2" := (Par c1 c2) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" := (If c1 c2 c3) (at level 80, right associativity).

CoInductive itree (E : Type -> Type) (A : Type): Type :=
  | Ret (a : A)
  | Tau (t : itree E A)
  | Vis {X : Type} (e : E X) (c : X -> itree E A).


Variant nondetE : Type -> Type :=
  | Or : nondetE bool.


Definition union (E1 E2 : Type -> Type) : (Type -> Type) := (fun tau => sum (E1 tau) (E2 tau)).


Variant ImpState : Type -> Type :=
  | GetVar (x : string) : ImpState nat
  | SetVar (x : string) (v : nat) : ImpState unit.


CoFixpoint bind {E : Type -> Type} {R S : Type} (t : itree E R) (c : R -> itree E S) : itree E S :=
  match t with
    | Ret _ _ r => c r
    | Tau _ _ t => Tau _ _ (bind t c)
    | Vis _ _ e k => Vis _ _ e (fun x => bind (k x) c)
  end.


Notation "t1 ;;; t2" := (bind t1 (fun _ => t2)) (at level 61, right associativity).
Notation "x <- t1 ;;; t2" := (bind t1 (fun x => t2)) (at level 61, t1 at next level, right associativity).


Fixpoint denote_expr (e : expr) : itree (union ImpState nondetE) nat :=
  match e with
    | Var x => Vis _ _ (inl (GetVar x)) (fun n => Ret _ _ n)
    | Lit n => Ret  _ _ n
  end.

Definition is_true (v : nat) : bool := if (v =? 0)%nat then false else true.


CoFixpoint par {E} (t1 t2 : itree (union E nondetE) unit) : (itree (union E nondetE) unit) := 
  match t1, t2 with
    | Ret _ _ a, _ => t2
    | _, Ret _ _ a => t1
    | Tau _ _ t'1, Tau _ _ t'2 => Vis _ _ (inr Or) (fun b : bool => if b then par t'1 t2 else par t1 t'2)
    | Tau _ _ t'1, Vis _ _ e2 c2 => Vis _ _ (inr Or) (fun b : bool => if b then par t'1 t2 else Vis _ _ e2 (fun x => par t1 (c2 x)))
    | Vis _ _ e1 c1, Tau _ _ t'2 => Vis _ _ (inr Or) (fun b : bool => if b then Vis _ _ e1 (fun x => par (c1 x) t2) else par t1 t'2)
    | Vis _ _ e1 c1, Vis _ _ e2 c2 =>  Vis _ _ (inr Or) (fun b : bool => if b then Vis _ _ e1 (fun x => par (c1 x) t2) else  Vis _ _ e2 (fun x => par t1 (c2 x)))
  end.


Fixpoint denote_stmt (t : stmt) : itree (union ImpState nondetE) unit :=
  match t with
    | Assign x e => v <- denote_expr e ;;; Vis _ _ (inl (SetVar x v)) (fun _ => Ret _ _ tt)
    | Seq t1 t2 => denote_stmt t1 ;;; denote_stmt t1
    | If e t1 t2 => v <- denote_expr e ;;; if is_true v then denote_stmt t1 else denote_stmt t2
    | Par t1 t2 => par (denote_stmt t1) (denote_stmt t2)
  end.

Definition example : stmt :=
  "x" ::= Lit 0 ;;
  "y" ::= Lit 0 ;;
  (("x" ::= Lit 1) ||| (TEST Var "x" THEN "y" ::= Lit 1 ELSE "y" ::= Lit 0 FI)).

Definition env := string -> nat.

CoInductive stream := cons (b : bool) (s : stream).

Definition update_env (f : env) (x : string) (n : nat) := fun y => if x =? y then n else f y.

Fixpoint eval 
(t : itree (union ImpState nondetE) unit)
(s : stream)
(f : env)
(n : nat) :
env :=
  match n with
    | 0 => f
    | S n => (match t, s with
            | Ret _ _ tt, _ => f
            | Tau _ _ t, _ => eval t s f n
            | Vis _ _ (inl (GetVar x)) k, _ => eval (k (f x)) s f n
            | Vis _ _ (inl (SetVar x v)) k, _ => eval (k tt) s (update_env f x v) n
            | Vis _ _ (inr Or) k, cons b bs => eval (k b) bs f n
            end)
   end.
