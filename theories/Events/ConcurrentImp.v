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

(* YZ: Why are you redefining everything??? *)
CoInductive itree (E : Type -> Type) (A : Type): Type :=
  | Ret (a : A)
  | Tau (t : itree E A)
  | Vis {X : Type} (e : E X) (c : X -> itree E A).


Variant nondetE : Type -> Type :=
  | Or : nondetE bool.


(* YZ: this "union" is called "sum1" in the library, and written "+'" *)
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

(**
 BEGIN YZ COMMENT
   This is not how we evaluate itrees.
   itrees are evaluated by providing a handler that gives a meaning to some events E in terms of a monad M.
   The notion of interpreter [interp] then takes such an handler as argument, and gives a meaning to a
   whole [itree E] in term of M.

   So here in particular such a function fixing a scheduler should probably be something like:
   schedules: itree (nondetE +' ImpState) ~> stateT (stream nat) (itree ImpState)

END YZ COMMENT
**)

(* You can work interactively with it like that: *)
Fixpoint eval'
(fuel : nat)
(t : itree (union ImpState nondetE) unit)
(s : stream)
(f : env)
  {struct fuel}:
  env.
  refine (
  match fuel with
    | 0 => f
    | S n => match s with
            | cons b bs => _
            end
  end).
  destruct t eqn:EQ.
  exact f.
  refine (eval' n t s f).
  destruct e.
  - destruct i.
    refine (eval' n (c (f x)) s f).
    refine (eval' n (c tt) s (update_env f x v)).
  - destruct n0.
    refine (eval' n (c b) bs f).
Defined.

(* It should compute, and by printing you can get the direct definition: *)

Definition eval :=
fix eval (fuel : nat) (t : itree (union ImpState nondetE) unit) (s : stream) (f : env) {struct fuel} : env :=
  match fuel with
  | 0 => f
  | S n =>
      match s with
      | cons b bs =>
          let i := t in
          let EQ : t = i := eq_refl in
          match i as i0 return (t = i0 -> env) with
          | Ret _ _ a => fun _ : t = Ret (union ImpState nondetE) unit a => f
          | Tau _ _ i0 => fun _ : t = Tau (union ImpState nondetE) unit i0 => eval n t s f
          | @Vis _ _ X e c =>
              fun EQ0 : t = Vis (union ImpState nondetE) unit e c =>
              match e as s0 return (t = Vis (union ImpState nondetE) unit s0 c -> env) with
              | inl i0 =>
                  fun EQ1 : t = Vis (union ImpState nondetE) unit (inl i0) c =>
                  match
                    i0 as i1 in (ImpState T)
                    return
                      (forall c0 : T -> itree (union ImpState nondetE) unit,
                       t = Vis (union ImpState nondetE) unit (inl i1) c0 -> env)
                  with
                  | GetVar x =>
                      fun (c0 : nat -> itree (union ImpState nondetE) unit)
                        (_ : t = Vis (union ImpState nondetE) unit (inl (GetVar x)) c0) => 
                      eval n (c0 (f x)) s f
                  | SetVar x v =>
                      fun (c0 : unit -> itree (union ImpState nondetE) unit)
                        (_ : t = Vis (union ImpState nondetE) unit (inl (SetVar x v)) c0) =>
                      eval n (c0 tt) s (update_env f x v)
                  end c EQ1
              | inr n0 =>
                  fun EQ1 : t = Vis (union ImpState nondetE) unit (inr n0) c =>
                  match
                    n0 as n1 in (nondetE T)
                    return
                      (forall c0 : T -> itree (union ImpState nondetE) unit,
                       t = Vis (union ImpState nondetE) unit (inr n1) c0 -> env)
                  with
                  | Or =>
                      fun (c0 : bool -> itree (union ImpState nondetE) unit)
                        (_ : t = Vis (union ImpState nondetE) unit (inr Or) c0) => eval n (c0 b) bs f
                  end c EQ1
              end EQ0
          end EQ
      end
  end.

(* That you may be able to clean up a bit after if need be *)
