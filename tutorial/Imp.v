(** We demonstrate how to use [itrees] in the context of verified compilation.
    To this end, we start in this file by introduceing a simplified variant of
    Software Foundations' [Imp] language.
    The language's semantics is expressed in terms of [itrees].
    The resulting semantics can be run through provided interpreters.
 *)

From Coq Require Import
     Lists.List
     Strings.String.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     Basics
     ITree.

Local Open Scope string_scope.

(* ================================================================= *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** For simplicity, the language manipulates [nat]s as values. *)
Definition value : Type := nat.

(** Expressions are made of variables, constant litterals, additions and substractions. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus (_ _ : expr)
| Minus (_ _ : expr)
| Mult (_ _ : expr).

(** _Imp_ statements: *)
Definition is_true (v : value) : bool := if v then false else true.

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
.

(* ================================================================= *)
(** ** Notations *)

Module ImpNotations.

  (* YZ: TODO Improve notations.
     And also, understand why overloaded notations seem to require to share the same level.
   *)
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
  
  Notation "a ;; b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v ' a  ';;' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'IF' i 'THEN' t 'ELSE' e 'FI'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'IF'  i '/' '[' 'THEN'  t  ']' '/' '[' 'ELSE'  e ']' 'FI' ']'").

  Notation "'WHILE' t 'DO' b 'DONE'" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v ' 'WHILE'  t '/' '[' 'DO'  b  ']' DONE ']'").

End ImpNotations.

(* ================================================================= *)
(** ** Semantics *)

Import ImpNotations.

(** _Imp_ produces effects by manipulating its variables.
    To account for this, we define a type of _external interactions_
    [Locals] modelling reads and writes to variables.
    A read, [GetVar], takes a variable as an argument and expects
    the environment to answer with a value, hence defining an effect
    of type [Locals value].
    Similarly, [SetVar] is a write effect parameterized by both a variable
    and a value to be written, and defines an effect of type [Locals unit],
    no informative answer being expected from the environment.
 *)
Inductive Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

Section Denote.

  (* YZ: TODO get a clear sense of what we want to qualify of:
     * meaning
     * semantics
     * denotation
     and be consistent about it.
   *)
  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of effects to be considered,
      taking as a semantic domain for _Imp_ [itree eff X].
      That would be sufficient to give meaning to _Imp_, but is inconvenient to
      relate this meaning to [itree]s stemmed from other entities.
      We therefore parameterize the denotation of _Imp_ by a larger universe of
      effects [eff] of which [Locals] is a subeffect.
   *)
  (* YZ: TODO think some more about where exactly we take advantage of this approach.
         Had initially in mind obviously when relating the denotations of imp and asm
         to prove the compiler correct. However we actually first interpret away all
         effects, hence it's not so clear.
   *)

  Context {eff : Type -> Type}.
  Context {HasLocals : Locals -< eff}.

  (** _Imp_ expressions are denoted as [itree eff value], where the returned value
      in the tree is the value computed by the expression.
      In the [Var] case, the [lift] operator allows to smoothly lift a single effect to
      an [itree] performing the corresponding [Vis] event and returning immediately the
      environment's answer.
      Usual monadic notations are used in the other cases. A constant is simply returned,
      while we can [bind] recursive computations in the case of operators as one would
      expect.
   *)

  Fixpoint denoteExpr (e : expr) : itree eff value :=
    match e with
    | Var v => lift (GetVar v)
    | Lit n => ret n
    | Plus a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (l + r)
    | Minus a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (l - r)
    | Mult a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (l * r)
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

Section Fact.

  Open Scope expr_scope.
  Open Scope stmt_scope.
  Variable input: var.
  Variable output: var.

  Definition fact (n:nat) :=
    input ← n;;
    output ← 1;;
    WHILE input
    DO output ← output * input;;
       input  ← input - 1
    DONE.

End Fact.

From ITree Require Import
     Effect.Env.

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

Definition ImpEval (s: stmt): itree emptyE (env * unit) :=
  let p := interp evalLocals _ (denoteStmt s) in
  run_env _ p empty.
