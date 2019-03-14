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

Import MonadNotation.
Local Open Scope monad_scope.
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
| Print  (s : string)
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

  Notation "'PRINT' s" :=
    (Print s)
      (at level 100,
       right associativity): stmt_scope.

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
Variant Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

Variant PrintE : Type -> Type :=
| Out (s : string) : PrintE unit.

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
  Context {HasPrint : PrintE -< eff}.

  (** _Imp_ expressions are denoted as [itree eff value], where the returned value
      in the tree is the value computed by the expression.
      In the [Var] case, the [lift] operator allows to smoothly lift a single effect to
      a [itree] performing the corresponding [Vis] event and returning immediately the
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

  (** We turn to the denotation of statements. As opposed to expressions, statements
      do not return any value: their semantic domain is therefore [itree eff unit].
      The most interesting construct is naturally the [while].

      To define its meaning, we make use of the [loop] combinator provided by
      the [itree] library: [loop : (C + A -> itree E (C + B)) -> A -> itree E B].
      The combinator takes as argument the body of the loop, i.e. a function
      that maps to inputs of type [C + A] a [itree], a computation, returning
      either a [C] that can be fed back to the loop, or a return value of type
      [B], and builds the fixpoint of the body, hiding away the [C] argument.

   (* YZ NOTE: Insert a reference here to Factorial directly defined over trees  *)

      We use [loop] to first build a new combinator [while] that takes a boolean
      computation, runs it and loops if it is true, exits otherwise.
   *)

  Definition while {eff} (t : itree eff bool) : itree eff unit :=
    loop
      (fun l : unit + unit =>
         match l with
         | inr _ => ret (inl tt)
         | inl _ => continue <- t ;;
                   if continue : bool then ret (inl tt) else ret (inr tt)
         end) tt.

  (** The meaning of statements can now be defined.
      They are all straightforward, except for [While] that uses our new
      [while] combinator over the computation that evaluates the conditional,
      and then the body if it were true.
   *)
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
    | Print s => lift (Out s)
    end.

End Denote.

Section Denote_Fact.

  (** We illustrate the language by writing the traditional factorial. *)

  Open Scope expr_scope.
  Open Scope stmt_scope.
  Variable input: var.
  Variable output: var.

  Definition fact (n:nat): stmt :=
    input ← n;;
    output ← 1;;
    WHILE input
    DO output ← output * input;;
       input  ← input - 1
    DONE.

  (* YZ NOTE: For tutorial purpose, it could be good to be able to show /some/
   representation of the tree inside of Coq. Can we have anything better than the
   following?
   *)
  Eval simpl in denoteStmt (fact 6).

  (** We have so far given meaning to [Imp] in terms of [itree]s. In order to
      actually run the computation, we now need to /handle/ the events contained
      in the trees, i.e. give a concrete interpretation of the environment.
   *)

End Denote_Fact.

From ITree Require Import
     Effects.Env.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(** We provide an /ITree event handler/ to interpret away [Locals] events.
    We use an /environment effect/ to do so, modelling the environment as
    a 0-initialized environment.
 *)

(* YZ NOTE: Here also we assume some global [E] that contains [envE] events.
   We could instead have had [Locals ~> itree (envE var value)]?
   Why chose this parameterized approach? It forces at the top level to instantiate
   things with some kind of static global [E] containing everything: does it have any
   drawbacks?
 *)
Definition evalLocals {E: Type -> Type} `{envE var value -< E}:
  Locals ~> itree E :=
  fun _ e =>
    (* match e with *)
    (* | inl1 e => *)
      match e with
      | GetVar x => env_lookupDefault x 0
      | SetVar x v => env_add x v
    (*   end *)
    (* | inr1 e => *)
    (*   match e with *)
    (*   | Out s => ret tt *)
    (*   end *)
    end.

(** We specifically implement this environment using ExtLib's finite maps. *)
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

(* Finally, we can define an evaluator for our statements.
   To do so, we first denote them, leading to a [itree Locals unit].
   We then [interp]ret [Locals] into [envE] using [evalLocals], leading to
   a [itree (envE var value) unit].
   Finally, [run_env] interprets the [itree] into the state monad, resulting into
   a an [itree] free of any effect, but returning an environment.
 *)
(* YZ NOTE: Here, we actually constrain the [eff] argument in [denoteStmt] to be
   exactly [Locals] rather than any universe of effect containing it.
 *)
(* Definition ImpEval (s: stmt) : itree void1 (env * unit):= *)
(*   let p := interp evalLocals _ (denoteStmt s) in *)
(*   run_env _ p empty. *)
