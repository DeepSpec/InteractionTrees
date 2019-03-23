(** * The Imp language  *)

(** We now demonstrate how to use ITrees in the context of verified compilation.
    To this end, we will consider a simple compiler from an imperative language
    to a control-flow-graph language.
    The meaning of both languages will be given in terms of ITrees, so that the
    proof of correctness is expressed by proving a bisimulation between ITrees.
    We shall emphasize two main satisfying aspects of the resulting formalization.
    - Despite the correctness being termination-sensitive, we do not write any
    cofixpoints. All reasoning is purely equational, and the underlying
    coinductive reasoning is hidden on the library side.
    - We split the correctness in two steps. First, a linking theory of the CFG language
    is proved correct. Then, this theory is leveraged to prove the functionnal correctness
    of the compiler. The first piece is fairly generic, and hence reusable.
 *)

(** This tutorial is composed of the following files:
    - Utils_tutorial.v     : utilities
    - Imp.v                : Imp language, syntax and semantics
    - Asm.v                : Asm language, syntax and semantics
    - AsmCombinators.v     : Linking theory for Asm
    - Imp2Asm.v            : Compiler from Imp to Asm
    - Imp2AsmCorrectness.v : Proof of correctness of the compiler
    The intended entry point for reading is Imp.v.
 *)

(** We thefore start by introducing a simplified variant of Software Foundations'
    [Imp] language.
    The language's semantics is first expressed in terms of [itree]s.
    The semantics of the program can then be obtained by
    interpreting the events contained in the trees.
 *)

(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
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

(* end hide *)

(* ================================================================= *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** For simplicity, the language manipulates [nat]s as values. *)
Definition value : Type := nat.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus (_ _ : expr)
| Minus (_ _ : expr)
| Mult (_ _ : expr).

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

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

End ImpNotations.

Import ImpNotations.

(* ================================================================= *)
(** ** Semantics *)

(** _Imp_ produces effects by manipulating its variables.
    To account for this, we define a type of _external interactions_
    [Locals] modeling reads and writes to variables.
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

Section Denote.

  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of effects to be considered,
      taking as a semantic domain for _Imp_ [itree Locals X].
      That would be sufficient to give meaning to _Imp_, but is inconvenient to
      relate this meaning to [itree]s stemmed from other entities.
      We therefore parameterize the denotation of _Imp_ by a larger universe of
      effects [eff], of which [Locals] is assumed to be a subeffect.
   *)

  Context {eff : Type -> Type}.
  Context {HasLocals : Locals -< eff}.

  (** _Imp_ expressions are denoted as [itree eff value], where the returned value
      in the tree is the value computed by the expression.
      In the [Var] case, the [lift] operator smoothly lifts a single effect to
      an [itree] by performing the corresponding [Vis] event and returning the
      environment's answer immediately.
      Usual monadic notations are used in the other cases. A constant (literal) is
      simply returned, while we can [bind] recursive computations in the case of
      operators as one would expect.
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
      The most interesting construct is naturally [while].

      To define its meaning, we make use of the [loop] combinator provided by
      the [itree] library:
      [loop : (C + A -> itree E (C + B)) -> A -> itree E B].
      The combinator takes as argument the body of the loop, i.e. a function
      that maps inputs of type [C + A] to an [itree] computing either a [C] that
      can be fed back to the loop, or a return value of type [B]. The combinator
      builds the fixpoint of the body, hiding away the [C] argument.
      
      Compared to the [mrec] and [rec] combinators introduced in [Introduction.v], [loop]
      is more restricted in that it naturally represents tail recursive functions.
      It however enjoys a rich equational theory: its addition grants the type of
      _continuation trees_, named [ktree]s in the library, a structure of
      _traced monoidal category_.

      We use [loop] to first build a new combinator [while] that takes a boolean
      computation, runs it, and loops if it returns true, exits otherwise.
   *)

  Definition while {eff} (t : itree eff bool) : itree eff unit :=
    loop 
      (fun l : unit + unit =>
         match l with
         | inr _ => ret (inl tt)
         | inl _ => continue <- t ;;
                   if continue : bool then ret (inl tt) else ret (inr tt)
         end) tt.

  (** Casting values into [bool]. *)

  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  (** The meaning of statements is now easy to define.
      They are all straightforward, except for [While] that uses our new
      [while] combinator over the computation that evaluates the conditional,
      and then the body if the former was true.
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
    end.

End Denote.

(* ================================================================= *)
(** ** Factorial *)

Section Denote_Fact.

  (** We briefly illustrate the language by writing the traditional factorial. *)

  Open Scope expr_scope.
  Open Scope stmt_scope.
  Variable input: var.
  Variable output: var.

  Definition fact (n:nat): stmt :=
    input ← n;;;
    output ← 1;;;
    WHILE input
    DO output ← output * input;;;
       input  ← input - 1.

  (** We have given _a_ notion of denotation to [fact 6] via [denoteStmt].
      However this is naturally not actually runnable yet, since it contains
      uninterpreted [Locals] events.
      We therefore now need to /handle/ the events contained
      in the trees, i.e. give a concrete interpretation of the environment.
   *)

End Denote_Fact.

(* ================================================================= *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Effects.Map.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
(* end hide *)

(** We provide an /ITree event handler/ to interpret away [Locals] events.
    We use an /environment effect/ to do so, modeling the environment as
    a 0-initialized environment.
    Recall from [Introduction.v] that a _handler_ for the effects [Locals]
    is a function of type [forall R, Locals R -> M R] for some monad [M].
    Here we take for our monad the special case of [M = itree E] for some
    universe of effects [E] required to contain the environment effects [envE]
    provided by the library. It comes with an effect handler [run_env]
    interpreting the computation into the state monad.
 *)

Definition evalLocals {E: Type -> Type} `{mapE var value -< E}: Locals ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x 0
    | SetVar x v => insert x v
    end.

(** We now concretely implement this environment using ExtLib's finite maps. *)
Definition env := alist var value.

(** These enable typeclass instances for Maps keyed by strings and values *)
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

(** Finally, we can define an evaluator for our statements.
   To do so, we first denote them, leading to an [itree Locals unit].
   We then [interp]ret [Locals] into [envE] using [evalLocals], leading to
   an [itree (envE var value) unit].
   Finally, [run_env] interprets the latter [itree] into the state monad,
   resulting in an [itree] free of any effect, but returning an environment.
 *)

Definition ImpEval (s: stmt): itree void1 (env * unit) :=
  let p := interp evalLocals _ (denoteStmt s) in
  run_map _ p empty.

(** Equipped with this evaluator, we can now compute.
    Naturally since Coq is total, we cannot do it directly
    inside of it. We can either rely on extraction, or
    use some fuel.
 *)
Compute (burn 100 (ImpEval (fact "x" "y" 6))). 

(** We now turn to our target language, in file [Asm].v *)
