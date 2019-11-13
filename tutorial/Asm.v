(** * The Asm language  *)

(** We now consider as a target a simple control-flow-graph language, so-called
    _Asm_.  Computations are represented as a collection of basic blocks linked
    by jumps.  *)

(* begin hide *)
From Coq Require Import
     Strings.String
     Program.Basics
     ZArith.ZArith
     Morphisms
     Setoid
     RelationClasses.

Require Import ExtLib.Structures.Monad.

  (* SAZ: Should we add ITreeMonad to ITree? *)
From ITree Require Import
     ITree
     ITreeFacts
     ITreeMonad
     Basics.MonadTheory
     Basics.CategorySub
     Events.State
     Events.StateKleisli
     Events.StateFacts.

Require Import Fin Utils_tutorial.

Import Monads.
(* end hide *)

(** ** Syntax *)

(** We define a countable set of memory addresses, represented as [string]s: *)
Definition addr : Set := string.

(** We define a set of register names (for this simple example, we identify them
with [nat]). *)
Definition reg : Set := nat.

(** For simplicity, _Asm_ manipulates [nat]s as values too. *)
Definition value : Set := nat.

(** We consider constants and variables as operands. *)
Variant operand : Set :=
| Oimm (_ : value)
| Oreg (_ : reg).

(** The instruction set covers moves and arithmetic operations, as well as load
    and stores to the heap.  *)
Variant instr : Set :=
| Imov   (dest : reg) (src : operand)
| Iadd   (dest : reg) (src : reg) (o : operand)
| Isub   (dest : reg) (src : reg) (o : operand)
| Imul   (dest : reg) (src : reg) (o : operand)
| Iload  (dest : reg) (addr : addr)
| Istore (addr : addr) (val : operand).

(** We consider both direct and conditional jumps *)
Variant branch {label : Type} : Type :=
| Bjmp (_ : label)                (* jump to label *)
| Bbrz (_ : reg) (yes no : label) (* conditional jump *)
| Bhalt
.
Global Arguments branch _ : clear implicits.

(** A basic [block] is a sequence of straightline instructions followed by a
    branch that either halts the execution, or transfers control to another
    [block]. *)
Inductive block {label : Type} : Type :=
| bbi (_ : instr) (_ : block)
| bbb (_ : branch label).
Global Arguments block _ : clear implicits.



(** A piece of code should expose the set of labels allowing to enter into it,
    as well as the set of outer labels it might jump to.  To this end, [bks]
    represents a collection of blocks labeled by [F A], with branches in [F B].
*)

Definition bks A B := fin A -> block (fin B).


(** An [asm] program represents the control flow of the computation.  It is a
    collection of labelled [blocks] such that its labels are classified into
    three categories:

    - [A]: (visible) entry points

    - [B]: (visible) exit points

    - [internal]: (hidden) internal linked labels

    Note that they uniformly represent open and closed programs, the latter
    corresponding to an [asm] program with a unique entry point and no exit
    labels, i.e. a [asm unit void].  Note that using [void] to describe the exit
    points means that closed program must either diverge (go into an infinite
    loop) or somehow generate an event that terminates them.  (See the
    denotation of [Bhalt] below.)  *)

Record asm (A B: nat) : Type :=
  {
    internal : nat;
    code     : bks (internal + A) (internal + B)
  }.

Arguments internal {A B}.
Arguments code {A B}.

(* ========================================================================== *)
(** ** Semantics *)

(** _Asm_ produces two kind of events for manipulating its two kinds of state:
    registers and the heap.
*)
Class HasReg (m : Type -> Type) : Type :=
  { get_reg : reg -> m value
  ; set_reg : reg -> value -> m unit
  }.

Class HasMemory (m : Type -> Type) : Type :=
  { load : addr -> m value
  ; store : addr -> value -> m unit
  }.

(* SAZ: Move Exit to the itrees library? *)
(** We also introduce a special event to model termination of the computation.
    Note that it expects _actively_ no answer from the environment: [Done] is
    of type [Exit void].  We can therefore use it to "close" an [itree E A] no
    matter what the expected return type [A] is, as witnessed by the [exit]
    computation.  *)
Class MonadExit (m : Type -> Type) : Type :=
  exit : forall a, m a.

Arguments exit {m _ a}.

Section Denote.

  (** Once again, [asm] programs shall be denoted as [itree]s. *)

  (* begin hide *)
  Import ExtLib.Structures.Monad.
  Import MonadNotation.
  Local Open Scope monad_scope.
  (* end hide *)

  Section with_event.

    (** As with _Imp_, we parameterize our semantics by a universe of events
        that shall encompass all the required ones. *)
    Context
      {m : Type -> Type}
      {Monad_m : Monad m}
      {MonadIter_m : MonadIter m}
      {HasReg_m : HasReg m}
      {HasMemory_m : HasMemory m}
      {MonadExit_m : MonadExit m}.

    (** Operands are trivially denoted as [itree]s returning values *)
    Definition denote_operand (o : operand) : m value :=
      match o with
      | Oimm v => ret v
      | Oreg v => get_reg v
      end.

    (** Instructions offer no suprises either. *)
    Definition denote_instr (i : instr) : m unit :=
      match i with
      | Imov d s =>
        v <- denote_operand s ;;
        set_reg d v
      | Iadd d l r =>
        lv <- get_reg l ;;
        rv <- denote_operand r ;;
        set_reg d (lv + rv)
      | Isub d l r =>
        lv <- get_reg l ;;
        rv <- denote_operand r ;;
        set_reg d (lv - rv)
      | Imul d l r =>
        lv <- get_reg l ;;
        rv <- denote_operand r ;;
        set_reg d (lv * rv)
      | Iload d addr =>
        val <- load addr ;;
        set_reg d val
      | Istore addr v =>
        val <- denote_operand v ;;
        store addr val
      end.

    Section with_labels.
      Context {A B : nat}.

      (** A [branch] returns the computed label whose set of possible values [B]
          is carried by the type of the branch.  If the computation halts
          instead of branching, we return the [exit] tree.  *)
      Definition denote_branch (b : branch (fin B)) : m (fin B) :=
        match b with
        | Bjmp l => ret l
        | Bbrz v y n =>
          val <- get_reg v ;;
          if val:nat then ret y else ret n
        | Bhalt => exit
        end.

      (** The denotation of a basic [block] shares the same type, returning the
          [label] of the next [block] it shall jump to.  It recursively denote
          its instruction before that.  *)
      Fixpoint denote_block (b : block (fin B)) : m (fin B) :=
        match b with
        | bbi i b =>
          denote_instr i ;; denote_block b
        | bbb b =>
          denote_branch b
        end.

      (* TODO: explain [sktree] -- think of a better name? *)
      (** A labelled collection of blocks, [bks], is simply the pointwise
          application of [denote_block].  However, its denotation is therefore
          crucially a [ktree], whose structure will be useful in the proof of
          the compiler.

          The type [ktree E A B] is shorthand for [A -> itree E B], and we can
          think of them as "continuations" with events in E.  They have a nice
          algebraic structure, supported by the library, including a [loop]
          combinator that we can use to link collections of basic blocks. (See
          below.) *)
      Definition denote_bks (bs: bks A B) : sub (Kleisli m) fin A B :=
        fun a => denote_block (bs a).

    End with_labels.

  (** One can think of an [asm] program as a circuit/diagram where wires
      correspond to jumps/program links.  [denote_bks] computes the meaning of
      each basic block as an [itree] that returns the label of the next block to
      jump to, laying down all our elementary wires.  In order to denote an [asm
      A B] program as a [ktree E A B], it therefore remains to wire all those
      denoted blocks together while hiding the internal labels.  Luckily, that
      is exactly what traced monoidal category are good for.  We therefore
      accomplish this with the same [loop] combinator we used to denote _Imp_'s
      [while] loop.  It directly takes our [denote_bks (code s): ktree E (I + A)
      (I + B)] and hides [I] as desired.  *)
    Definition denote_asm {A B} : asm A B -> sub (Kleisli m) fin A B :=
      fun s => loop (denote_bks (code s)).

  End with_event.
End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Basics.Category
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Data.String
     Structures.Maps
     Data.Map.FMapAList.

(* begin hide *)
(** These enable typeclass instances for Maps keyed by strings and registers *)
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

(* SAZ: Annoyingly, typeclass resolution picks the wrong map instance for nats by default, so
   we create an instance for [reg] that hides the wrong instance with the right one. *)
Instance RelDec_reg : RelDec (@eq reg) := RelDec_from_dec eq Nat.eq_dec.
(* end hide *)

(** Both environments and memory events can be interpreted as "map" events,
    exactly as we did for _Imp_. *)

(** Once again, we implement our Maps with a simple association list *)
Definition registers := alist reg value.
Definition memory    := alist addr value.
Definition asm_env : Type := registers * memory.

Import StateMonad.

Instance HasReg_stateT {m: Type -> Type} `{Monad m}
  : HasReg (stateT asm_env m) :=
  {| get_reg x := mkStateT (fun s => ret (lookup_default x 0 (fst s), s))
   ; set_reg x v := mkStateT (fun s => ret (tt, (add x v (fst s), snd s)))
  |}.

Instance HasMemory_stateT {m: Type -> Type} `{Monad m}
  : HasMemory (stateT asm_env m) :=
  {| load x := mkStateT (fun s => ret (lookup_default x 0 (snd s), s))
   ; store x v := mkStateT (fun s => ret (tt, (fst s, add x v (snd s))))
  |}.

Instance MonadExit_stateT {S} {m: Type -> Type} `{MonadExit m}
  : MonadExit (stateT S m).
Admitted.

Instance MonadExit_itree {E} : MonadExit (itree E). Admitted. (* TODO *)

(** The _asm_ interpreter takes as inputs a starting heap [mem] and register
    state [reg] and interprets an itree in two nested instances of the [map]
    variant of the state monad. To get this type to work out, we have to
    do a bit of post-processing to swap the order of the "state components"
    introduced by the interpretation.
*)

(** We can then define an evaluator for closed assembly programs by interpreting
    both store and heap events into two instances of [mapE], and running them
    both in the empty initial environments.  *)
Definition run_asm (p: asm 1 0) : itree void1 asm_env :=
  execStateT (denote_asm p Fin.f0) (empty, empty).

(** Now that we have both our language, we could jump directly into implementing
our compiler.  However, if we look slightly ahead of us, we can observe that: -
compiling expressions and basic statements will be mostly straightforward; - but
linking the resulting elementary (open) [asm] programs together is not as
trivial. In particular, reasoning inductively on this linking is more
challenging.  We therefore take a detour: we first reason in isolation about
linking, and to this end we jump to [AsmCombinators.v].  *)
