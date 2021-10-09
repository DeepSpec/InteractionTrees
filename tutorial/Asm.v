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
     Basics.Monad
     Basics.CategorySub
     Events.State
     Events.StateFacts
     Events.FailFacts.

From ITreeTutorial Require Import Fin Utils_tutorial.

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
| Babort
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
Variant Reg : Type -> Type :=
| GetReg (x : reg) : Reg value
| SetReg (x : reg) (v : value) : Reg unit.

Inductive Memory : Type -> Type :=
| Load  (a : addr) : Memory value
| Store (a : addr) (val : value) : Memory unit.


(* SAZ: Move Exit to the itrees library? *)
(** We also introduce a special event to model termination of the computation.
    Note that it expects _actively_ no answer from the environment: [Done] is
    of type [Exit void].  We can therefore use it to "close" an [itree E A] no
    matter what the expected return type [A] is, as witnessed by the [exit]
    computation.  *)
Inductive Exit : Type -> Type :=
| Done : Exit void.

Variant Abort : Type -> Type :=
| CAbort : Abort void.

Definition exit {E F A} `{Exit +? F -< E} : itree E A :=
  vis Done (fun v => match v : void with end).

(* begin hide *)
Import ExtLib.Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.
(* end hide *)

Section Denote.

  (** Once again, [asm] programs shall be denoted as [itree]s. *)
  Section with_event.

    (** As with _Imp_, we parameterize our semantics by a universe of events
        that shall encompass all the required ones. *)
    Context {E C1 C2 C3 C4 : Type -> Type}.
    Context {HasReg : Reg +? C1 -< E}.
    Context {HasMemory : Memory +? C2 -< E}.
    Context {HasExit : Exit +? C3 -< E}.
    Context {HasAbort : Abort +? C4 -< E}.

    (** Operands are trivially denoted as [itree]s returning values *)
    Definition denote_operand (o : operand) : itree E value :=
      match o with
      | Oimm v => Ret v
      | Oreg v => trigger (GetReg v)
      end.

    (** Instructions offer no suprises either. *)
    Definition denote_instr (i : instr) : itree E unit :=
      match i with
      | Imov d s =>
        v <- denote_operand s ;;
        trigger (SetReg d v)
      | Iadd d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (lv + rv))
      | Isub d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (lv - rv))
      | Imul d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (lv * rv))
      | Iload d addr =>
        val <- trigger (Load addr) ;;
        trigger (SetReg d val)
      | Istore addr v =>
        val <- denote_operand v ;;
        trigger (Store addr val)
      end.

    (** A [branch] returns the computed label whose set of possible values [B]
        is carried by the type of the branch.  If the computation halts
        instead of branching, we return the [exit] tree.  *)
    Definition denote_br {B} (b : branch B) : itree E B :=
      match b with
      | Bjmp l => ret l
      | Bbrz v y n =>
        val <- trigger (GetReg v) ;;
        if val:nat then ret y else ret n
      | Bhalt => exit
      | BAbort => x <- trigger CAbort;; match x:void with end
      end.

    (** The denotation of a basic [block] shares the same type, returning the
        [label] of the next [block] it shall jump to.  It recursively denote
        its instruction before that.  *)
    Fixpoint denote_bk {B} (b : block B) : itree E B :=
      match b with
      | bbi i b =>
        denote_instr i ;; denote_bk b
      | bbb b =>
        denote_br b
      end.

    (** A labelled collection of blocks, [bks], is simply the pointwise
        application of [denote_bk].  Crucially, its denotation is therefore
        a [ktree], whose structure will be useful in the proof of
        the compiler.

        The type [sub (ktree E) fin A B] is shorthand for
        [fin A -> itree E (fin B)], and we can think of them as "continuations"
        with events in E, with input values in [fin A] and output values in [fin B].
        They have a nice algebraic structure, supported by the library,
        including a [loop] combinator that we can use to link collections of
        basic blocks. (See below.) *)
    Definition denote_bks {A B : nat} (bs: bks A B): sub (ktree E) fin A B :=
      fun a => denote_bk (bs a).

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
    Definition denote_asm {A B} : asm A B -> sub (ktree E) fin A B :=
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

Definition map_reg {E G: Type -> Type} `{mapE reg 0 +? G -< E}
  : Reg ~> itree E :=
  fun _ e =>
    match e with
    | GetReg x => lookup_def x
    | SetReg x v => insert x v
    end.

Definition map_memory {E G : Type -> Type} `{mapE addr 0 +? G -< E} :
  Memory ~> itree E :=
  fun _ e =>
    match e with
    | Load x => lookup_def x
    | Store x v => insert x v
    end.

Definition handle_abort
           {E: Type -> Type}: Abort ~> failT (itree E) :=
  fun _ e =>
    match e with
    | CAbort => ret None
    end.

(** Once again, we implement our Maps with a simple association list *)
Definition registers := alist reg value.
Definition memory    := alist addr value.

(** The _asm_ interpreter takes as inputs a starting heap [mem] and register
    state [reg] and interprets an itree in two nested instances of the [map]
    variant of the state monad. To get this type to work out, we have to
    do a bit of post-processing to swap the order of the "state components"
    introduced by the interpretation.
 *)

Definition interp_asm_regs {E A C} `{Reg +? C -< E}
           (t: itree E A) : registers -> itree C (registers * A) :=
  interp_map (interp (over map_reg) t).

Definition interp_asm_mem {E A C} `{Memory +? C -< E}
           (t: itree E A) : memory -> itree C (memory * A) :=
  interp_map (interp (over map_memory) t).

Definition interp_asm_fail {E F A}
           `{Abort +? E -< F} (t : itree F A) : failT (itree E) A:=
  (interp (over handle_abort) t).

(* YZ: NOTE: Notice the mention of the successive contexts.
   A formulation of the form `Reg +' Memory +? C -< E` would both
   require another instance that is prone to looping (see [Subevent_to_complement]),
   as well as would fix the order in which Memory and Reg have to appear
 *)

(* YZ: NOTE: This style naturally leads to compose two interpreters.
   In contrast, the previous definition interpreted once the bimap of
   two handlers.
 *)
Definition interp_asm {C D E F A} `{Memory +? C -< D} `{Reg +? D -< E} `{Abort +? E -< F}
           (t : itree F A) : memory -> registers -> failT (itree C) (memory * (registers * A)) :=
  fun mem regs => let t' := interp_asm_regs t regs in
                  let t'' := interp_asm_mem t' mem in
                  interp_asm_fail t''.

Arguments interp_asm_mem /.
Arguments interp_asm_fail /.
Arguments interp_asm /.

(** We can then define an evaluator for closed assembly programs by interpreting
    both store and heap events into two instances of [mapE], and running them
    both in the empty initial environments.  *)
(** The definition [interp_asm] also induces a notion of equivalence (open)
    _asm_ programs, which is just the equivalence of the ktree category *)
Definition eq_asm_denotations {A B C D E F}
           `{Memory +? C -< D} `{Reg +? D -< E} `{Abort +? E -< F}
           (t1 t2 : Kleisli (itree F) A B) : Prop
    :=
  forall a mem regs, interp_asm (t1 a) mem regs ≈ interp_asm (t2 a) mem regs.

Definition eq_asm {A B C D E F G} `{Memory +? C -< D} `{Reg +? D -< E} `{Abort +? E -< F} `{Exit +? F -< G} 
           (p1 p2 : asm A B) : Prop :=
      eq_asm_denotations (denote_asm p1) (denote_asm p2).

Section InterpAsmProperties.

  Context {E C1 C2 C3 : Type -> Type}.
  Context {HasMemory : Memory +? C1 -< C2}.
  Context {HasReg : Reg +? C2 -< C3}.
  Context {HasAbort : Abort +? C3 -< E}.

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_asm {R}:
    Proper (eutt eq ==> eq ==> eq ==> eutt eq) (interp_asm (A := R)).
  Proof.
    repeat intro.
    unfold interp_asm.
    unfold interp_asm_mem.
    unfold interp_asm_regs.
    rewrite H.
    rewrite H0.
    rewrite H1.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [Ret]. *)
  Lemma interp_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory),
      @eutt C2 _ _ eq (interp_asm (ret r) mem regs)
            (ret (Some (mem, (regs, r)))).
  Proof.
    unfold interp_asm, interp_asm_mem, interp_asm_regs, interp_map.
    intros.
    unfold ret at 1, Monad_itree.
    rewrite interp_ret.
    rewrite interp_state_ret.
    rewrite interp_ret.
    rewrite interp_state_ret. cbn.
    setoid_rewrite interp_fail_ret.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (regs : registers) (mem: memory),
      interp_asm (ITree.bind t k) mem regs ≈
          ('(mem', (regs', x)) <- interp_asm t mem regs ;; interp_asm (k x) mem' regs').

  Proof.
    intros.
    unfold interp_asm, interp_asm_mem, interp_asm_regs, interp_map.
    About interp_bind.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind. cbn.
    setoid_rewrite interp_fail_bind.
    eapply eutt_clo_bind.
    { reflexivity. }
    intros.
    destruct u1 as [(? & ?)|], u2 as [(? & ?)|]; inv H;  [ | reflexivity].
    destruct p0.
    reflexivity.
  Qed.

End InterpAsmProperties.

(** Now that we have both our language, we could jump directly into implementing
our compiler.  However, if we look slightly ahead of us, we can observe that: -
compiling expressions and basic statements will be mostly straightforward; - but
linking the resulting elementary (open) [asm] programs together is not as
trivial. In particular, reasoning inductively on this linking is more
challenging.  We therefore take a detour: we first reason in isolation about
linking, and to this end we jump to [AsmCombinators.v].  *)
