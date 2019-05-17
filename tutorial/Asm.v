(** * The Asm language  *)

(** We now consider as a target a simple control-flow-graph language,
    so-called _Asm_.
    Computations are represented as a collection of basic blocks
    linked by jumps.
 *)

(* begin hide *)
From Coq Require Import
     Strings.String
     Program.Basics
     ZArith.ZArith
     Morphisms
     Setoid
     RelationClasses.


From ITree Require Import
     ITree
     ITreeFacts
     Events.Map
     StateFacts.

From ExtLib Require Structures.Monad.

Require Import Imp.

Typeclasses eauto := 5.

(* end hide *)

(* ================================================================= *)
(** ** Syntax *)

(** Once again, a countable set of variables represented as [string]s: *)
Definition var : Set := string.
(** For simplicity, _Asm_ manipulates [nat]s as values too. *)
Definition value : Set := nat. 

(** We consider constants and variables as operands. *)
Variant operand : Set :=
| Oimm (_ : value)
| Ovar (_ : var).

(** The instruction set covers moves and arithmetic operations,
    as well as load and stores to the heap.
 *)
Variant instr : Set :=
| Imov (dest : var) (src : operand)
| Iadd (dest : var) (src : var) (o : operand)
| Isub (dest : var) (src : var) (o : operand)
| Imul (dest : var) (src : var) (o : operand)
| Iload (dest : var) (addr : var)
| Istore (addr : var) (val : operand).

(** We consider both direct and conditional jumps *)
Variant branch {label : Type} : Type :=
| Bjmp (_ : label)                (* jump to label *)
| Bbrz (_ : var) (yes no : label) (* conditional jump *)
| Bhalt
.
Global Arguments branch _ : clear implicits.

(** A basic [block] is a sequence of straightline instructions
    followed by a branch that either halts the execution,
    or transfers control to another [block]. *)
Inductive block {label : Type} : Type :=
| bbi (_ : instr) (_ : block)
| bbb (_ : branch label).
Global Arguments block _ : clear implicits.

(** A piece of code should expose the set of labels allowing to enter
    into it, as well as the set of outer labels it might jump to.
    To this end, [bks] represents a collection of blocks labeled
    by [A], with branches in [B]. *)
Definition bks (A B: Type) := A -> block B.

(** An [asm] program represents the control flow of the computation.
    It is a collection of labelled [blocks] such that its labels are
    classified into three categories:
    - [A]: (visible) entry points
    - [B]: (visible) exit points
    - [internal]: (hidden) internal linked labels
    Note that they uniformely represent open and closed programs,
    the latter corresponding to an [asm] program with a unique entry
    point and always halting, i.e. a [asm unit void].
 *)
Record asm (A B: Type) : Type :=
  {
    internal : Type;
    code : bks (internal + A) (internal + B)
  }.

Arguments internal {A B}.
Arguments code {A B}.

(* ================================================================= *)
(** ** Semantics *)

(** _Asm_ produces two kind of events: through manipulation of the 
    local store and of the heap.
*)
Variant Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.

Inductive Memory : Type -> Type :=
| Load (addr : var) : Memory value
| Store (addr : var) (val : value) : Memory unit.

Section Denote.

  (** Once again, [asm] programs shall be denoted as [itree]s. *)

  (* begin hide *)
  Import ExtLib.Structures.Monad.
  Import MonadNotation.
  Local Open Scope monad_scope.
  (* end hide *)

  (** We introduce a special event to model termination of the computation.
      Note that it expects _actively_ no answer from the environment: 
      [Done] is of type [Exit void].
      We can therefore use it to "close" an [itree E A] no matter what the expected
      return type [A] is, as witnessed by the [done] computation.
   *)
  Inductive Exit : Type -> Type :=
  | Done : Exit void.

  Definition done {E A} `{Exit -< E} : itree E A :=
    vis Done (fun v => match v : void with end).

  Section with_event.

    (** As with _Imp_, we parameterize our semantics by a universe of events
        that shall encompass all the required ones.
     *)
    Context {E : Type -> Type}.
    Context {HasLocals : Locals -< E}.
    Context {HasMemory : Memory -< E}.
    Context {HasExit : Exit -< E}.

    (** Operands are trivially denoted as [itree]s returning values *)
    Definition denote_operand (o : operand) : itree E value :=
      match o with
      | Oimm v => Ret v
      | Ovar v => trigger (GetVar v)
      end.

    (** Instructions offer no suprises either. *)
    Definition denote_instr (i : instr) : itree E unit :=
      match i with
      | Imov d s =>
        v <- denote_operand s ;;
        trigger (SetVar d v)
      | Iadd d l r =>
        lv <- trigger (GetVar l) ;;
        rv <- denote_operand r ;;
        trigger (SetVar d (lv + rv))
      | Isub d l r =>
        lv <- trigger (GetVar l) ;;
        rv <- denote_operand r ;;
        trigger (SetVar d (lv - rv))
      | Imul d l r =>
        lv <- trigger (GetVar l) ;;
        rv <- denote_operand r ;;
        trigger (SetVar d (lv * rv))
      | Iload d addr =>
        val <- trigger (Load addr) ;;
        trigger (SetVar d val)
      | Istore addr v =>
        val <- denote_operand v ;;
        trigger (Store addr val)
      end.

    Section with_labels.
      Context {A B : Type}.

      (** A [branch] returns the computed label whose set of possible
          values [B] is carried by the type of the branch.
          If the computation halts instead of branching,
          we return the [done] tree.
       *)
      Definition denote_branch (b : branch B) : itree E B :=
        match b with
        | Bjmp l => ret l
        | Bbrz v y n =>
          val <- trigger (GetVar v) ;;
          if val:nat then ret y else ret n
        | Bhalt => done
        end.

      (** The denotation of a basic [block] shares the same type,
          returning the [label] of the next [block] it shall jump to.
          It recursively denote its instruction before that.
       *)
      Fixpoint denote_block (b : block B) : itree E B :=
        match b with
        | bbi i b =>
          denote_instr i ;; denote_block b
        | bbb b =>
          denote_branch b
        end.

      (** A labelled collection of blocks, [bks], is simply the pointwise
          application of [denote_block].
          However, its denotation is therefore crucially a [ktree],
          whose structure will be useful in the proof of the compiler.
       *)
      Definition denote_b (bs: bks A B): ktree E A B :=
        fun a => denote_block (bs a).

    End with_labels.

  (** One can think of an [asm] program as a circuit/diagram where wires
      correspond to jumps/program links.
      [denote_b] computes the meaning of each basic block as an [itree] that
      returns the label of the next block to jump to, laying down all our
      elementary wires. 
      In order to denote an [asm A B] program as a [ktree E A B], it therefore
      remains to wire all those denoted blocks together while hiding the
      internal labels.
      Luckily, that is exactly what traced monoidal category are good for.
      We therefore accomplish this with the same [loop] combinator we used to
      denote _Imp_'s [while] loop.
      It directly takes our [denote_b (code s): ktree E (I + A) (I + B)] and
      hides [I] as desired.
   *)

    (* Denotation of [asm] *)
    Definition denote_asm {A B} : asm A B -> ktree E A B :=
      fun s => KTree.loop (denote_b (code s)).

  End with_event.
End Denote.

(* ================================================================= *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Basics.Category
     Events.Map.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
(* end hide *)

(** Both environments and memory events can be interpreted as "map" events,
    exactly as we did for _Imp_. *)

Definition evalLocals {E: Type -> Type} `{mapE var value -< E}: Locals ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x 0
    | SetVar x v => insert x v
    end.


Definition evalMemory {E : Type -> Type} `{mapE var value -< E} :
  Memory ~> itree E :=
  fun _ e =>
    match e with
    | Load x => lookup_def x 0
    | Store x v => insert x v
    end.

(** Once again, we implement our Maps with a simple association list *)
Definition memory := alist var value.

Definition interp_asm {E A} (t : itree (Locals +' Memory +' E) A) globals locals : itree E (memory * (memory * A)) :=
  let h := bimap evalLocals (bimap evalMemory (id_ _)) in                             
  let t' := interp h t in
  run_map (run_map t' locals) globals.
  
(** We can then define an evaluator for closed assembly programs by
    interpreting both store and heap events into two instances of [mapE],
    and running them both in the empty initial environments.
 *)
Definition AsmEval (p: asm unit void) :=
  interp_asm (denote_asm p tt) empty empty.

Section InterpAsmProperties.
  Context {E': Type -> Type}.
  Notation E := (Locals +' Memory +' E').

  (* (** [interp_locals] handle [Locals] into the [mapE] events, and then *)
  (*     run these events into the state monad. *) *)
  (* Definition interp_locals {R: Type} (t: itree E R) (s: alist var value) *)
  (*   : itree E' (alist var value * R) := *)
  (*   run_map (interp (bimap evalLocals (id_ _)) t) s. *)

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_asm {R}:
    Proper (@eutt E R R eq ==> eq ==> eq ==> @eutt E' (prod (memory) (prod (memory) R)) (prod _ (prod _ R)) eq)
           interp_asm.
  Proof.
    repeat intro.
    unfold interp_asm.
    unfold run_map.
    rewrite H0. eapply eutt_interp_state; auto.
    rewrite H1. rewrite H. reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (l g: memory),
      @eutt E' _ _ eq
            (interp_asm (ITree.bind t k) g l)
            (ITree.bind (interp_asm t g l) (fun '(g', (l', x)) => interp_asm (k x) g' l')).
  Proof.
    intros.
    unfold interp_asm.
    unfold run_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    apply eutt_bind. red. intros.
    destruct a as [g' [l' x]].
    simpl.
    reflexivity.
    reflexivity.
  Qed.

End InterpAsmProperties.

(** Now that we have both our language, we could jump directly into implementing
    our compiler.
    However, if we look slightly ahead of us, we can observe that:
    - compiling expressions and basic statements will be mostly straightforward;
    - but linking the resulting elementary (open) [asm] programs together is not
    as trivial. In particular, reasoning inductively on this linking is more
    challenging.
    We therefore take a detour: we first reason in isolation about linking, and
    to this end we jump to [AsmCombinators.v].
 *)
