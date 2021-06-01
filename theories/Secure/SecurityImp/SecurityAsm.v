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
     Secure.SecurityImp.Fin
     Secure.SecurityImp.SecurityImp
.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
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
| IEq    (dest : reg) (src : reg) (o : operand)
| ILe    (dest : reg) (src : reg) (o : operand)
| IAnd   (dest : reg) (src : reg) (o : operand)
| INot   (dest : reg) (o : operand)
| Iload  (dest : reg) (addr : addr)
| Istore (addr : addr) (val : operand)
| IOutput (s : sensitivity) (src : reg)
.

(** We consider both direct and conditional jumps *)
Variant branch {label : Type} : Type :=
| Bjmp (_ : label)                (* jump to label *)
| Bbrz (_ : reg) (yes no : label) (* conditional jump *)
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
    Context {E : Type -> Type}.
    Context {HasReg : Reg -< E}.
    Context {HasMemory : Memory -< E}.
    Context {HasIOE : IOE -< E}.

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
      | IEq d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (if Nat.eqb lv rv then 1 else 0))
      | ILe d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (if Nat.leb lv rv then 1 else 0))
      | INot d r =>
        rv <- denote_operand r ;;
        trigger (SetReg d (match rv with | 0 => 1 | _ => 0 end))
      | IAnd d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (match lv,rv with | 0,0 | 0,1 | 1,0 => 0 | _,_ => 1 end))
      | Iload d addr =>
        val <- trigger (Load addr) ;;
            trigger (SetReg d val)
      | Istore addr v =>
        val <- denote_operand v ;;
            trigger (Store addr val)
      | IOutput s r =>
        val <- trigger (GetReg r);;
            trigger (LabelledPrint s val)
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
(*
Definition h_reg {E: Type -> Type}
  : Reg ~> stateT (itree E) :=
  fun _ e s =>
    match e with
    | GetReg x => lookup_def x
    | SetReg x v => insert x v
    end.

Definition h_memory {E : Type -> Type} `{mapE addr 0 -< E} :
  Memory ~> itree E :=
  fun _ e =>
    match e with
    | Load x => lookup_def x
    | Store x v => insert x v
    end.
*)
(** Once again, we implement our Maps with a simple association list *)
Definition registers := nat -> value.
Definition memory    := map.

Definition get_reg (n : nat) (s : registers) := s n.
Definition update_reg (n : nat) (v : value) (s : registers) :=
  fun m => if n =? m then v else s m.

Definition h_reg {E : Type -> Type} : Reg ~> stateT (registers * memory) (itree E) :=
  fun _ e => match e with
          | GetReg n => fun '(regs,mem) => Ret (regs, mem, get_reg n regs)
          | SetReg n v => fun '(regs, mem) => Ret (update_reg n v regs, mem, tt) end.

Definition h_mem {E : Type -> Type} : Memory ~> stateT (registers * memory) (itree E) :=
  fun _ e => match e with 
          | Load x => fun '(regs,mem) => Ret (regs, mem, get x mem)
          | Store x v => fun '(regs, mem) => Ret (regs, update x v mem, tt) end.

Definition asm_handler {E} : (Reg +' Memory +' E) ~> stateT (registers * memory) (itree E) :=
  fun _ e => match e with 
          | inl1 reg_e => h_reg _ reg_e
          | inr1 e' => match e' with 
                      | inl1 mem_e => h_mem _ mem_e
                      | inr1 e'' => (fun s => v <- ITree.trigger e'' ;; Ret (s, v)) end end.

Definition interp_asm {E A} (t : itree (Reg +' Memory +' E) A ) : 
  stateT (registers * memory) (itree E) A :=
  fun '(mem, regs) => interp_state asm_handler t (mem, regs).
(*

(** The _asm_ interpreter takes as inputs a starting heap [mem] and register
    state [reg] and interprets an itree in two nested instances of the [map]
    variant of the state monad. To get this type to work out, we have to
    do a bit of post-processing to swap the order of the "state components"
    introduced by the interpretation.
*)
Definition interp_asm {E A} (t : itree (Reg +' Memory +' E) A) :
  memory -> registers -> itree E (memory * (registers * A)) :=
  let h := bimap h_reg (bimap h_memory (id_ _)) in
  let t' := interp h t in
  fun  mem regs => interp_map (interp_map t' regs) mem.


(** We can then define an evaluator for closed assembly programs by interpreting
    both store and heap events into two instances of [mapE], and running them
    both in the empty initial environments.  *)
Definition run_asm (p: asm 1 0) := interp_asm (denote_asm p Fin.f0) empty empty.

(* SAZ: Should some of thes notions of equivalence be put into the library?
   SAZ: Should this be stated in terms of ktree ?
 *)
(** The definition [interp_asm] also induces a notion of equivalence (open)
    _asm_ programs, which is just the equivalence of the ktree category *)
Definition eq_asm_denotations {E A B} (t1 t2 : Kleisli (itree (Reg +' Memory +' E)) A B) : Prop :=
  forall a mem regs, interp_asm (t1 a) mem regs ≈ interp_asm (t2 a) mem regs.

Definition eq_asm {A B} (p1 p2 : asm A B) : Prop :=
  eq_asm_denotations (denote_asm p1) (denote_asm p2).

Section InterpAsmProperties.

  Context {E': Type -> Type}.
  Notation E := (Reg +' Memory +' E').

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_asm {R}:
    Proper (@eutt E R R eq ==> eq ==> eq ==> @eutt E' (prod memory (prod registers R)) (prod _ (prod _ R)) eq) interp_asm.
  Proof.
    repeat intro.
    unfold interp_asm.
    unfold interp_map.
    rewrite H0.
    rewrite H.
    rewrite H1.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [Ret]. *)
  Lemma interp_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory),
      @eutt E' _ _ eq (interp_asm (ret r) mem regs)
            (ret (mem, (regs, r))).
  Proof.
    unfold interp_asm, interp_map.
    intros.
    unfold ret at 1, Monad_itree.
    rewrite interp_ret, 2 interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (regs : registers) (mem: memory),
      @eutt E' _ _ eq (interp_asm (ITree.bind t k) mem regs)
            (ITree.bind (interp_asm t mem regs) (fun '(mem', (regs', x)) => interp_asm (k x) mem' regs')).

  Proof.
    intros.
    unfold interp_asm.
    unfold interp_map. cbn.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    repeat rewrite Eq.bind_bind.
    eapply eutt_clo_bind.
    { reflexivity. }
    intros.
    rewrite H.
    destruct u2 as [g' [l' x]].
    reflexivity.
  Qed.

End InterpAsmProperties.
*)
(** Now that we have both our language, we could jump directly into implementing
our compiler.  However, if we look slightly ahead of us, we can observe that: -
compiling expressions and basic statements will be mostly straightforward; - but
linking the resulting elementary (open) [asm] programs together is not as
trivial. In particular, reasoning inductively on this linking is more
challenging.  We therefore take a detour: we first reason in isolation about
linking, and to this end we jump to [AsmCombinators.v].  *)
