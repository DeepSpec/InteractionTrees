(** * The Asm language  *)

(** We now consider as a target a simple control-flow-graph language, so-called
    _Asm_.  Computations are represented as a collection of basic blocks linked
    by jumps.  *)

(* begin hide *)
From Coq Require Import Arith String Setoid.

  (* SAZ: Should we add ITreeMonad to ITree? *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.CategorySub
     Events.State
     Events.Exception
.

Require Import Lattice LabelledImp.
Require Import Fin.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
(* end hide *)

Variant sensitivity : Type :=
  | Public
  | Private.

Definition meet_sense l1 l2 :=
  match l1 with
  | Public => Public
  | Private => l2 end.

Definition join_sense l1 l2 :=
  match l1 with
  | Public => l2
  | Private => Private end.

#[global]
Instance sensitivity_lat : Lattice :=
  {|
  T := sensitivity;
  eqlat := eq;
  join := join_sense;
  meet := meet_sense;
  top := Private;
  bot := Public

  |}.

#[global]
Instance sensitivity_latlaws : LatticeLaws sensitivity_lat.
Proof.
  constructor.
  - apply eq_equivalence.
  - unfold eqlat. cbn. repeat intro. subst. auto.
  - unfold eqlat. cbn. repeat intro. subst. auto.
  - intros l1 l2. cbn. destruct l1; destruct l2; eauto; right; intro; discriminate.
  - cbn. intros [ | ] [ | ]; auto.
  - cbn. intros [ | ] [ | ] [| ]; auto.
  - cbn. intros [ | ] [ | ]; auto.
  - cbn. intros [ | ] [ | ] [| ]; auto.
  - cbn. intros [ | ]; auto.
  - cbn. intros [ | ]; auto.
  - cbn. intros [ | ] [ | ]; auto.
  - cbn. intros [ | ] [ | ]; auto.
Qed.
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
| BRaise (s : sensitivity)
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
    (* Context (Labels : Lattice). *)
    (* could use a slight generalization sensitivity_lat to Lattice *)

    (** As with _Imp_, we parameterize our semantics by a universe of events
        that shall encompass all the required ones. *)
    Context {E : Type -> Type}.
    Context {HasExc : impExcE sensitivity_lat -< E}.
    Context {HasReg : Reg -< E}.
    Context {HasMemory : Memory -< E}.
    Context {HasIOE : IOE sensitivity_lat -< E}.

    Arguments LabelledPrint {Labels}.
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
      | BRaise s => v <- trigger (Throw s);; match v : void with end
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
(* SAZ: Annoyingly, typeclass resolution picks the wrong map instance for nats by default, so
   we create an instance for [reg] that hides the wrong instance with the right one. *)
#[global]
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

Definition asm_handler {E1 E2} : (E1 +' Reg +' Memory +' E2) ~> stateT (registers * memory) (itree (E1 +' E2)) :=
  fun _ e => match e with
          | inr1 (inl1 reg_e) => h_reg _ reg_e
          | inr1 (inr1 (inl1 mem_e)) =>  h_mem _ mem_e
          | inl1 e' =>  (fun s => v <- ITree.trigger (inl1 e') ;; Ret (s, v))
          | inr1 (inr1 (inr1 e')) =>  (fun s => v <- ITree.trigger (inr1 e') ;; Ret (s, v))

end.

Definition interp_asm {E1 E2 A} (t : itree (E1 +' Reg +' Memory +' E2) A ) :
  stateT (registers * memory) (itree (E1 +' E2)) A :=
  fun '(mem, regs) => interp_state asm_handler t (mem, regs).
