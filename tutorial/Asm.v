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

From ITree Require Import
     ITree
     ITreeFacts
     ITreeMonad
     Basics.Monad
     Basics.CategorySub
     Events.State
     Events.StateFacts
     Eq.Eq.

From ITreeTutorial Require Import Fin Utils_tutorial.

Require Import Imp.
Import Monads.
(* end hide *)

(** ** Syntax *)

(** We define a countable set of memory addresses, represented as [string]s: *)
Definition addr : Set := string.

(** We define a set of register names (for this simple example, we identify them
with [nat]). *)
Definition reg : Set := nat.

(** For simplicity, _Asm_ manipulates [nat]s as values and function id's too. *)
Definition value : Set := nat.
Definition func : Set := nat.

(** We consider constants and variables as operands. *)
(* The operands also include [Ocall], which denote external calls. *)
Variant operand : Set :=
| Oimm (_ : value)
| Oreg (_ : reg)
| Ocall (f: func).

(** The instruction set covers moves and arithmetic operations, as well as load
    and stores to the heap.  *)
Variant instr : Set :=
| Imov   (dest : reg) (src : operand)
| Iadd   (dest : reg) (src : reg) (o : operand)
| Isub   (dest : reg) (src : reg) (o : operand)
| Imul   (dest : reg) (src : reg) (o : operand)
| Iload  (dest : reg) (addr : addr)
| Istore (addr : addr) (val : operand)
.

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
Variant Reg : Type -> Type :=
| GetReg (x : reg) : Reg value
| SetReg (x : reg) (v : value) : Reg unit.

Inductive Memory : Type -> Type :=
| Load  (a : addr) : Memory value
| Store (a : addr) (val : value) : Memory unit.

(* The events for external calls. *)
Inductive FnCall : Type -> Type :=
| Call (f : func) : FnCall value.

(** We also introduce a special event to model termination of the computation.
    Note that it expects _actively_ no answer from the environment: [Done] is
    of type [Exit void].  We can therefore use it to "close" an [itree E A] no
    matter what the expected return type [A] is, as witnessed by the [exit]
    computation.  *)
Inductive Exit : Type -> Type :=
| Done : Exit void.

Definition exit {E A} `{Exit -< E} : itree E A :=
  vis Done (fun v => match v : void with end).


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
    Context {HasExit : Exit -< E}.
    Context {HasCall : FnCall -< E}.

    (** Operands are trivially denoted as [itree]s returning values *)
    Definition denote_operand (o : operand) : itree E value :=
      match o with
      | Oimm v => Ret v
      | Oreg v => trigger (GetReg v)
      | Ocall f => trigger (Call f)
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
    Definition denote_branch {B} (b : branch B) : itree E B :=
      match b with
      | Bjmp l => ret l
      | Bbrz v y n =>
        val <- trigger (GetReg v) ;;
        if val:nat then ret y else ret n
      | Bhalt => exit
      end.

    (** The denotation of a basic [block] shares the same type, returning the
        [label] of the next [block] it shall jump to.  It recursively denote
        its instruction before that.  *)
    Fixpoint denote_bk {B} (b : block B) : itree E B :=
      match b with
      | bbi i b =>
        denote_instr i ;; denote_bk b
      | bbb b =>
        denote_branch b
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

Instance RelDec_reg : RelDec (@eq reg) := RelDec_from_dec eq Nat.eq_dec.
(* end hide *)

(** Both environments and memory events can be interpreted as "map" events,
    exactly as we did for _Imp_. *)

Definition h_reg {E: Type -> Type} `{mapE reg 0 -< E}
  : Reg ~> itree E :=
  fun _ e =>
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

Definition h_E {E F} `{mapE addr 0 -< F} `{E -< F} : E ~> itree F :=
  fun R e => trigger e.

(** Once again, we implement our Maps with a simple association list *)
Definition registers := alist reg value.
Definition memory    := alist addr value.

(** The _asm_ interpreter takes as inputs a starting heap [mem] and register
    state [reg] and interprets an itree in two nested instances of the [map]
    variant of the state monad. To get this type to work out, we have to
    do a bit of post-processing to swap the order of the "state components"
    introduced by the interpretation.
*)

(* The [FnCall] is interpreted entirely into the [memory] state after having
  knowledge about the external call handler. *)
Definition later_interp_asm {E : Type -> Type} {A : Type} ext_handler
           (t : itree (Reg +' Memory +' FnCall +' E) A):
    memory -> registers -> itree E (memory * (registers * A)) :=
  let t' := interp (bimap h_reg (case_ h_memory (case_ h_E h_E))) t in
  fun  mem regs => later_interp_map ext_handler (interp_map t' regs) mem.

(** We can then define an evaluator for closed assembly programs by interpreting
    both store and heap events into two instances of [mapE], and running them
    both in the empty initial environments.  *)
Definition later_run_asm (p: asm 1 0) ext_handler := later_interp_asm ext_handler (denote_asm p Fin.f0) empty empty.

(** The definition [interp_asm] also induces a notion of equivalence (open)
    _asm_ programs, which is just the equivalence of the ktree category *)
Definition eq_asm_denotations {E A B} (t1 t2 : Kleisli (itree (Reg +' Memory +' FnCall +' E)) A B) : Prop :=
  forall a mem regs ext, later_interp_asm ext (t1 a) mem regs ≈ later_interp_asm ext (t2 a) mem regs.

Definition eq_asm {A B} (p1 p2 : asm A B) : Prop :=
  eq_asm_denotations (denote_asm p1) (denote_asm p2).

Section LaterInterpAsmProperties.

  Context {F: Type -> Type}.
  Notation E := (Reg +' Memory +' FnCall +' F).
  Notation E' := (FnCall +' F).

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_later_interp_asm {R} h:
    Proper (@eutt E R R eq ==> eq ==> eq ==> @eutt F (prod memory (prod registers R)) (prod _ (prod _ R)) eq)
           (later_interp_asm h).
  Proof.
    repeat intro.
    unfold later_interp_asm.
    unfold interp_map.
    rewrite H0.
    rewrite H.
    rewrite H1.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [Ret]. *)
  Lemma later_interp_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory) ext,
      @eutt E' _ _ eq (later_interp_asm ext (ret r) mem regs)
            (ret (mem, (regs, r))).
  Proof.
    unfold later_interp_asm, later_interp_map, interp_map.
    intros.
    unfold ret at 1, Monad_itree.
    rewrite interp_ret, 2 interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma later_interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (regs : registers) (mem: memory) ext,
      @eutt F _ _ eq (later_interp_asm ext (ITree.bind t k) mem regs)
            (ITree.bind (later_interp_asm ext t mem regs) (fun '(mem', (regs', x)) => later_interp_asm ext (k x) mem' regs')).
  Proof.
    intros.
    unfold later_interp_asm.
    unfold later_interp_map, interp_map. cbn.
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

  (* Given a trigger of an external call, now we can state that an arbitrary
    implementation of an external function does may change the memory. *)
  Definition ext_call f : itree E value := (trigger (Call f)).

  (* As a degenerate example, let's say that we have knowledge about the external
    calls, specifically that any external call will modify the memory by adding
    a "foo" address *)
  Definition handle_call {E : Type -> Type} `{mapE addr 0 -< E} :
    FnCall ~> itree E :=
    fun _ e =>
      match e with
      | Call x => (ITree.bind (insert "foo"%string 3) (fun _ => Ret 3))
      end.

  (* This is the corresponding [handler] that is the external call implementation. *)
  Definition call_modifies_mem : (FnCall +' F) ~> stateT memory (itree F).
    intros.
    eapply interp_map.
    pose (case_ handle_call (h_E (E := F))). eapply h. eapply X.
  Defined.

  (* Now, we can show that we can indeed give an instance of a handler for an
    external function such that the resulting memory is not equivalent to the initial
    memory. *)
  Lemma external_call_can_affect_memory:
    forall regs f,
    exists ext mem,
      (eutt (fun '(mem', _) _ => mem <> mem')
            (later_interp_asm ext (ext_call f) mem regs)
            (later_interp_asm ext (ext_call f) mem regs)).
  Proof.
    intros. exists call_modifies_mem, nil.
    subst.
    unfold later_interp_asm, later_interp_map, interp_map.
    unfold ext_call.
    setoid_rewrite interp_trigger. cbn.
    unfold cat, Cat_Handler, Handler.cat.
    cbn. unfold resum, ReSum_id, id_, Id_IFun.
    unfold h_E.
    setoid_rewrite interp_trigger.
    unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
    unfold ITree.trigger.
    rewrite interp_state_vis. rewrite interp_state_bind. cbn.
    unfold pure_state. rewrite interp_state_bind. rewrite bind_bind.
    setoid_rewrite tau_eutt. do 2 setoid_rewrite interp_state_ret.
    replace
      (fun st : memory * (registers * value) => Ret (fst st, (fst (snd st), snd (snd st)))) with
      (fun st => {| _observe := RetF (E := F) (R := memory * (registers * value)) st |}).
    2 : {
      eapply FunctionalExtensionality.functional_extensionality.
      intros. destruct x, p. cbn; auto.
    }
    rewrite interp_state_trigger. setoid_rewrite bind_ret_l.
    unfold call_modifies_mem. cbn.
    unfold interp_map. rewrite interp_state_bind. rewrite bind_bind.
    unfold insert. unfold embed, Embeddable_forall, embed, Embeddable_itree.
    rewrite interp_state_trigger. cbn. rewrite bind_ret_l.
    rewrite interp_state_ret. rewrite bind_ret_l.
    cbn.
    apply eqit_Ret.
    intro. unfold alist_add in H;cbn in H. inv H.
  Qed.

End LaterInterpAsmProperties.

(* NEXT: There still remains the question of how to specify the behavior of
  arbitrary external calls, given this formulation.

  One strategy could be interpreting into some kind of
      stateT (Predicate about state) (itree E) R
  where we can now state predicates about states using Iris.

  The above type would unfold to ...
      (S -> iProp) -> itree E ((S -> iProp) * R)
 *)

(* What if we want to introduce another kind of effect as part of the
  interpretation for [FnCall]?

  "Partial interpretation" of events (kind of a weird idea.. )
 *)
Section PartialInterpAsmProperties.

  (* The interpretation is "partial", as it expects a handler input [h] which is
    corresponds to the implementation of the external call. The [FnCall] affects
    [memory], but may also have another effect that we can interpret. *)
  Definition partial_interp_asm {E : Type -> Type} {A : Type} ext_handler
            (t : itree (Reg +' Memory +' FnCall +' E) A):
      memory -> registers -> itree (FnCall +' E) (memory * (registers * A)) :=
    let t' := interp (bimap h_reg (case_ h_memory (case_ h_E h_E))) t in
    fun  mem regs => partial_interp_map ext_handler (interp_map t' regs) mem.

  (* Notice that the return type of [partial_run_asm] still has an [FnCall] event left,
    thus corresponding to a partial interpretation of the program. *)
  Definition partial_run_asm (p: asm 1 0) ext_handler := partial_interp_asm ext_handler (denote_asm p Fin.f0) empty empty.
    Context {F: Type -> Type}.
    Notation E := (Reg +' Memory +' FnCall +' F).
    Notation E' := (FnCall +' F).

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_partial_interp_asm {R} h:
    Proper (@eutt E R R eq ==> eq ==> eq ==> @eutt E' (prod memory (prod registers R)) (prod _ (prod _ R)) eq)
           (partial_interp_asm h).
  Proof.
    repeat intro.
    unfold partial_interp_asm.
    unfold interp_map.
    rewrite H0.
    rewrite H.
    rewrite H1.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [Ret]. *)
  Lemma interp_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory) ext,
      @eutt E' _ _ eq (partial_interp_asm ext (ret r) mem regs)
            (ret (mem, (regs, r))).
  Proof.
    unfold partial_interp_asm, partial_interp_map, interp_map.
    intros.
    unfold ret at 1, Monad_itree.
    rewrite interp_ret, 2 interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (regs : registers) (mem: memory) ext,
      @eutt E' _ _ eq (partial_interp_asm ext (ITree.bind t k) mem regs)
            (ITree.bind (partial_interp_asm ext t mem regs)
                        (fun '(mem', (regs', x)) => partial_interp_asm ext (k x) mem' regs')).
  Proof.
    intros.
    unfold partial_interp_asm.
    unfold partial_interp_map, interp_map. cbn.
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

  Import ITreeNotations.
  Import MonadNotation.
  Open Scope monad_scope.

  (* As a simple example, this external call handler is going to modify the
     memory by adding a "foo" address, while still keeping the [Call] trigger. *)
  Definition partial_handle_call : FnCall ~> itree (mapE addr 0 +' FnCall +' F) :=
    fun _ e =>
      match e with
      | Call x => v <- trigger (Call x);; (insert "foo"%string v) ;; Ret v
      end.

  (* This is the corresponding [handler] that is the external call implementation. *)
  Definition call_modifies_mem' : (FnCall +' F) ~> stateT memory (itree (FnCall +' F)).
    intros.
    eapply interp_map.
    pose (case_ partial_handle_call (h_E (E := F))). eapply h. eapply X.
  Defined.

  (* Now, we can show that we can indeed give an instance of a handler for an
    external function such that the resulting memory is not equivalent to the initial
    memory.

    Notice that the uninterpreted [Call] trigger is guaranteed to not affect the memory,
    which is why we can prove this lemma.
   *)
  Lemma external_call_can_affect_memory':
    forall regs f,
    exists ext mem,
      (eutt (fun '(mem', _) _ => mem <> mem')
            (partial_interp_asm ext (ext_call f) mem regs)
            (partial_interp_asm (E := F) ext (ext_call f) mem regs)).
  Proof.
    intros. exists call_modifies_mem', nil.
    subst.
    unfold partial_interp_asm, partial_interp_map, interp_map.
    unfold ext_call.
    setoid_rewrite interp_trigger. cbn.
    unfold cat, Cat_Handler, Handler.cat.
    cbn. unfold resum, ReSum_id, id_, Id_IFun.
    unfold h_E.
    setoid_rewrite interp_trigger.
    unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
    unfold ITree.trigger.
    rewrite interp_state_vis. rewrite interp_state_bind. cbn.
    unfold pure_state. rewrite interp_state_bind. rewrite bind_bind.
    setoid_rewrite tau_eutt. do 2 setoid_rewrite interp_state_ret.
    replace
      (fun st : memory * (registers * value) => Ret (fst st, (fst (snd st), snd (snd st)))) with
      (fun st => {| _observe := RetF (E := FnCall +' F) (R := memory * (registers * value)) st |}).
    2 : {
      eapply FunctionalExtensionality.functional_extensionality.
      intros. destruct x, p. cbn; auto.
    }
    rewrite interp_state_trigger. setoid_rewrite bind_ret_l.
    unfold call_modifies_mem'. cbn.
    unfold interp_map. rewrite interp_state_bind. rewrite bind_bind.
    unfold insert. unfold embed, Embeddable_forall, embed, Embeddable_itree.
    rewrite interp_state_trigger. cbn.

    unfold pure_state. rewrite bind_bind.
    unfold trigger.
    rewrite bind_vis. eapply eqit_Vis. intros.
    rewrite bind_ret_l. cbn. rewrite bind_ret_l. rewrite interp_state_bind.
    rewrite bind_bind. rewrite interp_state_vis.
    cbn. rewrite bind_ret_l.
    cbn.
    rewrite interp_state_ret. rewrite tau_eutt. rewrite bind_ret_l.
    cbn. rewrite interp_state_ret. rewrite bind_ret_l.
    apply eqit_Ret.
    intro. unfold alist_add in H;cbn in H. inv H.
  Qed.

End PartialInterpAsmProperties.

From Paco Require Import paco.
Require Import EuttEv.

Section MemCallAsmProperties.

  Definition interp_call_asm {E : Type -> Type} {A : Type}
            (t : itree (Reg +' Memory +' FnCall +' E) A):
      memory -> registers -> itree (mem_callE +' E) (memory * (registers * A)) :=
    let t' := interp (bimap h_reg (case_ h_memory (case_ h_E h_E))) t in
    fun  mem regs => interp_call_map (interp_map t' regs) mem.

  Definition run_call_asm (p: asm 1 0) :=
    interp_call_asm (denote_asm p Fin.f0) empty empty.

  Context {F: Type -> Type}.
  Notation E := (Reg +' Memory +' FnCall +' F).
  Notation E' := (mem_callE +' F).

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_call_asm {R}:
    Proper (@eutt E R R eq ==> eq ==> eq ==> @eutt E' (prod memory (prod registers R)) (prod _ (prod _ R)) eq)
           (interp_call_asm).
  Proof.
    repeat intro.
    unfold interp_call_asm.
    unfold interp_map. subst.
    rewrite H.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [Ret]. *)
  Lemma interp_call_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory),
      @eutt E' _ _ eq (interp_call_asm (ret r) mem regs)
            (ret (mem, (regs, r))).
  Proof.
    unfold interp_call_asm, interp_call_map, interp_map.
    intros.
    unfold ret at 1, Monad_itree.
    rewrite interp_ret, 2 interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_asm] commutes with [bind]. *)
  Lemma interp_call_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (regs : registers) (mem: memory),
      @eutt E' _ _ eq (interp_call_asm (ITree.bind t k) mem regs)
            (ITree.bind (interp_call_asm t mem regs)
                        (fun '(mem', (regs', x)) => interp_call_asm (k x) mem' regs')).
  Proof.
    intros.
    unfold interp_call_asm.
    unfold interp_call_map, interp_map. cbn.
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

  Import ITreeNotations.
  Import MonadNotation.
  Open Scope monad_scope.


  Lemma interp_call_asm_ext_call_eq :
    forall E regs f mem,
      (interp_call_asm (E := E) (ext_call f) mem regs) ≈
      (vis (MemCall (mem, resum IFun value (Call f))) (fun x : memory * value => Ret (fst x, (regs, snd x)))).
  Proof.
    intros. subst.
    unfold interp_call_asm, interp_call_map, interp_map.
    unfold ext_call.
    setoid_rewrite interp_trigger. cbn.
    unfold cat, Cat_Handler, Handler.cat.
    cbn. unfold resum, ReSum_id, id_, Id_IFun.
    unfold h_E.
    setoid_rewrite interp_trigger.
    unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
    unfold ITree.trigger.
    rewrite interp_state_vis. rewrite interp_state_bind. cbn.
    unfold pure_state. rewrite interp_state_bind. rewrite bind_bind.
    setoid_rewrite tau_eutt.
    rewrite interp_state_trigger. cbn.
    setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    setoid_rewrite interp_state_ret. unfold MapDefault.handle_call.
    rewrite bind_trigger. cbn. reflexivity.
  Qed.

  (* Let's write a (way too) simple specification that states that any external
      call is going to modify an empty memory to a non-empty one.
   *)
  Definition mem_call_spec A B : @mem_callE memory FnCall A -> A -> @mem_callE memory FnCall B -> B -> Prop.
    intros memE_A a memE_B b.
    destruct memE_A eqn : HA; rename X into A.
    destruct p as (initial_memory_A & call_event_A).
    destruct a as (final_memory_A & returned_value_A).

    destruct memE_B eqn : HB; rename X into B.
    destruct p as (initial_memory_B & call_event_B).
    destruct b as (final_memory_B & returned_value_B).

    exact (initial_memory_A = nil ->
           final_memory_A <> nil).
  Defined.

  (* We can use this specification for the [euttEv] relation, which incorporates
     specifications about events. *)
  Lemma ext_call_ev :
    forall A f regs,
    euttEv (R1 := (memory * (A * value))) (fun _ _ _ _ => True) mem_call_spec (fun '(m_final, _) _ => m_final <> nil)
      (vis (MemCall (nil, resum IFun value (Call f))) (fun x : memory * value => Ret (fst x, (regs, snd x))))
      (vis (MemCall (nil, resum IFun value (Call f))) (fun x : memory * value => Ret (fst x, (regs, snd x)))).
  Proof.
    intros. pstep. econstructor. auto. intros. red. left.
    pstep. econstructor.
    repeat red in H. cbn in H. destruct a, b.
    specialize (H eq_refl). auto.
  Qed.

End MemCallAsmProperties.

(** Now that we have both our language, we could jump directly into implementing
our compiler.  However, if we look slightly ahead of us, we can observe that: -
compiling expressions and basic statements will be mostly straightforward; - but
linking the resulting elementary (open) [asm] programs together is not as
trivial. In particular, reasoning inductively on this linking is more
challenging.  We therefore take a detour: we first reason in isolation about
linking, and to this end we jump to [AsmCombinators.v].  *)
