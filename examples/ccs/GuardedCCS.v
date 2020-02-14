From ITree Require Import
     ITree
     ITreeFacts
     ITreeDefinition
     Eq
.

From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Arith.EqNat
     Arith.PeanoNat
     Lists.List
     Morphisms
     Program.Equality
     Setoid
     Strings.String
     RelationClasses
     Relations.Relation_Operators
     ZArith.Int.


Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(* *Finitary, Guarded CCS*
   - Finitary: for any p, Const(p) is finite.
   - Guarded: for any summation, the top level process is an action or
              synchronous step.

   Idea(?) : Instead of interpreting non-determination as an uninterpreted event,
   let's model them using K-Trees.

   We also attempted to impose an extra guardedness condition on the
   non-deterministic continuations: namely, that the immediate continuations
   must be an action event and cannot be a silent step. This did not work, as
   explained below.
   This constraint was a proposed work-around to the approach in [WeakCCS.v] and
   [ccs.org].
 *)


Import Monads.
Import MonadNotation.
Import ListNotations.
Local Open Scope monad_scope.

Section GuardedCCS.

  (** *Syntax *)

  (* Locally Nameless representation of variables. *)
  Variant idx : Type :=
  | I_string (s : string) : idx
  | I_nat (n : nat) : idx
  .

  Definition eq_idx : idx -> idx -> bool :=
    fun i1 i2 =>
      match i1 with
      | I_string s => match i2 with
                    | I_string s => true
                    | _ => false
                    end
      | I_nat n => match i2 with
                  | I_nat n => true
                  | _ => false
                  end
      end
  .

  (* CCS labels have polarity. *)
  Variant visible : Type :=
  | In (x : idx)
  | Out (x : idx)
  .

  Variant label : Type :=
  | Visible (x : visible)
  | Silent
  .

  (** Guarded CCS Syntax, following:
     [R.Gorrieri, C.Versari, _Introduction to Concurrency Theory_].
     Any sequence of labels under nondeterministic choice must be guarded,
     i.e. the starting label must be an action. *)

  (*
     We attempted, at first, to define a "Strongly Guarded" CCS.
     Guarded CCS is defined as having action labels immediately under
     nondeterministic choice. _Strongly Guarded_ CCS, on the other hand,
     forces a *visible* action under nondeterministic choice, i.elim .

        Inductive action : Type := Action (x : label) (a : action).
        Inductive seq_ccs : Type :=
                  ...
        | GAct (vx : visible) (a : action).

     However, this notion of "Strongly Guarded" doesn't work for two
     reasons:

     1. You cannot model any _internal step_ that a system may wish
        to take.
        For instance, in vanilla CCS, one can write down the following
        expression:
              τ.N + α -τ-> N
        We cannot write an equivalent expression in Strongly Guarded CCS.

     2. Guardedness condition breaks (is fragile) whenever we try to
        define an _action_ step.
        How do we define a correct action step?

        Let's look at this expression:
              α.τ.N + β.τ.N
        No matter what the system chooses to do, the guardedness condition
        immediately breaks. Since we want to compare the operational weak
        bisimulation to our denotational equivalence of ITree weak bisimulation,
        (for proving full abstraction) we still want to be able to define
        a small step semantics. This syntactic definition will be fragile.
  *)

  (* Sequential Processes. *)
  Inductive seq_ccs : Type :=
  | Zero
  | Or (a b : seq_ccs)
  | Act (x : label) (a : seq_ccs)
  .

  (* CCS Processes. *)
  Inductive ccs : Type :=
  | Proc (p : seq_ccs)
  | Par (a b : ccs)
  | New (x : idx) (a : ccs)
  | Bang (p : ccs)
  .

  (** *Structural Operational Semantics *)


End GuardedCCS.

Infix "≡?" := (eq_idx) (at level 70).

(** *Denotational Semantics

    Denotation of operational CCS in ITrees.
 *)

Section DenoteCCS.

  (* IY: We leave the parallel composition operator as an uninterpreted event
         for now. *)
  Variant eff : Type -> Type :=
  | ActE (x : label) : eff unit
  | OrE : eff bool
  | ParE : eff bool
  .

  Fixpoint denote_seq_ccs (sp : seq_ccs) : itree eff unit :=
    match sp with
    | Zero => ret tt
    | Or a b =>
      let p1 := denote_seq_ccs a in
      let p2 := denote_seq_ccs b in
      Vis OrE (fun (b : bool) => if b then p1 else p2)
    | Act x k =>
      let p := denote_seq_ccs k in
      Vis (ActE x) (fun _ => p)
    end.

  (* IY: These series of matches seem like they should have a nice functional
     combinator... *)

  Definition match_idx (target x : idx) : idx :=
    if x ≡? target then I_nat 0
    else match x with
         | I_string _ => x
         | I_nat i => I_nat (i + 1)
         end
  .

  Definition match_visible (target : idx) (x : visible) : visible :=
    match x with
    | In x1 => In (match_idx target x1)
    | Out x1 => Out (match_idx target x1)
    end
  .

  Definition match_action (target : idx) (x : label) : label :=
    match x with
    | Silent => Silent
    | Visible v => Visible (match_visible target v)
    end
  .

  (* Hiding function for denoting the `New` operator. *)
  Definition hide (x : idx) {E : Type -> Type} : eff ~> eff :=
    fun _ e =>
      match e with
      | ActE a =>
        ActE (match_action x a)
      | x => x
      end.

  (* The generating operator, bang.
     IY: Can we write this using the `iter` combinator? *)
  CoFixpoint bang (body : itree eff unit -> (itree eff ((itree eff unit) + unit))):
    (itree eff unit) -> itree eff unit :=
    fun (a : itree eff unit) => ab <- body a;;
             match ab with
             | inl a => Vis ParE (fun (b : bool) => if b then Tau (a) else bang body a)
             | inr b => Ret b (* never going to be reached *)
             end
   .

  Fixpoint denote_ccs (p : ccs) : itree eff unit :=
    match p with
    | Proc x => denote_seq_ccs x
    | New x a => let k := denote_ccs a in
                translate (@hide x eff) k
    | Par a b => let k1 := denote_ccs a in
                let k2 := denote_ccs b in
                Vis ParE (fun (b : bool) => if b then k1 else k2)
    | Bang x => bang (fun a => ret (inl a)) (denote_ccs x)
    end.

   Compute (burn 100 (denote_ccs (Bang (Proc (Or Zero Zero))))).

End DenoteCCS.

(* TODO: 1. Implement operational and contextual preorder.
         2. Prove full abstraction.
         3. Write handler for denotation. (Prop or State monad?)
 *)
