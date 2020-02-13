From ITree Require Import
     ITree
     ITreeDefinition
     Eq
.

From ExtLib Require Import
     Structures.Monad. 

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(** *Weak Bisimilarity in CCS
    How do we define weak bisimilarity in CCS using ITrees, when their notion
    of bisimilarity is different? We need only to observe this simple example
    to observe the limitation of weak bisimulation in ITrees.

    These processes are weakly inequivalent in CCS:
      τ.A + B
      A + B
    While these are weakly equivalent:
      τ.τ.A + B
      τ.A + B
    This pair of processes are also weakly equivalent:
      a.τ.C + B
      a.C + B
    (For a proof of why this is so, see Chapter 6 of Milner's π-calculus text [1].)

    Under the notion of weak bisimulation in ITrees, we simply cannot treat the
    internal steps in CCS as a silent, unobservable step. This is because in the
    presence of nondeterministic choice (+), the τ-step in CCS (the handshake
    operator), weirdly enough, does have an observational influence in the process.
    (i.e. If a handshake step appears right under nondeterministic choice, it
    affects the weak bisimilarity relation).

    One solution to this (as seen in DenoteCCS.v) is to always promote the
    τ steps in CCS as a visible event (the "Sync" event). However, this not only
    creates a notion of equivalence that is too strong but also the interpretation
    of these ITrees remain in question.

    [ccs.org] presents a sketch of a possible work around: let's try promoting the
    synchronous silent step directly under a nondeterministic choice as a "special"
    synchronous step that is visible!
 *)


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* A variant of CCS denotation, using binary `or` operators and `promoted silent`
   steps. *)
Section denote_ccs.

  (* Labels for defining parity of actions. *)
  Variant Label : Type :=
  | In (n : nat) : Label
  | Out (n : nat) : Label
  .

  (* CCS Syntax. *)
  Inductive ccs : Set :=
  | Zero
  | Fail
  | Or (a b : ccs)
  | Bang (a : ccs)
  | Act (l : Label) (a : ccs)
  | Par (a b : ccs)
  .

  (* CCS Events. *)
  Variant ccsE : Type -> Type :=
  | OrE : ccsE bool
  | ActE (l : Label) : ccsE unit
  | FailE : ccsE void
  | SyncE : ccsE unit
  | OSyncE : ccsE unit (* See ccs.org. *)
  .

  (* Denotation of CCS as uninterpreted ITree events. *)
  Definition ccsD := itree ccsE unit.

  (*Context {eff : Type -> Type}.
  Context {CCS: ccsE -< eff}.*)

  (* Equational theories for CCS. *)

  (* State Lemma that this shape invariant can hold for any tree. *)

  Definition or (p1 p2 : itree ccsE unit) : itree ccsE unit :=
    Vis OrE (fun (x : bool) => if x then p1 else p2)
  .

  Definition denote_or (p1 p2 : itree ccsE unit) : itree ccsE unit :=
    match p1, p2 with
    | Vis SyncE t1, Vis SyncE t2 => or (or (Vis OSyncE t1) (Vis SyncE t1))
                                       (or (Vis OSyncE t2) (Vis SyncE t2))
    | Vis SyncE t1, _=> or (or (Vis OSyncE t1) (Vis SyncE t1)) p2
    | _, Vis SyncE t2 => or p1 (or (Vis OSyncE t2) (Vis SyncE t2))
    | _, _ => or p1 p2
    end
  .

  (*Fixpoint denote_ccs (p : ccs) : itree ccsE unit :=
    match p with
    | Zero => ret tt
    | Fail => Vis FailE (fun x : void => match x with end)
    | Act l a => trigger (ActE l) ;; Tau (denote_ccs a)
    | Or a b => denote_or (denote_ccs a) (denote_ccs b)
    | Par a b => p1 <- denote_ccs a ;;
                    p2 <- denote_ccs b ;;
                    ret tt
    | Bang a => ret tt
    end
  .*)

End denote_ccs.

