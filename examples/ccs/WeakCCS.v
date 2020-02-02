From ITree Require Import
     ITree
     ITreeDefinition
     Eq
.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(** *Weak Bisimilarity in CCS
    How do we define weak bisimilarity in CCS using ITrees, when their notion
    of bisimilarity are different? We need only to observe this simple example
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


(* A variant of CCS denotation, using binary `or` operators and `promoted silent`
   steps. *)
Section weak_ccs.

  (* Labels for defining parity of actions. *)
  Variant Label : Type :=
  | In (n : nat) : Label
  | Out (n : nat) : Label
  .

  Variant ccsE : Type -> Type :=
  | Or : ccsE bool
  | Act (l : Label) : ccsE unit
  | Fail : ccsE void
  .

  Definition ccs := itree ccsE unit.

End weak_ccs.

Notation ccs' := (itree' ccsE unit).

Section weak_ccs_combinators.

  Definition zero : ccs := Ret tt.

  Definition fail : ccs := Vis Fail (fun x : void => match x with end).

  Definition send (n : nat) (p : ccs) : ccs := Vis (Act (In n)) (fun _ => p).
  Definition recv (n : nat) (p : ccs) : ccs := Vis (Act (Out n)) (fun _ => p).

  Definition choose (p1 p2 : ccs) : ccs :=
    Vis Or (fun (b : bool) => if b then p1 else p2).

End weak_ccs_combinators.

