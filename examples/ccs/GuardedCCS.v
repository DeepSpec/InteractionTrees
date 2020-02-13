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

(* *Finitary, Strongly Guarded CCS*
   - Finitary: for any p, Const(p) is finite.
   - Guarded: for any summation, the top level process is an action or
              synchronous step.
   - Strongly Guarded : for any summation, the top level process is **visible**
                        action.

   Instead of interpreting non-determination as an uninterpreted event,
   let's model them using K-Trees.

   We also impose an extra guardedness condition on the non-deterministic
   continuations: namely, that the immediate continuations must be an action event
   and cannot be a silent step.

   This constraint is a work-around to the approach in [WeakCCS.v] and [ccs.org]
 *)


Import Monads.
Import MonadNotation.
Import ListNotations.
Local Open Scope monad_scope.

Section GuardedCCS.

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

  Variant action : Type :=
  | Visible (x : visible)
  | Silent
  .

  (* Any sequence of labels must be strongly guarded, i.e. the starting label
     must be a visible action. *)
  Variant labels : Type := Labels (vx : visible) (xl : action).

  (** Strongly Guarded CCS Syntax, following:
     [R.Gorrieri, C.Versari, _Introduction to Concurrency Theory_].  *)

  (* Sequential Processes. *)
  Inductive seq_ccs : Type :=
  | Zero
  | Or (a b : seq_ccs)
  | Act (x : labels) (a : seq_ccs)
  .

  (* CCS Processes. *)
  Inductive ccs : Type :=
  | Proc (p : seq_ccs)
  | Par (a b : ccs)
  | New (x : idx) (a : ccs)
  | Bang (p : ccs)
  .

End GuardedCCS.

Infix "≡?" := (eq_idx) (at level 70).

Section DenoteCCS.

  Variant eff : Type -> Type :=
  | ActE (x : labels) : eff unit
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

  Definition match_action (target : idx) (x : action) : action :=
    match x with
    | Silent => Silent
    | Visible v => Visible (match_visible target v)
    end
  .

  (* Hiding function for denoting the `New` operator. *)
  Definition hide (x : idx) {E : Type -> Type} : eff ~> eff :=
    fun _ e =>
      match e with
      | ActE (Labels v1 a2) =>
        ActE (Labels (match_visible x v1) (match_action x a2))
      | x => x
      end.

  (* The generating operator, bang. *)
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

