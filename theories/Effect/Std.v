(* Common effects *)

(* In this module:
   - [failureE]
   - [nondetE]
   - [readerE]
   - [stateE]
   - [writerE]
   - [stopE]  ([Ret] as an effect)
   - [traceE] (for debugging)
 *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib.Structures Require Import
     Functor Monoid.

From ITree Require Import
     Basics
     Core Morphisms
     Effect.Sum
     OpenSum.

Section Failure.

Variant failureE : Type -> Type :=
| Fail : string -> failureE void.

Definition fail {E : Type -> Type} `{failureE -< E} {X}
           (reason : string)
  : itree E X :=
  vis (Fail reason) (fun v : void => match v with end).

End Failure.

Section NonDeterminism.

Variant nondetE : Type -> Type :=
| Or : nondetE bool.

Definition or {E} `{nondetE -< E} {R} (k1 k2 : itree E R)
  : itree E R :=
  vis Or (fun b : bool => if b then k1 else k2).

(* This can fail if the list is empty. *)
Definition choose {E} `{nondetE -< E} `{failureE -< E} {X}
  : list X -> itree E X := fix choose' xs : itree E X :=
  match xs with
  | [] => fail "choose: No choice left"
  | x :: xs =>
    or (Ret x) (choose' xs)
  end.

(* Choose an element from a nonempty list (with the head and tail
   as separate arguments), so it cannot fail. *)
Definition choose1 {E} `{nondetE -< E} {X}
  : X -> list X -> itree E X := fix choose1' x xs : itree E X :=
  match xs with
  | [] => Ret x
  | x' :: xs => or (Ret x) (choose1' x' xs)
  end.

(* All ways of picking one element in a list apart
   from the others. *)
Definition select {X} : list X -> list (X * list X) :=
  let fix select' pre xs :=
      match xs with
      | [] => []
      | x :: xs' => (x, pre ++ xs') :: select' (pre ++ [x]) xs'
      end in
  select' [].

End NonDeterminism.

(* TODO Another nondet with Or indexed by Fin. *)

Section Reader.

  Variable (env : Type).

  Variant readerE : Type -> Type :=
  | Ask : readerE env.

  Definition ask {E} `{readerE -< E} : itree E env :=
    embed Ask.

  Definition eval_reader {E} : env -> readerE ~> itree E :=
    fun r _ e =>
      match e with
      | Ask => Ret r
      end.

  Definition run_reader {E} : env -> itree (readerE +' E) ~> itree E :=
    interp_reader (into_reader eval_reader).

End Reader.

Arguments ask {env E _}.
Arguments run_reader {_ _} _ _ _.

Import ITree.Basics.Monads.

Section State.

  Variable (S : Type).

  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E} `{stateE -< E} : itree E S := embed Get.
  Definition put {E} `{stateE -< E} : S -> itree E unit := embed Put.

  Definition eval_state {E} : stateE ~> stateT S (itree E) :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
      end.

  Definition run_state {E} :
    itree (stateE +' E) ~> stateT S (itree E) :=
    interp_state (into_state eval_state).

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {_ _} [_] _ _.

Section Writer.

  Variable (W : Type).

  Variant writerE : Type -> Type :=
  | Tell : W -> writerE unit.

  Definition tell {E} `{writerE -< E} : W -> itree E unit :=
    embed Tell.

End Writer.

Section Stop.
  (* "Return" as an effect. *)

  Variant stopE (S : Type) : Type -> Type :=
  | Stop : S -> stopE S void.

  Definition stop {E S R} `{stopE S -< E} : S -> itree E R :=
    fun s =>
      vis (Stop s) (fun v : void => match v with end).

End Stop.

Arguments stopE S X.
Arguments stop {E S R _}.

Section Trace.

  Variant traceE : Type -> Type :=
  | Trace : string -> traceE unit.

  Definition trace {E} `{traceE -< E} (msg : string) : itree E unit :=
    lift (Trace msg).

  Definition trace_hom {E} (R : Type) (e : traceE R) : itree E R :=
    match e with
    | Trace _ => Ret tt
    end.

  Definition ignore_trace {E} : itree (traceE +' E) ~> itree E :=
    interp (into trace_hom).

End Trace.
