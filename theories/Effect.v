(** Common effects *)

(* TODO Swap sums (changed associativity). *)

Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.
Require Import String.

Require Import ITree.ITree.

Inductive void : Type := .

Section Extensible.

(** Sums for extensible event types. *)

Definition sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
  E1 X + E2 X.

Inductive emptyE : Type -> Type := .

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

Definition swap1 {A B : Type -> Type} {X : Type}
           (ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inl a => inr a
  | inr b => inl b
  end.

Definition bimap_sum1 {A B C D : Type -> Type} {X Y : Type}
           (f : A X -> C Y) (g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

(* Automatic application of commutativity and associativity for sums.
   TODO: This is still quite fragile and prone to
   infinite instance resolution loops.
 *)

Class Convertible (A B : Type -> Type) :=
  { convert : forall {X}, A X -> B X }.

(* Don't try to guess. *)
Global Instance fluid_id A : Convertible A A | 0 :=
  { convert X a := a }.

(* Destructure sums. *)
Global Instance fluid_sum A B C `{Convertible A C} `{Convertible B C}
  : Convertible (sum1 A B) C | 7 :=
  { convert X ab :=
      match ab with
      | inl a => convert a
      | inr b => convert b
      end }.

(* Lean right by default for no reason. *)
Global Instance fluid_left A B `{Convertible A B} C
  : Convertible A (sum1 B C) | 9 :=
  { convert X a := inl (convert a) }.

(* Very incoherent instances. *)
Global Instance fluid_right A C `{Convertible A C} B
  : Convertible A (sum1 B C) | 8 :=
  { convert X a := inr (convert a) }.

Global Instance fluid_empty A : Convertible emptyE A :=
  { convert X v := match v with end }.

End Extensible.

Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
(at level 50, left associativity) : type_scope.

Notation "E -< F" := (Convertible E F)
(at level 90, left associativity) : type_scope.

Module Import SumNotations.

(* Is this readable? *)

Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inr x) : sum_scope.
Notation "( x |)" := (inl x) : sum_scope.
Notation "(| x |)" := (inl (inr x)) : sum_scope.
Notation "(|| x )" := (inr (inr x)) : sum_scope.
Notation "(|| x |)" := (inr (inr (inl x))) : sum_scope.
Notation "(||| x )" := (inr (inr (inr x))) : sum_scope.
Notation "(||| x |)" := (inr (inr (inr (inl x)))) : sum_scope.
Notation "(|||| x )" := (inr (inr (inr (inr x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inr (inr (inr (inr (inl x))))) : sum_scope.
Notation "(||||| x )" :=
  (inr (inr (inr (inr (inr x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inr (inr (inr (inr (inr (inl x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inr (inr (inr (inr (inr (inr x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inr (inr (inr (inr (inr (inr (inl x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inr (inr (inr (inr (inr (inr (inr x))))))) : sum_scope.

End SumNotations.

Open Scope sum_scope.

Definition lift {E F R} `{Convertible E F} : itree E R -> itree F R :=
  hoist (@convert _ _ _).

Class Embed A B :=
  { embed : A -> B }.

Instance Embed_fun T A B `{Embed A B} : Embed (T -> A) (T -> B) :=
  { embed := fun f t => embed (f t) }.

Instance Embed_eff E F R `{Convertible E F} :
  Embed (E R) (itree F R) :=
  { embed := fun e => liftE (convert e) }.

Arguments embed {A B _} e.

Definition vis {E F R X} `{F -< E}
           (e : F X) (k : X -> itree E R) : itree E R :=
  Vis (convert e) k.

Definition run {E F} (run_ : eff_hom E F)
: forall X, itree (E +' F) X -> itree F X :=
  let run' Y (e : (E +' F) Y) :=
      match e with
      | (| f' ) => liftE f'
      | ( e' |) => run_ _ e'
      end
  in hom run'.
Arguments run {_ _} _ [_] _.

Section Failure.

Inductive failureE : Type -> Type :=
| Fail : string -> failureE void.

Definition fail {E : Type -> Type} `{failureE -< E} {X}
           (reason : string)
  : itree E X :=
  vis (Fail reason) (fun v : void => match v with end).

End Failure.

Section NonDeterminism.

Inductive nondetE : Type -> Type :=
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

(* TODO: how about a variant of [choose] that expects
   a nonempty list so it can't fail? *)

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

Inductive readerE : Type -> Type :=
| Ask : readerE env.

Definition ask {E} `{Convertible readerE E} : itree E env :=
  liftE (convert Ask).

CoFixpoint run_reader {E R} (v : env) (t : itree (readerE +' E) R)
  : itree E R :=
  match t with
  | Ret r => Ret r
  | Vis ( e |) k =>
    match e in readerE X return (X -> _) -> _ with
    | Ask => fun k => Tau (run_reader v (k v))
    end k
  | Vis (| e ) k => Vis e (fun x => run_reader v (k x))
  | Tau t => Tau (run_reader v t)
  end.

End Reader.

Arguments ask {env E _}.

Section State.

Variable (S : Type).

Inductive stateE : Type -> Type :=
| Get : stateE S
| Put : S -> stateE unit.

Definition get {E} `{stateE -< E} : itree E S := embed Get.
Definition put {E} `{stateE -< E} (s : S) : itree E unit :=
  embed Put s.

CoFixpoint run_state' {E R} (s : S) (t : itree (stateE +' E) R)
  : itree E (S * R) :=
  match t with
  | Ret r => Ret (s, r)
  | Tau t => Tau (run_state' s t)
  | Vis ( e |) k =>
    match e in stateE X return (X -> _) -> _ with
    | Get => fun k => Tau (run_state' s (k s))
    | Put s' => fun k => Tau (run_state' s' (k tt))
    end k
  | Vis (| e ) k => Vis e (fun x => run_state' s (k x))
  end.

Definition run_state {E F : Type -> Type}
           `{Convertible E (stateE +' F)} {R}
           (s : S) (m : itree E R) : itree F (S * R) :=
  run_state' s (hoist (@convert _ _ _) m : itree (stateE +' F) R).

Definition exec_state {E F : Type -> Type}
           `{Convertible E (stateE +' F)} {R}
           (s : S) (m : itree E R) : itree F S :=
  map fst (run_state s m).

Definition eval_state {E F : Type -> Type}
           `{Convertible E (stateE +' F)} {R}
           (s : S) (m : itree E R) : itree F R :=
  map snd (run_state s m).

End State.

Arguments get {S E _}.
Arguments put {S E _}.

Section Counter.

Class Countable (N : Type) := { zero : N; succ : N -> N }.

Global Instance Countable_nat : Countable nat | 0 :=
  { zero := O; succ := S }.

Inductive nat' {T} (tag : T) : Type :=
| Tagged : nat -> nat' tag.

Global Instance Countable_nat' T (tag : T)
  : Countable (nat' tag) :=
  { zero := Tagged O; succ := fun '(Tagged n) => Tagged (S n) }.

(* Parameterizing by the type of counters makes it easier
   to have more than one counter at once. *)
Inductive counterE (N : Type) : Type -> Type :=
| Incr : counterE N N.

Definition incr {N E} `{counterE N -< E} : itree E N :=
  embed Incr.

CoFixpoint run_counter_from' {N E} `{Countable N} {R}
           (c : N) (t : itree (counterE N +' E) R)
  : itree E R :=
  match t with
  | Ret r => Ret r
  | Tau t => Tau (run_counter_from' c t)
  | Vis ( e |) k =>
    match e in counterE _ X return (X -> _) -> _ with
    | Incr => fun k => Tau (run_counter_from' (succ c) (k c))
    end k
  | Vis (| e ) k =>
    Vis e (fun x => run_counter_from' c (k x))
  end.

Definition run_counter' {N} `{Countable N} {E R}
  : itree (counterE N +' E) R -> itree E R :=
  run_counter_from' zero.

Definition run_counter_for {T} (tag : T) {E R}
  : itree (counterE (nat' tag) +' E) R -> itree E R :=
  run_counter'.

End Counter.

Arguments run_counter_for {T} tag {_ _} t.

Section Writer.

Variable (W : Type).

Inductive writerE : Type -> Type :=
| Tell : W -> writerE unit.

Definition tell {E} `{writerE -< E} (w : W) : itree E unit :=
  embed Tell w.

End Writer.

Section Stop.
  (* "Return" as an effect. *)

  Inductive stopE (S : Type) : Type -> Type :=
  | Stop : S -> stopE S void.

  Definition stop {E S R} `{stopE S -< E} : S -> itree E R :=
    fun s =>
      vis (Stop s) (fun v : void => match v with end).

End Stop.

Arguments stopE S X.
Arguments stop {E S R _}.

Section Trace.

Inductive traceE : Type -> Type :=
| Trace : string -> traceE unit.

Definition trace {E} `{traceE -< E} : string -> itree E unit :=
  embed Trace.

CoFixpoint ignore_trace {E R} (t : itree (traceE +' E) R) :
  itree E R :=
  match t with
  | Ret r => Ret r
  | Tau t => Tau (ignore_trace t)
  | Vis ( e |) k =>
    match e in traceE T return (T -> _) -> _ with
    | Trace _ => fun k => Tau (ignore_trace (k tt))
    end k
  | Vis (| e ) k => Vis e (fun x => ignore_trace (k x))
  end.

End Trace.
