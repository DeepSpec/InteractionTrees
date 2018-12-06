(** Common effects *)

(* TODO Swap sums (changed associativity). *)
(* TODO Split framework for extensible effects from concrete effect definitions *)

Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.
Require Import String.

Require Import ITree.ITree.
Require Import ITree.Morphisms.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monoid.

Variant void : Type := .

(** Sums for extensible event types. *)

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inlE (_ : E1 X)
| inrE (_ : E2 X).

Variant emptyE : Type -> Type := .

(* Just for this section, [A B C D : Type -> Type] are more
   effect types. *)

Definition swap1 {A B : Type -> Type} {X : Type}
           (ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inlE a => inrE a
  | inrE b => inlE b
  end.

Definition bimap_sum1 {A B C D : Type -> Type} {X Y : Type}
           (f : A X -> C Y) (g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inlE a => inlE (f a)
  | inrE b => inrE (g b)
  end.

Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.

Section into.
  Context {E F : Type -> Type}.

  Definition into (h : eff_hom E F) : eff_hom (E +' F) F :=
    fun _ e =>
      match e with
      | inlE e => h _ e
      | inrE e => liftE e 
      end.

  Definition into_state {s} (h : eff_hom_s s E F) : eff_hom_s s (E +' F) F :=
    fun _ e s =>
      match e with
      | inlE e => h _ e s
      | inrE e => Vis e (fun x => Ret (s, x))
      end.

  Definition into_reader {s} (h : eff_hom_r s E F) : eff_hom_r s (E +' F) F :=
    fun _ e s =>
      match e with
      | inlE e => h _ e s
      | inrE e => liftE e
      end.

  Definition into_writer {s} `{Monoid_s : Monoid s} (h : eff_hom_w s E F)
  : eff_hom_w s (E +' F) F :=
    fun _ e =>
      match e with
      | inlE e => h _ e
      | inrE e => Vis e (fun x => Ret (monoid_unit Monoid_s, x))
      end.

  (* todo(gmm): is the a corresponding definition for `eff_hom_p`? *)

End into.


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
      | inlE a => convert a
      | inrE b => convert b
      end }.

(* Lean right by default for no reason. *)
Global Instance fluid_left A B `{Convertible A B} C
: Convertible A (sum1 B C) | 9 :=
  { convert X a := inlE (convert a) }.

(* Very incoherent instances. *)
Global Instance fluid_right A C `{Convertible A C} B
: Convertible A (sum1 B C) | 8 :=
  { convert X a := inrE (convert a) }.

Global Instance fluid_empty A : Convertible emptyE A :=
  { convert X v := match v with end }.

Notation "EE ++' E" := (List.fold_right sum1 EE E)
(at level 50, left associativity) : type_scope.

Notation "E -< F" := (Convertible E F)
(at level 90, left associativity) : type_scope.

Module Import SumNotations.

(* Is this readable? *)

Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inrE x) : sum_scope.
Notation "( x |)" := (inlE x) : sum_scope.
Notation "(| x |)" := (inlE (inrE x)) : sum_scope.
Notation "(|| x )" := (inrE (inrE x)) : sum_scope.
Notation "(|| x |)" := (inrE (inrE (inlE x))) : sum_scope.
Notation "(||| x )" := (inrE (inrE (inrE x))) : sum_scope.
Notation "(||| x |)" := (inrE (inrE (inrE (inlE x)))) : sum_scope.
Notation "(|||| x )" := (inrE (inrE (inrE (inrE x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inrE (inrE (inrE (inrE (inlE x))))) : sum_scope.
Notation "(||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inrE (inrE (inrE (inrE (inrE (inlE x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE (inrE x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inrE (inrE (inrE (inrE (inrE (inrE (inlE x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inrE (inrE (inrE (inrE (inrE (inrE (inrE x))))))) : sum_scope.

End SumNotations.

Open Scope sum_scope.

(*
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
*)

Definition vis {E F R X} `{F -< E}
           (e : F X) (k : X -> itree E R) : itree E R :=
  Vis (convert e) k.

Definition lift {E F X} `{F -< E}
           (e : F X) : itree E X :=
  liftE (convert e).


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

  Variant readerE : Type -> Type :=
  | Ask : readerE env.

  Definition ask {E} `{Convertible readerE E} : itree E env :=
    liftE (convert Ask).

  Definition eval_reader {E} : eff_hom_r env readerE E :=
    fun _ e r =>
      match e with
      | Ask => Ret r
      end.

  Definition run_reader {E} R (v : env) (t : itree (readerE +' E) R)
  : itree E R :=
    interp_reader (into_reader eval_reader) t v.

End Reader.

Arguments ask {env E _}.
Arguments run_reader {_ _} [_] _ _.

Section State.

  Variable (S : Type).

  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E} `{stateE -< E} : itree E S := lift Get.
  Definition put {E} `{stateE -< E} (s : S) : itree E unit :=
    lift (Put s).

  Definition eval_state {E} : eff_hom_s S stateE E :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
      end.

  Definition run_state {E R} (v : S) (t : itree (stateE +' E) R)
  : itree E (S * R) :=
    interp_state (into_state eval_state) t v.

(*
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
*)

End State.

Arguments get {S E _}.
Arguments put {S E _}.
Arguments run_state {_ _} [_] _ _.

Section Tagged.
  Variable E : Type -> Type.

  Record Tagged (tag : Set) (t : Type) : Type := Tag
  { unTag : E t }.

  Definition atTag (tag : Set) {t} (e : E t) : Tagged tag t :=
  {| unTag := e |}.

  Definition eval_tagged {tag} : eff_hom (Tagged tag) E :=
    fun _ e => liftE e.(unTag).

End Tagged.

Arguments unTag {E tag}.
Arguments Tag {E} tag.

Section Counter.

  Class Countable (N : Type) := { zero : N; succ : N -> N }.

  Global Instance Countable_nat : Countable nat | 0 :=
  { zero := O; succ := S }.

  (* Parameterizing by the type of counters makes it easier
   to have more than one counter at once. *)
  Variant counterE (N : Type) : Type -> Type :=
  | Incr : counterE N N.

  Definition incr {N E} `{counterE N -< E} : itree E N :=
    lift Incr.

  Definition eval_counter {N E} `{Countable N}
  : eff_hom_s N (counterE N) E :=
    fun _ e s =>
      match e with
      | Incr => Ret (succ s, s)
      end.

  Definition run_counter {N} `{Countable N} {E R} (t : itree (counterE N +' E) R)
  : itree E R :=
    fmap snd (interp_state (into_state eval_counter) t zero).

End Counter.

Arguments run_counter {_ _ _} [_] _.

Section Writer.

  Variable (W : Type).

  Variant writerE : Type -> Type :=
  | Tell : W -> writerE unit.

  Definition tell {E} `{writerE -< E} (w : W) : itree E unit :=
    lift (Tell w).

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

  (* todo(gmm): define in terms of `eff_hom` *)
  CoFixpoint ignore_trace {E R} (t : itree (traceE +' E) R)
  : itree E R :=
    match t.(observe) with
    | RetF r => Ret r
    | TauF t => Tau (ignore_trace t)
    | @VisF _ _ _ u e k =>
      match e return (u -> _) -> _ with
      | inlE e => match e with
                 | Trace _ => fun k => Tau (ignore_trace (k tt))
                 end
      | inrE e => fun k => Vis e (fun x => ignore_trace (k x))
      end k
    end.

End Trace.
