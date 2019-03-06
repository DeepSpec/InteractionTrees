(** The semantics of an interaction tree [itree E ~> M] can be
    derived from semantics given for every individual effect
    [E ~> M].

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] means [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following.

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "Itree interpreters" (or "itree morphisms") are monad morphisms
      [itree E ~> itree F]. Most interpreters in this library are
      actually itree interpreters.

    This module provides various ways of defining interpreters
    from effect handlers and other similar structures.

    - "Effect handlers" are functions [E ~> M] where [M] is a monad.

    - "Itree effect handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough).
 *)

From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics
     Core
     Effect.Sum
     Translate
     OpenSum.

Open Scope itree_scope.

(*

(*  ------------------------------------------------------------------------- *)

A Monad Transformer MT is given by:
  MT : (type -> type) -> (type -> type)
  lift : `{Monad m} {a}, m a -> MT m a

such that:
  Monad (MT m)

  lift o return = return
  lift o (bind t1 k) =

EXAMPLE:
   stateT S m a :=    S -> m (S * a)
   lift : m `{Monad m} {a}, fun (c: m a) (s:S) => y <- c ;; ret (s, y)

operations
  get : m `{Monad m} stateT S m S := fun s => ret_m (s, s)
  put : m `{Monad m}, S -> stateT S m unit := fun s' => fun s => ret_m (s', tt)

(* category *)
id : A ~> MT (itree A)
compose : (B ~> MT2 (itree C)) ~> (A ~> MT1 (itree B)) -> (A ~> (MT2 o MT1) (itree C))

(* co-cartesian *)
par  : (A ~> MT1 (itree B)) -> (C ~> MT2 (itree D)) -> (A + C ~> (MT1 ** MT2) (itree (B + D)))
both : (A ~> MT (itree B)) -> (C ~> (MT itree B)) -> (A + C ~> MT (itree B))

swap : (A ~> MT1 (itree B)) -> (C ~> MT2 (itree D)) -> (A + C ~> (MT2 ** MT1) (itree (D + B)))


left : A ~> MT (itree (A + B))
right : B ~> MT (itree (A + B))

left : (A ~> MT (itree B)) -> (A ~> MT (itree (B + C)))
right : (C ~> MT (itree D)) -> (C ~> MT (itree (A + D)))



(*  ------------------------------------------------------------------------- *)
Algebraic effects handlers

Definition sig (E:Type -> Type) m `{Monad m} := forall X, E X -> m x





*)

(** An itree effect handler [E ~> itree F] defines an
    itree morphism [itree E ~> itree F]. *)
Definition interp {E F : Type -> Type} (h : E ~> itree F) :
  itree E ~> itree F := fun R =>
  ITree.aloop (fun t =>
    match observe t with
    | RetF r => inr r
    | TauF t => inl (Ret t)
    | VisF e k => inl (ITree.map k (h _ e))
    end).
(* TODO: this does a map, and aloop does a bind. We could fuse those
   by giving aloop a continuation to compose its bind with.
   (coyoneda...) *)

(** Effects [E, F : Type -> Type] and itree [E ~> itree F] form a
    category. *)

(* Morphism Category -------------------------------------------------------- *)

Definition eh_cmp {A B C} (g : B ~> itree C) (f : A ~> itree B) :
  A ~> itree C :=
  fun _ e => interp g _ (f _ e).

Definition eh_id {A} : A ~> itree A := @ITree.liftE A.

Definition eh_par {A B C D} (f : A ~> itree B) (g : C ~> itree D)
: (A +' C) ~> itree (B +' D) :=
  fun _ e =>
    match e with
    | inl1 e1 => translate (@inl1 _ _) (f _ e1)
    | inr1 e2 => translate (@inr1 _ _) (g _ e2)
    end.

Definition eh_both {A B C} (f : A ~> itree B) (g : C ~> itree B)
: (A +' C) ~> itree B :=
  fun _ e =>
    match e with
    | inl1 e1 => f _ e1
    | inr1 e2 => g _ e2
    end.

Definition eh_lift {A B} (m : A ~> B)  : A ~> itree B :=
  fun _ e => ITree.liftE (m _ e).

Definition eh_inl {A B} : A ~> itree (A +' B) :=
  eh_lift (fun _ e => inl1 e).

Definition eh_inr {A B} : B ~> itree (A +' B) :=
  eh_lift (fun _ e => inr1 e).

Definition eh_swap {A B} : A +' B ~> itree (B +' A) :=
  eh_lift Sum1.swap.

Definition eh_elim_empty {A} : emptyE ~> itree A :=
  eh_lift Sum1.elim_emptyE.

Definition eh_empty_left {B} : emptyE +' B ~> itree B :=
  eh_lift Sum1.emptyE_left.

Definition eh_empty_right {A} : A +' emptyE ~> itree A :=
  eh_lift Sum1.emptyE_right.

(* SAZ: do we need the assoc2 too -- add to Sum.v ? *)
Definition eh_assoc {A B C} : (A +' (B +' C)) ~> itree ((A +' B) +' C) :=
  eh_lift Sum1.assoc.
                            


(** Standard interpreters *)

Import ITree.Basics.Monads.

(* TODO: refactor these three... *)

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)


Definition interp_state {E F S} (h : E ~> stateT S (itree F)) :
  itree E ~> stateT S (itree F) :=
  fun R t0 s0 =>
    ITree.aloop (fun st =>
      let s := fst st in let t := snd st in
      match t.(observe) with
      | RetF r => inr (s, r)
      | TauF t => inl (Ret (s, t))
      | VisF e k => inl (ITree.map (fun '(s, x) => (s, k x)) (h _ e s))
      end) (s0, t0).

(** The "reader" and "writer" variants are specializations
    of the above stateful morphisms when the state cannot
    be changed or read (i.e., append only). *)

Definition interp_reader {E F R} (h : R -> E ~> itree F) :
  R -> itree E ~> itree F :=
  fun r => interp (h r).

Definition translate_reader {E F R} (h : R -> E ~> identity) :
  R -> itree E ~> itree F :=
  fun r => interp (fun _ e => Ret (h r _ e)).

Import ExtLib.Structures.Monoid.

Definition map_fst {A A' B} (f : A -> A') : A * B -> A' * B :=
  fun '(a, b) => (f a, b).

Definition interp_writer {E F W} {Monoid_W : Monoid W} (h : E ~> writerT W (itree F)) :
  itree E ~> writerT W (itree F) :=
  fun _ t =>
    interp_state
      (fun _ e s => ITree.map (map_fst (monoid_plus Monoid_W s)) (h _ e))
      _ t (monoid_unit Monoid_W).

(* todo(gmm): this can be stronger if we allow for a `can_returnE` *)
Inductive can_return {E : Type -> Type} {t : Type} : itree E t -> t -> Prop :=
| can_return_Ret {x} : can_return (Ret x) x
| can_return_Tau {tr x} (_ : can_return tr x) : can_return (Tau tr) x
| can_return_Vis {u e k} {x: u} {res} (_ : can_return (k x) res)
  : can_return (Vis e k) res.

(** A propositional "interpreter"
    This can be useful for non-determinism.
 *)
Section interp_prop.
  Context {E F : Type -> Type}.

  Definition eff_hom_prop : Type :=
    forall t, E t -> itree F t -> Prop.

  CoInductive interp_prop (f : eff_hom_prop) (R : Type)
  : itree E R -> itree F R -> Prop :=
  | ipRet : forall x, interp_prop f R (Ret x) (Ret x)
  | ipVis : forall {T} {e : E T} {e' : itree F T}
              (k : _ -> itree E R) (k' : T -> itree F R),
      f _ e e' ->
      (forall x,
          can_return e' x ->
          interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (ITree.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.

(** An extensional stateful handler *)
Section eff_hom_e.
  Context {E F : Type -> Type}.

  (* note(gmm): you should be able to add effects here
   * using a monad transformer. In that case, the type
   * of `eval` is:
   *
   *   forall t, E t -> m (itree F) (t * eff_hom_e)
   *
   * but you have the usual conditions on strictly positive uses
   *)
  CoInductive eff_hom_e : Type :=
  { eval : forall t, E t -> itree F (eff_hom_e * t) }.

  Definition interp_e (h : eff_hom_e) : itree E ~> itree F := fun R t =>
    ITree.aloop (fun '(s, t) =>
      match t.(observe) with
      | RetF r => inr r
      | TauF t => inl (Ret (s, t))
      | VisF e k => inl (ITree.map (fun '(s, x) => (s, k x)) (h.(eval) _ e))
      end) (h, t).

End eff_hom_e.

Section into.
  Context {E F : Type -> Type}.

  Definition into (h : E ~> itree F) : (E +' F) ~> itree F :=
    fun _ e =>
      match e with
      | inl1 e => h _ e
      | inr1 e => ITree.liftE e
      end.

  Definition into_state {s} (h : E ~> stateT s (itree F)) :
    (E +' F) ~> stateT s (itree F) :=
    fun _ e s =>
      match e with
      | inl1 e => h _ e s
      | inr1 e => Vis e (fun x => Ret (s, x))
      end.

  Definition into_reader {R} (h : R -> E ~> itree F) :
    R -> E +' F ~> itree F :=
    fun r _ e =>
      match e with
      | inl1 e => h r _ e
      | inr1 e => ITree.liftE e
      end.

  Definition into_writer {W} (Monoid_W : Monoid W)
             (h : E ~> writerT W (itree F))
    : E +' F ~> writerT W (itree F) :=
    fun _ e =>
      match e with
      | inl1 e => h _ e
      | inr1 e => Vis e (fun x => Ret (monoid_unit Monoid_W, x))
      end.

  (* todo(gmm): is the a corresponding definition for `eff_hom_p`? *)

End into.
