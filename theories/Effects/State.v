(* begin hide *)
From ExtLib Require Import
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Indexed.Sum
     Interp.Interp.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.
(* end hide *)

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
      | inr1 e => ITree.lift e
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
      | inr1 e => ITree.lift e
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
