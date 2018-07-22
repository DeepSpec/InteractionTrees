(* Effects form a category where the arrows are effect morphisms.
 *
 * These morphisms can be used to transport itrees from one effect
 * to another.
 *
 * Some morphisms interpret effects using additional structure.
 * In general, this additional structure is monadic in nature.
 *)
Require Import ITree.ITree.
Require Import ExtLib.Structures.Functor.

(* * Homomorphisms between effects *)
Definition eff_hom (E E' : Type -> Type) : Type :=
  forall t, E t -> itree E' t.

(* An `eff_hom` can be used to transport itrees between different effects.
 *)
Definition interp {E F : Type -> Type}
           (f : eff_hom E F) (R : Type)
: itree E R -> itree F R :=
  cofix hom_f t :=
    match t with
    | Ret r => Ret r
    | Vis e k => Core.bindTau (f _ e) (fun x => hom_f (k x))
    | Tau t => Tau (hom_f t)
    end.
Arguments interp {E F} _ [R] _.

(* * Effects form a category
 * The objects are effects: i.e. `Type -> Type`
 * The morphisms from `a` to `b` are `eff_hom a b`
 *)

(* todo(gmm): it would be good to have notation for this.
 * - if there was a "category" class like in Haskell, then we could
 *   get composition from something like that.
 *)
Definition eh_compose {A B C} (g : eff_hom B C) (f : eff_hom A B)
: eff_hom A C :=
  fun _ e =>
    interp g (f _ e).

Definition eh_id {A} : eff_hom A A :=
  fun _ e => Vis e Ret.

Section eff_hom_state.
  Variable s : Type.
  Variable E E' : Type -> Type.

  (* * Stateful homomorphisms between effects *)
  Definition eff_hom_s : Type :=
    forall t, E t -> s -> itree E' (s * t).

  (* question(gmm): Should we export this using `stateT`? That is,
   *
   * interp_state {E F S} (f : eff_hom_s S E F) (R : Type)
   *   itree E R -> stateT S (itree F) R.
   *
   * a nice benefit of this is that it makes the structure a bit more
   * explicit (and hints at the generalization to arbitary monads).
   *)
  Variable f : eff_hom_s.
  CoFixpoint interp_state (R : Type) (t : itree E R) (st : s)
  : itree E' (s * R) :=
    match t with
    | Ret r => Ret (st, r)
    | Vis e k => Core.bindTau (f _ e st) (fun '(s',x) => interp_state _ (k x) s')
    | Tau t => Tau (interp_state _ t st)
    end.
End eff_hom_state.
Arguments interp_state {_ _ _} _ [_] _ _.

(* * Reader homomorphisms between effects *)
Section eff_hom_reader.
  Variable s : Type.
  Variable E E' : Type -> Type.

  Definition eff_hom_r : Type :=
    forall t, E t -> s -> itree E' t.

  Variable f : eff_hom_r.
  CoFixpoint interp_reader (R : Type) (t : itree E R) (st : s) : itree E' R :=
    match t with
    | Ret r => Ret r
    | Vis e k => Core.bindTau (f _ e st) (fun x => interp_reader _ (k x) st)
    | Tau t => Tau (interp_reader _ t st)
    end.

End eff_hom_reader.

Arguments interp_reader {_ _ _} _ [_] _ _.

Require Import ExtLib.Structures.Monoid.

(* * Writer homomorphisms between effects *)
Section eff_hom_writer.
  Variable s : Type.
  Variable E E' : Type -> Type.

  Definition eff_hom_w : Type :=
    forall t, E t -> itree E' (s * t).

  Context {Monoid_s : Monoid s}.
  Variable f : eff_hom_w.

  (* Note that we have to give an intepretation in terms of state in order
   * to pass the productivity checker. This definition is equivalent to:
   *
   * CoFixpoint interp_reader (R : Type) (t : itree E R) (st : s) : itree E' R :=
   *   match t with
   *   | Ret r => Ret r
   *   | Vis e k => Core.bindTau (f _ e st)
   *     (fun x => fmap (fun '(s',x) => (monoid_plus Monoid_s s s', x))
   *                    (interp_writer _ (k x) st))
   *   | Tau t => Tau (interp_writer _ t st)
   *   end.
   *)
  Definition interp_writer (R : Type) (t : itree E R) : itree E' (s * R) :=
    interp_state
      (fun _ e s => fmap (fun '(s',x) => (monoid_plus Monoid_s s s', x)) (f _ e))
      t (monoid_unit Monoid_s).

End eff_hom_writer.

Arguments interp_writer {_ _ _ _} _ [_] _.

(* A propositional "interpreter"
 * This can be useful for non-determinism.
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
      (forall x, interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (Core.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.