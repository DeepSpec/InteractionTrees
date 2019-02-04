(* Effects form a category where the arrows are effect morphisms.
 *
 * These morphisms can be used to transport itrees from one effect
 * to another.
 *
 * Some morphisms interpret effects using additional structure.
 * In general, this additional structure is monadic in nature.
 *)

From ExtLib.Structures Require Import
     Functor.

From ITree Require Import
     Core OpenSum.

Open Scope itree_scope.

(* * Homomorphisms between effects *)
Definition eff_hom (E E' : Type -> Type) : Type :=
  forall t, E t -> itree E' t.

Definition interp_match {E F R}
           (f : eff_hom E F) (hom : itree E R -> itree F R)
           (ot : itreeF E R _) :=
  match ot with
  | RetF r => Ret r
  | VisF e k => Tau (ITree.bind (f _ e) (fun x => hom (k x)))
  | TauF t' => Tau (hom t')
  end.

(* An `eff_hom` can be used to transport itrees between different
   effects.
 *)
(* N.B.: the guardedness of this definition relies on implementation
   details of [bind]. *)
Definition interp {E F : Type -> Type} {R : Type}
           (f : eff_hom E F)
: itree E R -> itree F R :=
  cofix hom_f t := interp_match f hom_f (observe t).

(*
Lemma match_interp {E F R} {f : eff_hom E F} (t : itree E R) :
  interp f t = interp_match f (fun t' => interp f t') t.
Proof.
  rewrite (match_itree (interp _ _)).
  simpl; rewrite <- match_itree.
  reflexivity.
Qed.
*)

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

Definition eh_id {A} : eff_hom A A := @ITree.liftE A.

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
    match t.(observe) with
    | RetF r => Ret (st, r)
    | VisF e k => ITree.bind (f _ e st) (fun '(s',x) => Tau (interp_state _ (k x) s'))
    | TauF t => Tau (interp_state _ t st)
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
    match t.(observe) with
    | RetF r => Ret r
    | VisF e k => ITree.bind (f _ e st) (fun x => Tau (interp_reader _ (k x) st))
    | TauF t => Tau (interp_reader _ t st)
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

(* todo(gmm): this can be stronger if we allow for a `can_returnE` *)
Inductive can_return {E : Type -> Type} {t : Type} : itree E t -> t -> Prop :=
| can_return_Ret {x} : can_return (Ret x) x
| can_return_Tau {tr x} (_ : can_return tr x) : can_return (Tau tr) x
| can_return_Vis {u e k} {x: u} {res} (_ : can_return (k x) res)
  : can_return (Vis e k) res.

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
      (forall x,
          can_return e' x ->
          interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (ITree.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.

(* * An extensional effect morphism
 *)
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
  { eval : forall t, E t -> itree F (t * eff_hom_e) }.

  CoFixpoint interp_e (f : eff_hom_e) {t} (tr : itree E t)
  : itree F t :=
    match tr.(observe) with
    | RetF v => Ret v
    | VisF e k =>
      ITree.bind (f.(eval) _ e) (fun '(x, f') => Tau (interp_e f' (k x)))
    | TauF tr => Tau (interp_e f tr)
    end.
End eff_hom_e.

Section into.
  Context {E F : Type -> Type}.

  Definition into (h : eff_hom E F) : eff_hom (E +' F) F :=
    fun _ e =>
      match e with
      | inlE e => h _ e
      | inrE e => ITree.liftE e
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
      | inrE e => ITree.liftE e
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
