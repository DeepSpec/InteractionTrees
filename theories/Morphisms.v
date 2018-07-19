(* Effects form a category where the arrows are effect morphisms
 *)
Require Import ITree.ITree.

(* * Homomorphisms between effects *)
Definition eff_hom (E E' : Type -> Type) : Type :=
  forall t, E t -> itree E' t.

(** If we can interpret the effects of a tree as computations in
    another, we can extend that interpretation to the whole tree. *)
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

(* * Stateful homomorphisms between effects *)
Definition eff_hom_s (s : Type) (E E' : Type -> Type) : Type :=
  forall t, E t -> s -> itree E' (s * t).

(* question(gmm): Should we export this using `stateT`? That is,
 *
 * interp_state {E F S} (f : eff_hom_s S E F) (R : Type)
 *   itree E R -> stateT S (itree F) R.
 *
 * a nice benefit of this is that it makes the structure a bit more
 * explicit (and hints at the generalization to arbitary monads).
 *)
Definition interp_state {E F : Type -> Type} {S : Type}
           (f : eff_hom_s S E F) (R : Type)
: itree E R -> S -> itree F (S * R) :=
  cofix homState_f t s :=
    match t with
    | Ret r => Ret (s, r)
    | Vis e k => Core.bindTau (f _ e s) (fun '(s',x) => homState_f (k x) s')
    | Tau t => Tau (homState_f t s)
    end.
Arguments interp_state {_ _ _} _ [_] _.
