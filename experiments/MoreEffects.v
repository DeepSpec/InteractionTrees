Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib.Structures Require Import
     Functor Monoid.

From ITree Require Import
     ITree Morphisms OpenSum.

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
