(** * Monadic interpretations of interaction trees *)

(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by mapping the event morphism across each visible event.  We call this
    process _event translation_.


    Translate is defined separately from the itree Morphisms because it is
    conceptually at a different level: translation always yields strong
    bisimulations.  We can relate translation and interpretation via the law:

    translate h t ≈ interp (send ∘ h) t
*)

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

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition.

(* end hide *)

(** ** Translate *)

(** A plain effect morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {E F R} (h : E ~> F) (rec: itree E R -> itree F R) (t : itreeF E R _) : itree F R  :=
  match t with
  | RetF x => Ret x
  | TauF t => Tau (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

CoFixpoint translate {E F R} (h : E ~> F) (t : itree E R) : itree F R
  := translateF h (translate h) (observe t).

(** ** Interpret *)

(** An effect handler [E ~> M] defines a monad morphism
    [itree E ~> M] for any monad [M] with a loop operator. *)

Definition interp {E M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {LM : ALoop M}
           (h : E ~> M) :
  itree E ~> M := fun R =>
  aloop (fun t =>
    match observe t with
    | RetF r => inr r
    | TauF t => inl (ret t)
    | VisF e k => inl (fmap k (h _ e))
    end).
(* TODO: this does a map, and aloop does a bind. We could fuse those
   by giving aloop a continuation to compose its bind with.
   (coyoneda...) *)

Arguments interp {E M FM MM LM} h [T].
