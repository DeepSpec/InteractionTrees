(** * Monadic interpretations of interaction trees *)

(** We can derive semantics for an interaction tree [itree E ~> M]
    from semantics given for every individual event [E ~> M],
    when [M] is a monad (actually, with some more structure).

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] stands for [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following:

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "ITree interpreters" (or "itree morphisms") are monad morphisms
      where the codomain is made of ITrees: [itree E ~> itree F].

    Interpreters can be obtained from handlers:

    - In general, "event handlers" are functions [E ~> M] where
      [M] is a monad.

    - "ITree event handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough).
 *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Indexed.Relation.
(* end hide *)

(** ** Translate *)

(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by applying the event morphism to every visible event.  We call this
    process _event translation_.

    Translation is a special case of interpretation:
[[
    translate h t ≈ interp (trigger ∘ h) t
]]
    However this definition of [translate] yields strong bisimulations
    more often than [interp].
    For example, [translate (id_ E) t ≅ id_ (itree E)].
*)

(** A plain event morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {E F R} (h : E ~> F) (rec: itree E R -> itree F R) (t : itreeF E R _) : itree F R  :=
  match t with
  | RetF x => Ret x
  | TauF t => Tau (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

Definition translate {E F} (h : E ~> F)
  : itree E ~> itree F
  := fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F} h [T].

(** ** Interpret *)

(** An event handler [E ~> M] defines a monad morphism
    [itree E ~> M] for any monad [M] with a loop operator. *)

Definition interp {E M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> M) :
  itree E ~> M := fun R =>
  iter (fun t =>
    match observe t with
    | RetF r => ret (inr r)
    | TauF t => ret (inl t)
    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
    end).
(* TODO: this does a map, and aloop does a bind. We could fuse those
   by giving aloop a continuation to compose its bind with.
   (coyoneda...) *)

Arguments interp {E M FM MM IM} h [T].
