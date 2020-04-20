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
From ITree Require Import
     Basics.Basics
     Basics.Monad
     Basics.MonadEither
     Core.ITreeDefinition
     Indexed.Relation.
(* end hide *)

Definition interp_either {E M : Type -> Type} {A: Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> eitherT A M) :
  eitherT A (itree E) ~> eitherT A M :=
  fun R => iter (fun t =>
                match observe (unEitherT t) with
                | RetF (inl a) => mkEitherT (ret (inl a))
                | RetF (inr r) => ret (inr r)
                | TauF t => ret (inl (mkEitherT t))
                | VisF e k => fmap (fun x => inl (mkEitherT (k x))) (h _ e)
                end).

Definition interp_either' {E M : Type -> Type} {A: Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> M) :
  eitherT A (itree E) ~> eitherT A M :=
  fun R => iter (fun t =>
                match observe (unEitherT t) with
                | RetF (inl a) => mkEitherT (ret (inl a))
                | RetF (inr r) => ret (inr r)
                | TauF t => ret (inl (mkEitherT t))
                | VisF e k => fmap (fun x => inl (mkEitherT (k x))) (MonadTrans.lift (h _ e))
                end).

Arguments interp_either {E M A FM MM IM} h [T].
