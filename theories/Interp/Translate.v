(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by mapping the event morphism across each visible event.  We call this
    process _event translation_.


    Translate is defined separately from the itree Morphisms because it is
    conceptually at a different level: translation always yields strong
    bisimulations.  We can relate translation and interpretation via the law:

    translate h t ≈ interp (liftE ∘ h) t
*)

From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Indexed.Sum.

Open Scope itree_scope.

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
