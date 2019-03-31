(** * Event handlers *)

(** Events types [E, F : Type -> Type] and itree [E ~> itree F]
    form a category. *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Interp.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

(** ** Handler combinators *)

Module Handler.

(** Lift an _event morphism_ into an _event handler_. *)
Definition htrigger {A B} (m : A ~> B) : A ~> itree B :=
  fun _ e => ITree.trigger (m _ e).

(** Trivial handler, triggering any event it's given, so
    the resulting interpretation is the identity function:
    [interp (id_ E) _ t ≈ t]. *)
Definition id_ (E : Type -> Type) : E ~> itree E := ITree.trigger.

(** Chain handlers: [g] handles the events produced by [f]. *)
Definition cat {E F G : Type -> Type}
           (f : E ~> itree F) (g : F ~> itree G)
  : E ~> itree G
  := fun R e => interp g (f R e).

(** Wrap events to the left of a sum. *)
Definition inl_ {E F : Type -> Type} : E ~> itree (E +' F)
  := htrigger inl1.

(** Wrap events to the right of a sum. *)
Definition inr_ {E F : Type -> Type} : F ~> itree (E +' F)
  := htrigger inr1.

(** Case analysis on sums of events. *)
Definition case_ {E F G : Type -> Type}
           (f : E ~> itree G) (g : F ~> itree G)
  : E +' F ~> itree G
  := @case_sum1 E F (itree G) f g.
(* TODO: why is there a universe inconsistency if this is before [inl_] and [inr_]? *)

(** Handle events independently, with disjoint sets of output events. *)
Definition bimap {E F G H : Type -> Type}
           (f : E ~> itree G) (g : F ~> itree H)
  : E +' F ~> itree (G +' H)
  := case_ (Handler.cat f inl_) (Handler.cat g inr_).

End Handler.

(** ** Category instances *)

Definition Handler (E F : Type -> Type) := E ~> itree F.

Definition eq_Handler {E F : Type -> Type}
  : Handler E F -> Handler E F -> Prop
  := i_pointwise (fun R => eq_itree eq).

Definition eutt_Handler {E F : Type -> Type}
  : Handler E F -> Handler E F -> Prop
  := i_pointwise (fun R => eutt eq).

(** The default handler equivalence is [eutt]. *)
Instance Eq2_Handler : Eq2 Handler
  := @eutt_Handler.

Instance Id_Handler : Id_ Handler
  := @Handler.id_.

Instance Cat_Handler : Cat Handler
  := @Handler.cat.

Instance Case_sum1_Handler : CoprodCase Handler sum1
  := @Handler.case_.

Instance Inl_sum1_Handler : CoprodInl Handler sum1
  := @Handler.inl_.

Instance Inr_sum1_Handler : CoprodInr Handler sum1
  := @Handler.inr_.

Instance Initial_void1_Handler : Initial Handler void1
  := fun _ _ v => match v : void1 _ with end.
