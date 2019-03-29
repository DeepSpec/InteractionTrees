(** * Effect handlers *)

(** Effects [E, F : Type -> Type] and itree [E ~> itree F] form a
    category. *)

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
     Interp.Interp.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

(** ** Handler combinators *)

Module Handler.

(** Lift an _effect morphism_ into an _effect handler_. *)
Definition hsend {A B} (m : A ~> B) : A ~> itree B :=
  fun _ e => ITree.send (m _ e).

(** This handler just wraps effects back into itrees, which is
    a noop (modulo taus): [interp (id_ E) _ t ≈ t]. *)
Definition id_ (E : Type -> Type) : E ~> itree E := ITree.send.

(** Chain handlers: [g] handles the effects produced by [f]. *)
Definition cat {E F G : Type -> Type}
           (f : E ~> itree F) (g : F ~> itree G)
  : E ~> itree G
  := fun R e => interp g (f R e).

(** Wrap effects to the left of a sum. *)
Definition inl_ {E F : Type -> Type} : E ~> itree (E +' F)
  := hsend inl1.

(** Wrap effects to the right of a sum. *)
Definition inr_ {E F : Type -> Type} : F ~> itree (E +' F)
  := hsend inr1.

(** Case analysis on sums of effects. *)
Definition case_ {E F G : Type -> Type}
           (f : E ~> itree G) (g : F ~> itree G)
  : E +' F ~> itree G
  := @case_sum1 E F (itree G) f g.
(* TODO: why is there a universe inconsistency if this is before [inl_] and [inr_]? *)

(** Handle independent effects. *)
Definition bimap {E F G H : Type -> Type}
           (f : E ~> itree G) (g : F ~> itree H)
  : E +' F ~> itree (G +' H)
  := case_ (Handler.cat f inl_) (Handler.cat g inr_).

End Handler.

(** ** Category instances *)

(** This is an indexed generalization of the standard [respectful]
    relation ([==>]). *)
(* TODO: should also take a relation on [A]. *)
Definition i_respectful {A B : Type -> Type} (R : forall t, B t -> B t -> Prop)
           (f g : A ~> B) : Prop :=
  forall X (a : A X), (R X) (f X a) (g X a).

Definition Handler (E F : Type -> Type) := E ~> itree F.

Definition eq_Handler {E F : Type -> Type}
  : Handler E F -> Handler E F -> Prop
  := @i_respectful E (itree F) (fun R => @eq_itree _ _ R eq).

(** The default handler equivalence is [eutt]. *)
Instance Eq2_Handler : Eq2 Handler
  := fun E F
     => @i_respectful E (itree F) (fun R => @eutt _ _ R eq).

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
