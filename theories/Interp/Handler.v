(** * Effect handlers *)

(** Effects [E, F : Type -> Type] and itree [E ~> itree F] form a
    category. *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITree
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
Definition hlift {A B} (m : A ~> B) : A ~> itree B :=
  fun _ e => ITree.lift (m _ e).

(** This handler just wraps effects back into itrees, which is
    a noop (modulo taus): [interp (id_ E) _ t ≈ t]. *)
Definition id_ (E : Type -> Type) : E ~> itree E := ITree.lift.

(** Chain handlers: [g] handles the effects produced by [f]. *)
Definition cat {E F G : Type -> Type}
           (f : E ~> itree F) (g : F ~> itree G)
  : E ~> itree G
  := fun R e => interp g R (f R e).

(** Wrap effects to the left of a sum. *)
Definition inl_ {E F : Type -> Type} : E ~> itree (E +' F)
  := hlift inl1.

(** Wrap effects to the right of a sum. *)
Definition inr_ {E F : Type -> Type} : F ~> itree (E +' F)
  := hlift inr1.

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



(*



(*  ------------------------------------------------------------------------- *)

A Monad Transformer MT is given by:
  MT : (type -> type) -> (type -> type)
  lift : `{Monad m} {a}, m a -> MT m a

such that:
  Monad (MT m)

  lift o return = return
  lift o (bind t1 k) =

EXAMPLE:
   stateT S m a :=    S -> m (S * a)
   lift : m `{Monad m} {a}, fun (c: m a) (s:S) => y <- c ;; ret (s, y)

operations
  get : m `{Monad m} stateT S m S := fun s => ret_m (s, s)
  put : m `{Monad m}, S -> stateT S m unit := fun s' => fun s => ret_m (s', tt)

(* category *)
id : A ~> MT (itree A)
compose : (B ~> MT2 (itree C)) ~> (A ~> MT1 (itree B)) -> (A ~> (MT2 o MT1) (itree C))

(* co-cartesian *)
par  : (A ~> MT1 (itree B)) -> (C ~> MT2 (itree D)) -> (A + C ~> (MT1 ** MT2) (itree (B + D)))
both : (A ~> MT (itree B)) -> (C ~> (MT itree B)) -> (A + C ~> MT (itree B))

swap : (A ~> MT1 (itree B)) -> (C ~> MT2 (itree D)) -> (A + C ~> (MT2 ** MT1) (itree (D + B)))


left : A ~> MT (itree (A + B))
right : B ~> MT (itree (A + B))

left : (A ~> MT (itree B)) -> (A ~> MT (itree (B + C)))
right : (C ~> MT (itree D)) -> (C ~> MT (itree (A + D)))

(*  ------------------------------------------------------------------------- *)
Algebraic effects handlers

Definition sig (E:Type -> Type) m `{Monad m} := forall X, E X -> m x





*)
