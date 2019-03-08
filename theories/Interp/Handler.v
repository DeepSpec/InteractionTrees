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

Set Universe Polymorphism.
(* end hide *)

(* Morphism Category -------------------------------------------------------- *)

(** * Morphism equivalence *)
Definition Rhom {A B : Type -> Type} (R : forall t, B t -> B t -> Prop)
           (f g : A ~> B) : Prop :=
  forall X (a : A X), (R X) (f X a) (g X a).

Definition eh_eq {A B : Type -> Type}
: (A ~> itree B) -> (A ~> itree B) -> Prop :=
  Rhom (fun t => @eq_itree B _ t eq).

Definition eh_eutt {A B : Type -> Type}
: (A ~> itree B) -> (A ~> itree B) -> Prop :=
  Rhom (fun t => @eutt B _ t eq).

Notation "f ≡ g" := (eh_eutt f g) (at level 70).

Definition eh_cmp {A B C} (g : B ~> itree C) (f : A ~> itree B) :
  A ~> itree C :=
  fun _ e => interp g _ (f _ e).

Definition eh_id {A} : A ~> itree A := @ITree.liftE A.

Definition eh_par {A B C D} (f : A ~> itree B) (g : C ~> itree D)
: (A +' C) ~> itree (B +' D) :=
  fun _ e =>
    match e with
    | inl1 e1 => translate (@inl1 _ _) (f _ e1)
    | inr1 e2 => translate (@inr1 _ _) (g _ e2)
    end.

Definition eh_both {A B C} (f : A ~> itree B) (g : C ~> itree B)
: (A +' C) ~> itree B :=
  fun _ e =>
    match e with
    | inl1 e1 => f _ e1
    | inr1 e2 => g _ e2
    end.

Definition eh_lift {A B} (m : A ~> B)  : A ~> itree B :=
  fun _ e => ITree.liftE (m _ e).

Definition eh_inl {A B} : A ~> itree (A +' B) :=
  eh_lift (fun _ e => inl1 e).

Definition eh_inr {A B} : B ~> itree (A +' B) :=
  eh_lift (fun _ e => inr1 e).

Definition eh_swap {A B} : A +' B ~> itree (B +' A) :=
  eh_lift swap.

Definition eh_elim_empty {A} : void1 ~> itree A :=
  eh_lift empty.

Definition eh_empty_left {B} : void1 +' B ~> itree B :=
  eh_lift unit_l.

Definition eh_empty_right {A} : A +' void1 ~> itree A :=
  eh_lift unit_r.

(* SAZ: do we need the assoc2 too -- add to Sum.v ? *)
Definition eh_assoc {A B C} : (A +' (B +' C)) ~> itree ((A +' B) +' C) :=
  eh_lift assoc_l.



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
