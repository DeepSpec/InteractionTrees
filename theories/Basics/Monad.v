(** * Monad laws and associated typeclasses *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ExtLib Require Export
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function.
(* end hide *)

Set Primitive Projections.

(* Canonical equivalence relation for a unary type family. *)
Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.

(* Proof that [eq1] is an equivalence relation. *)
Class Eq1Equivalence (M : Type -> Type) `{Monad M} `{Eq1 M} :=
  eq1_equiv :> forall A, Equivalence (eq1 A).

Arguments eq1 {M _ _}.
Infix "≈" := eq1 (at level 70) : monad_scope.

Section Laws.

  Context (M : Type -> Type).
  Context {Eq1 : @Eq1 M}.
  Context {Monad : Monad M}.

  Local Open Scope monad_scope.

  (* Monad laws up to [M]'s canonical equivalence relation. *)
  (* This differs coq-ext-lib's [MonadLaws] in that the equiv. relation may be
     distinct from [eq]. *)
  Class MonadLawsE : Prop :=
    { bind_ret_l : forall A B (f : A -> M B) (x : A), bind (ret x) f ≈ f x
    ; bind_ret_r : forall A (x : M A), bind x (fun y => ret y) ≈ x
    ; bind_bind : forall A B C (x : M A) (f : A -> M B) (g : B -> M C),
        bind (bind x f) g ≈ bind x (fun y => bind (f y) g)
    ; Proper_bind :> forall {A B},
        (@Proper (M A -> (A -> M B) -> M B)
         (eq1 ==> pointwise_relation _ eq1 ==> eq1)
         bind)
    }.

End Laws.

Arguments bind_ret_l {M _ _ _}.
Arguments bind_ret_r {M _ _ _}.
Arguments bind_bind {M _ _ _}.
Arguments Proper_bind {M _ _ _}.
