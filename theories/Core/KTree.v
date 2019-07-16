(** * The category of continuation trees (KTrees) *)

(** The Kleisli category of ITrees. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Basics.MonadTheory
     Basics.CategoryKleisli
     Basics.Function
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Local Open Scope itree_scope.

From Coq Require Import
     Morphisms.
(* end hide *)

Implicit Types E : Type -> Type.
Implicit Types a b : Type.

Notation ktree E := (Kleisli (itree E)).

Bind Scope ktree_scope with ktree.

Notation ktree_apply := (@Kleisli_apply (itree _)).
Notation lift_ktree := (@pure (itree _) _ _ _).
Notation lift_ktree_ E a b := (@pure (itree E) _ a b).

(* [ktree E] forms an iterative category, i.e. a cocartesian category with a
   loop operator *)
(* Obj ≅ Type *)
(* Arrow: A -> B ≅ terms of type (ktree A B) *)


(** ** Categorical operations *)

Section Operations.

Context {E : Type -> Type}.

Local Notation ktree := (ktree E).

(** *** Traced monoidal category *)

(** The trace operator here is [loop].

   We can view a [ktree (I + A) (I + B)] as a circuit, drawn below as [###],
   with two input wires labeled by [I] and [A], and two output wires
   labeled by [I] and [B].

   The [loop : ktree (I + A) (I + B) -> ktree A B] combinator closes
   the circuit, linking the box with itself by plugging the [I] output
   back into the input.
[[
     +-----+
     | ### |
     +-###-+I
  A----###----B
       ###
]]
 *)

End Operations.

Notation iter := (@iter _ (ktree _) sum _ _ _).
Notation loop := (@loop _ (ktree _) sum _ _ _ _ _ _ _ _ _).

