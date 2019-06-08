(** * The category of continuation trees (KTrees) *)

(** The Kleisli category of ITrees. *)

(* begin hide *)
From ITree Require Import
     Basics.CategoryOps
     Basics.Basics
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

Definition ktree (E: Type -> Type) (A B : Type) : Type
  := Kleisli (itree E) A B.
(* ktree can represent both blocks (A -> block B) and asm (asm A B). *)

Bind Scope ktree_scope with ktree.

(* (@ktree E) forms a traced monoidal category, i.e. a symmetric monoidal one with a loop operator *)
(* Obj ≅ Type *)
(* Arrow: A -> B ≅ terms of type (ktree A B) *)

(** ** KTree equivalence *)
Section Equivalence.

Context {E : Type -> Type}.

Global Instance EqM_ktree : EqM (itree E) := fun A => (@eutt E _ _ eq).

(* We work up to pointwise eutt *)
Definition eutt_ktree {A B} (d1 d2 : ktree E A B) := @Eq2_Kleisli (itree E) _ A B d1 d2.
(*
Definition eutt_ktree {A B} (d1 d2 : ktree E A B) :=
  (forall a, eutt eq (d1 a) (d2 a)).
*)
Global Instance Eq2_ktree : Eq2 (ktree E) := @eutt_ktree.

End Equivalence.

(** *** Conversion to [itree] *)
(** A trick to allow rewriting with eq_ktree in pointful contexts. *)

Definition to_itree {E A} (f : @ktree E unit A) : itree E A := f tt.

Global Instance Proper_to_itree {E A} :
  Proper (eq2 ==> eutt eq) (@to_itree E A).
Proof.
  repeat intro.
  apply H.
Qed.

Lemma fold_to_itree {E} (f : @ktree E unit unit) : f tt = to_itree f.
Proof. reflexivity. Qed.


(** ** Categorical operations *)

Section Operations.

Context {E : Type -> Type}.

Local Notation ktree := (ktree E).

(* Utility function to lift a pure computation into ktree *)
(* SAZ: Maybe call this operation [pure] as in Haskell? *)
Definition lift_ktree {A B} : (A -> B) -> ktree A B := pure.

(** *** Category *)

(** Identity morphism *)
Global Instance Id_ktree : Id_ ktree :=
  fun A a => Ret a.

(** Composition is [ITree.cat], denoted as [>>>]. *)
Global Instance Cat_ktree : Cat ktree := @ITree.cat E.

(** *** Symmetric monoidal category *)

(** Initial object, monoidal unit *)
Local Notation I := Basics.void.

Global Instance Initial_void_ktree : Initial ktree I :=
  fun _ v => match v : I with end.

(** The tensor product is given by the coproduct *)

Global Instance Case_ktree : CoprodCase ktree sum :=
  fun _ _ _ => @case_sum _ _ _.

Local Opaque eutt.

Global Instance Proper_case_ {A B C} :
  @Proper (ktree A C -> ktree B C -> _)
          (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro; destruct a; cbv; auto. apply H. apply H0.
Qed.

Global Instance Inl_ktree : CoprodInl ktree sum :=
  fun _ _ => lift_ktree inl.

Global Instance Inr_ktree : CoprodInr ktree sum :=
  fun _ _ => lift_ktree inr.

(** *** Traced monoidal category *)

Global Instance Iter_ktree : Iter ktree sum :=
  fun A B (f : ktree A (A + B)) (a0 : A) =>
    ITree.aloop (fun ar =>
      match ar with
      | inl a => inl (f a)
      | inr r => inr r
      end) (inl a0) : itree E B.

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

