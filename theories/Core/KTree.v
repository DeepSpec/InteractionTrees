(** * The Category of Continuation Trees *)

(** The Kleisli category of ITrees. *)

(* begin hide *)
From ITree Require Import
     Basics.Category
     Basics.Function
     Core.ITree
     Eq.UpToTaus
     Indexed.OpenSum.

Import ITreeNotations.
Local Open Scope itree_scope.

Set Universe Polymorphism.

From Coq Require Import
     Morphisms.
(* end hide *)

Definition ktree (E: Type -> Type) (A B : Type) : Type
  := A -> itree E B.
(* ktree can represent both blocks (A -> block B) and asm (asm A B). *)

Bind Scope ktree_scope with ktree.

(* (@ktree E) forms a traced monoidal category, i.e. a symmetric monoidal one with a loop operator *)
(* Obj ≅ Type *)
(* Arrow: A -> B ≅ terms of type (ktree A B) *)

(** ** KTree equivalence *)
Section Equivalence.

Context {E : Type -> Type}.

(* We work up to pointwise eutt *)
Definition eutt_ktree {A B} (d1 d2 : ktree E A B) :=
  (forall a, eutt eq (d1 a) (d2 a)).

Global Instance Eq2_ktree : Eq2 (ktree E) := @eutt_ktree.

Global Instance Equivalence_eq_ktree {A B} : @Equivalence (ktree E A B) eq2.
Proof.
  split.
  - intros ab a; reflexivity.
  - intros ab ab' eqAB a; symmetry; auto.
  - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
Qed.

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

Let ktree := ktree E.

(* Utility function to lift a pure computation into ktree *)
Definition lift_ktree {A B} (f : A -> B) : ktree A B := fun a => Ret (f a).

(** *** Category *)

(** Identity morphism *)
Global Instance Id_ktree : Id_ ktree :=
  fun A a => Ret a.

(** Composition is [ITree.cat], denoted as [>=>]. *)
Global Instance Cat_ktree : Cat ktree := @ITree.cat E.

(** *** Symmetric monoidal category *)

(** Initial object, monoidal unit *)
Local Notation I := Basics.void.

Global Instance Initial_void_ktree : Initial ktree I :=
  fun _ v => match v : I with end.

(** The tensor product is given by the coproduct *)

Global Instance Elim_ktree : CoprodElim ktree sum :=
  fun _ _ _ => @sum_elim _ _ _.

Local Opaque eutt.

Global Instance Proper_elim {A B C} :
  @Proper (ktree A C -> ktree B C -> _)
          (eq2 ==> eq2 ==> eq2) elim.
Proof.
  repeat intro; destruct a; cbv; auto.
Qed.

Global Instance Inl_ktree : CoprodInl ktree sum :=
  fun _ _ => lift_ktree inl.

Global Instance Inr_ktree : CoprodInr ktree sum :=
  fun _ _ => lift_ktree inr.

(** Traced monoidal category *)

(* The trace is [Fix.loop].

   A [box : ktree (I + A) (I + B)] is a circuit, drawn below as ###,
   with two input wires labeled by I and A, and two output wires
   labeled by I and B.

   The [loop_ktree : ktree (I + A) (I + B) -> ktree A B] combinator closes
   the circuit, linking the box with itself by plugging the I output
   back into the input.

     +-----+
     | ### |
     +-###-+I
  A----###----B
       ###

 *)

End Operations.

Definition loop_once {E : Type -> Type} {A B C : Type}
           (body : C + A -> itree E (C + B))
           (loop_ : C + A -> itree E B) : C + A -> itree E B :=
  fun ca =>
    cb <- body ca ;;
    match cb with
    | inl c => loop_ (inl c)
    | inr b => Ret b
    end.

Definition loop_ {E : Type -> Type} {A B C : Type}
           (body : C + A -> itree E (C + B)) :
  C + A -> itree E B :=
  cofix loop__ := loop_once body (fun cb => Tau (loop__ cb)).

(** Iterate a function updating an accumulator [C],
    until it produces an output [B]. An encoding of tail recursive
    functions.

    The Kleisli category for the [itree] monad is a traced
    monoidal category, with [loop] as its trace.
 *)
(* We use explicit recursion instead of relying on [rec] to
   make the definition properly tail recursive. *)
Definition loop {E : Type -> Type} {A B C : Type}
           (body : (C + A) -> itree E (C + B)) :
  A -> itree E B :=
  fun a => loop_ body (inr a).