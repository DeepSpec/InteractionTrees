(** * The Category of Continuation Trees *)

(** The Kleisli category of ITrees. *)

(* begin hide *)
From ITree Require Import
     Basics.Functions
     Core.ITree
     Eq.UpToTaus
     Indexed.OpenSum.

Import ITreeNotations.
Local Open Scope itree_scope.

From Coq Require Import
     Program
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
Definition eq_ktree {A B} (d1 d2 : ktree E A B) :=
  (forall a, eutt eq (d1 a) (d2 a)).

Global Instance Equivalence_eq_ktree {A B} : Equivalence (@eq_ktree A B).
Proof.
  split.
  - intros ab a; reflexivity.
  - intros ab ab' eqAB a; symmetry; auto.
  - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
Qed.

Global Instance eq_ktree_elim {A B C} :
  Proper (eq_ktree ==> eq_ktree ==> eq_ktree) (@sum_elim A B (itree E C)).
Proof.
  repeat intro. destruct a; unfold sum_elim; auto.
Qed.

End Equivalence.

Infix "⩯" := eq_ktree (at level 70).

(** *** Conversion to [itree] *)
(** A trick to allow rewriting with eq_ktree in pointful contexts. *)

Definition to_itree {E} (f : @ktree E unit unit) : itree E unit := f tt.

Global Instance Proper_to_itree {E} :
  Proper (eq_ktree ==> eutt eq) (@to_itree E).
Proof.
  repeat intro.
  apply H.
Qed.

Lemma fold_to_itree {E} (f : @ktree E unit unit) : f tt = to_itree f.
Proof. reflexivity. Qed.


(** ** Categorical operations *)

Section Operations.

Context {E : Type -> Type}.

(* Utility function to lift a pure computation into ktree *)
Definition lift_ktree {A B} (f : A -> B) : ktree E A B := fun a => Ret (f a).

(** *** Category *)

(** Identity morphism *)
Definition id_ktree {A} : ktree E A A := fun a => Ret a.

(** Composition is [ITree.cat], denoted as [>=>]. *)

(** *** Symmetric monoidal category *)

(** Monoidal unit *)
Definition I: Type := Empty_set.

(** Tensor product *)
(* Tensoring on objects is given by the coproduct *)
Definition tensor_ktree {A B C D}
           (ab : ktree E A B) (cd : ktree E C D)
  : ktree E (A + C) (B + D)
  := sum_elim (ab >=> lift_ktree inl) (cd >=> lift_ktree inr).

(* Left and right unitors *)
Definition λ_ktree  {A: Type}: ktree E (I + A) A := lift_ktree sum_empty_l.
Definition λ_ktree' {A: Type}: ktree E A (I + A) := lift_ktree inr.
Definition ρ_ktree  {A: Type}: ktree E (A + I) A := lift_ktree sum_empty_r.
Definition ρ_ktree' {A: Type}: ktree E A (A + I) := lift_ktree inl.

(* Associators *)
Definition assoc_ktree_l {A B C: Type}: ktree E (A + (B + C)) ((A + B) + C) := lift_ktree sum_assoc_l.
Definition assoc_ktree_r {A B C: Type}: ktree E ((A + B) + C) (A + (B + C)) := lift_ktree sum_assoc_r.

(* Symmetry *)
Definition sym_ktree {A B: Type}: ktree E (A + B) (B + A) := lift_ktree sum_comm.

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

Infix "⊗" := (tensor_ktree) (at level 30).

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
