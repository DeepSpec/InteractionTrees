From Coq Require Import
     Morphisms
     Program.

Set Universe Polymorphism.

(* TODO: Move this in the library  *)

(** * The Category of Functions *)

(* id : A -> A
   compose : (B -> C) -> (A -> B) -> (A -> C)
   Infix "∘" = compose

   compose_id_right : f ∘ id = f
   compose_id_left : id ∘ f = f
   compose_assoc : (f ∘ g) ∘ h = f ∘ (g ∘ h)
 *)

Hint Rewrite @compose_id_left : cat.
Hint Rewrite @compose_id_right : cat.

(** Extensional function equality *)
Definition eqeq {A B} := (@eq A ==> @eq B)%signature.

Instance Equivalence_eqeq {A B} : Equivalence (@eqeq A B).
Proof.
  constructor; cbv; intros; subst; auto.
  - symmetry; auto.
  - etransitivity; auto.
Qed.

Instance eq_compose {A B C} :
  Proper (eqeq ==> eqeq ==> eqeq) (@compose A B C).
Proof. cbv; auto. Qed.

(** * Diagramatic/categorical sum combinators. *)

Definition sum_elim {A B C} (f : A -> C) (g : B -> C) : A + B -> C :=
  fun x =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

Definition sum_bimap {A B C D} (f : A -> B) (g : C -> D) :
  A + C -> B + D :=
  sum_elim (inl ∘ f) (inr ∘ g).

Definition sum_map_l {A B C} (f : A -> B) : A + C -> B + C :=
  sum_bimap f id.

Definition sum_map_r {A B C} (f : A -> B) : C + A -> C + B :=
  sum_bimap id f.

Definition sum_assoc_r {A B C} (abc : (A + B) + C) : A + (B + C) :=
  match abc with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition sum_comm {A B} : A + B -> B + A :=
  sum_elim inr inl.

Definition sum_assoc_l {A B C} (abc : A + (B + C)) : (A + B) + C :=
  match abc with
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c
  end.

Definition sum_merge {A} : A + A -> A := sum_elim id id.

(** ** Equational theory *)

Lemma compose_sum_elim {A B C D} (ac : A -> C) (bc : B -> C) (cd : C -> D) :
  eqeq (cd ∘ sum_elim ac bc)
       (sum_elim (cd ∘ ac) (cd ∘ bc)).
Proof.
  intros [] ? []; auto.
Qed.

Lemma sum_elim_inl {A B C} (f : A -> C) (g : B -> C) :
  sum_elim f g ∘ inl = f.
Proof. reflexivity. Qed.

Lemma sum_elim_inr {A B C} (f : A -> C) (g : B -> C) :
  sum_elim f g ∘ inr = g.
Proof. reflexivity. Qed.

Lemma sum_elim_inl' {A B C D} (f : A -> C) (g : B -> C) (h : D -> A) :
  sum_elim f g ∘ (inl ∘ h) = f ∘ h.
Proof. reflexivity. Qed.

Lemma sum_elim_inr' {A B C D} (f : A -> C) (g : B -> C) (h : D -> B) :
  sum_elim f g ∘ (inr ∘ h) = g ∘ h.
Proof. reflexivity. Qed.

Lemma unfold_sum_assoc_r {A B C} :
  @sum_assoc_r A B C = sum_elim (sum_elim inl (inr ∘ inl)) (inr ∘ inr).
Proof. cbv; auto. Qed.

Instance eqeq_sum_elim {A B C} :
  Proper (eqeq ==> eqeq ==> eqeq) (@sum_elim A B C).
Proof. cbv; intros; subst; destruct _; auto. Qed.

Hint Rewrite @sum_elim_inl : sum_elim.
Hint Rewrite @sum_elim_inr : sum_elim.
Hint Rewrite @sum_elim_inl' : sum_elim.
Hint Rewrite @sum_elim_inr' : sum_elim.

(** ** Automatic solver of reassociating sums *)

Class ReSum (A B : Type) :=
  resum : A -> B.

Instance ReSum_id A : ReSum A A := id.
Instance ReSum_sum A B C `{ReSum A C} `{ReSum B C} : ReSum (A + B) C :=
  sum_elim resum resum.
Instance ReSum_inl A B C `{ReSum A B} : ReSum A (B + C) :=
  inl ∘ resum.
Instance ReSum_inr A B C `{ReSum A B} : ReSum A (C + B) :=
  inr ∘ resum.

(* Usage template:

[[
Opaque compose.
Opaque id.
Opaque sum_elim.

Definition f {X Y Z} : complex_sum -> another_complex_sum :=
  Eval compute in resum.

Transparent compose.
Transparent id.
Transparent sum_elim.
]]
*)

(** * Bijections *)

Class Iso {A B} (f : A -> B) (f' : B -> A) : Type :=
  { iso_ff' : forall a, f' (f a) = a;
    iso_f'f : forall b, f (f' b) = b;
  }.

Instance Iso_id {A} : Iso (@id A) id := {}.
Proof. all: auto. Qed.

Instance Iso_sum_assoc_l {A B C} : Iso (@sum_assoc_l A B C) sum_assoc_r := {}.
Proof.
  - destruct 0 as [| []]; auto.
  - destruct 0 as [[] |]; auto.
Qed.

Instance Iso_sum_assoc_r {A B C} : Iso (@sum_assoc_r A B C) sum_assoc_l := {}.
Proof.
  - destruct 0 as [[] |]; auto.
  - destruct 0 as [| []]; auto.
Qed.

Instance Iso_compose {A B C} (f : A -> B) (g : B -> C)
         {f' : B -> A} `{Iso _ _ f f'}
         {g' : C -> B} `{Iso _ _ g g'} : Iso (compose g f) (compose f' g') := {}.
Proof.
  all: intro a; cbv; rewrite ?iso_ff', ?iso_f'f; auto.
Qed.

Instance Iso_sum_comm {A B} : @Iso (A + B) _ sum_comm sum_comm := {}.
Proof. all: intros []; auto. Qed.

Instance Iso_sum_bimap {A B C D} (f : A -> B) (g : C -> D)
         {f' : B -> A} `{Iso _ _ f f'}
         {g' : D -> C} `{Iso _ _ g g'} :
  Iso (sum_bimap f g) (sum_bimap f' g') := {}.
Proof.
  all: intros []; cbv; rewrite ?iso_ff', ?iso_f'f; auto.
Qed.
