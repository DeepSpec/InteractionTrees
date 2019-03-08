From Coq Require Import
     Setoid Morphisms.

Set Universe Polymorphism.

Local Notation Hom obj := (obj -> obj -> Type).
Local Notation binop obj := (obj -> obj -> obj).

Delimit Scope cat_scope with cat.

Section CatOps.

Context {obj : Type} (C : Hom obj).

Class Eq2 : Type :=
  eq2 : forall a b (f g : C a b), Prop.

Class Id_ : Type :=
  id_ : forall a, C a a.

Class Cat : Type :=
  cat : forall a b c, C a b -> C b c -> C a c.

Class Initial (i : obj) :=
  empty : forall a, C i a.

End CatOps.

Arguments eq2 {obj C Eq2 a b}.
Arguments id_ {obj C Id_}.
Arguments cat {obj C Cat a b c}.
Arguments empty {obj C i Initial a}.

Section CocartesianOps.

Context {obj : Type} (C : Hom obj) (bif : binop obj).

(** *** Bifctor *)

Class Bimap :=
  bimap : forall a b c d, C a c -> C b d -> C (bif a b) (bif c d).

(** *** Coproduct *)

Class CoprodElim :=
  elim : forall a b c, C a c -> C b c -> C (bif a b) c.

Class CoprodInl :=
  coprod_inl : forall a b, C a (bif a b).

Class CoprodInr :=
  coprod_inr : forall a b, C b (bif a b).

(** *** Tensor (monoidal) *)

Class AssocR :=
  assoc_r : forall a b c, C (bif (bif a b) c) (bif a (bif b c)).

Class AssocL :=
  assoc_l : forall a b c, C (bif a (bif b c)) (bif (bif a b) c).

Class UnitL (i : obj) :=
  unit_l : forall a, C (bif i a) a.

Class UnitL' (i : obj) :=
  unit_l' : forall a, C a (bif i a).

Class UnitR (i : obj) :=
  unit_r : forall a, C (bif a i) a.

Class UnitR' (i : obj) :=
  unit_r' : forall a, C a (bif a i).

(** *** Symmetry *)

Class Swap :=
  swap : forall a b, C (bif a b) (bif b a).

End CocartesianOps.

Arguments bimap {obj C bif Bimap a b c d}.
Arguments elim {obj C bif CoprodElim a b c}.
Arguments coprod_inl {obj C bif CoprodInl a b}.
Arguments coprod_inr {obj C bif CoprodInr a b}.
Arguments assoc_r {obj C bif AssocR a b c}.
Arguments assoc_l {obj C bif AssocL a b c}.
Arguments unit_l  {obj C bif i UnitL a}.
Arguments unit_l' {obj C bif i UnitL' a}.
Arguments unit_r  {obj C bif i UnitR a}.
Arguments unit_r' {obj C bif i UnitR' a}.
Arguments swap {obj C bif Swap a b}.

Notation elim_ C := (@elim _ C _ _ _ _ _)
  (only parsing).

Module Import CatNotations.

Infix "⩯" := eq2 (at level 70) : cat_scope.
Infix ">=>" := cat (at level 50, left associativity) : cat_scope.
Notation "f ⊗ x g" := (@bimap _ x _ _ _ _ _ f g)
  (at level 40) : cat_scope.

End CatNotations.

Local Open Scope cat.

(** ** Derived constructions *)

Definition merge {obj : Type} {C : Hom obj} {bif : binop obj}
           {Id_C : Id_ C} {Coproduct_C : CoprodElim C bif}
  : forall {a : obj}, C (bif a a) a :=
  fun a => elim (id_ a) (id_ a).

Section CocartesianConstruct.

Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).
Variables (SUM : binop obj) (Coprod_SUM : CoprodElim C SUM)
          (CoprodInl_SUM : CoprodInl C SUM)
          (CoprodInr_SUM : CoprodInr C SUM).

Global Instance Bimap_Coproduct : Bimap C SUM :=
  fun a b c d (f : C a c) (g : C b d) =>
    elim (f >=> coprod_inl) (g >=> coprod_inr).

Global Instance Swap_Coproduct : Swap C SUM :=
  fun a b => elim coprod_inr coprod_inl.

Global Instance AssocR_Coproduct : AssocR C SUM :=
  fun a b c => elim (elim coprod_inl (coprod_inl >=> coprod_inr))
                    (coprod_inr >=> coprod_inr).

Global Instance AssocL_Coproduct : AssocL C SUM :=
  fun a b c => elim (coprod_inl >=> coprod_inl)
                    (elim (coprod_inr >=> coprod_inl) coprod_inr).

Variables (Id_C : Id_ C) (I : obj) (Initial_I : Initial C I).

Global Instance UnitL_Coproduct : UnitL C SUM I :=
  fun a => elim empty (id_ a).

Global Instance UnitL'_Coproduct : UnitL' C SUM I :=
  fun a => coprod_inr.

Global Instance UnitR_Coproduct : UnitR C SUM I :=
  fun a => elim (id_ a) empty.

Global Instance UnitR'_Coproduct : UnitR' C SUM I :=
  fun a => coprod_inl.

End CocartesianConstruct.

(** * Laws *)

Section CatLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2C : Eq2 C} {IdC : Id_ C} {CatC : Cat C}.

Class CatIdL : Prop :=
  cat_id_l : forall a b (f : C a b), id_ _ >=> f ⩯ f.

Class CatIdR : Prop :=
  cat_id_r : forall a b (f : C a b), f >=> id_ _ ⩯ f.

Class AssocCat : Prop :=
  assoc_cat : forall a b c d (f : C a b) (g : C b c) (h : C c d),
      (f >=> g) >=> h ⩯ f >=> (g >=> h).

Class Category : Prop := {
  category_cat_id_l :> CatIdL;
  category_cat_id_r :> CatIdR;
  category_assoc_cat :> AssocCat;
}.

Class InitialObject (i : obj) {Initial_i : Initial C i} : Prop :=
  initial_object : forall a (f : C i a), f ⩯ empty.

End CatLaws.

Section CoproductLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
Context {bif : binop obj}.
Context {CoprodElim_C : CoprodElim C bif}
        {CoprodInl_C : CoprodInl C bif}
        {CoprodInr_C : CoprodInr C bif}.

Class ElimInl : Prop :=
  elim_inl : forall a b c (f : C a c) (g : C b c),
    coprod_inl >=> elim f g ⩯ f.

Class ElimInr : Prop :=
  elim_inr : forall a b c (f : C a c) (g : C b c),
    coprod_inr >=> elim f g ⩯ g.

Class ElimUniversal : Prop :=
  elim_universal :
    forall a b c (f : C a c) (g : C b c) (fg : C (bif a b) c),
      (coprod_inl >=> fg ⩯ f) ->
      (coprod_inr >=> fg ⩯ g) ->
      fg ⩯ elim f g.

Class Coproduct : Prop := {
  coproduct_elim_inl :> ElimInl;
  coproduct_elim_inr :> ElimInr;
  coproduct_elim_universal :> ElimUniversal;
}.

End CoproductLaws.

Section CoproductFacts.

Context {obj : Type} (C : Hom obj).

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.
Context {Proper_cat : forall a b c,
          @Proper (C a b -> C b c -> C a c) (eq2 ==> eq2 ==> eq2) cat}.

Context {Category_C : Category C}.

Context (bif : binop obj).
Context {CoprodElim_C : CoprodElim C bif}
        {CoprodInl_C : CoprodInl C bif}
        {CoprodInr_C : CoprodInr C bif}.
Context {Coproduct_C : Coproduct C}.

Lemma cat_elim
      {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : elim ac bc >=> cd ⩯ elim (ac >=> cd) (bc >=> cd).
Proof.
  apply (elim_universal _).
  - rewrite <- assoc_cat; [ | typeclasses eauto ].
    rewrite elim_inl; [ | typeclasses eauto ].
    reflexivity.
  - rewrite <- assoc_cat; [ | typeclasses eauto ].
    rewrite elim_inr; [ | typeclasses eauto ].
    reflexivity.
Qed.

End CoproductFacts.

Hint Rewrite @elim_inl : cocartesian.
Hint Rewrite @elim_inr : cocartesian.

(** ** Automatic solver of reassociating sums *)

Section RESUM.

Context {obj : Type} (C : Hom obj) (bif : binop obj).
Context `{Id_ _ C} `{Cat _ C}.
Context `{CoprodElim _ C bif} `{CoprodInl _ C bif} `{CoprodInr _ C bif}.

Class ReSum (a b : obj) :=
  resum : C a b.

Global Instance ReSum_id `{Id_ _ C} a : ReSum a a := { resum := id_ a }.
Global Instance ReSum_sum a b c
         `{ReSum a c} `{ReSum b c} : ReSum (bif a b) c :=
  { resum := elim resum resum }.
Global Instance ReSum_inl a b c `{ReSum a b} : ReSum a (bif b c) :=
  { resum := resum >=> coprod_inl }.
Global Instance ReSum_inr a b c `{ReSum a b} : ReSum a (bif c b) :=
  { resum := resum >=> coprod_inr }.

(* Usage template:

[[
Opaque cat.
Opaque id.
Opaque elim.
Opaque coprod_inl.
Opaque coprod_inr.

    (* where the category is (->)  vv *)
Definition f {X Y Z} : complex_sum -> another_complex_sum :=
  Eval compute in resum.

Transparent cat.
Transparent id.
Transparent elim.
Transparent coprod_inl.
Transparent coprod_inr.
]]
*)

End RESUM.
