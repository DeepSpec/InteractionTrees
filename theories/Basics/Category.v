From Coq Require Import
     Setoid Morphisms.


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
Notation "f ⊗ x g" := (@bimap _ x _ _ _ _ _ _ f g)
  (at level 40) : cat_scope.
(* TODO: this bimap notation hides the bifunctor, which may be
   ambiguous. *)

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

Arguments assoc_cat {obj} C {Eq2C CatC AssocCat} [a b c d].
Arguments initial_object : clear implicits.
Arguments initial_object {obj} C {Eq2C} i {Initial_i InitialObject}.

Section BifunctorLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
Context (bif : binop obj).
Context {Bimap_bif : Bimap C bif}.

Class BimapId : Prop :=
  bimap_id : forall a b,
    bimap (id_ a) (id_ b) ⩯ id_ (bif a b).

Class BimapCat : Prop :=
  bimap_cat : forall a1 a2 b1 b2 c1 c2
                     (f1 : C a1 b1) (g1 : C b1 c1)
                     (f2 : C a2 b2) (g2 : C b2 c2),
    bimap (f1 >=> g1) (f2 >=> g2) ⩯ bimap f1 f2 >=> bimap g1 g2.

Class Bifunctor : Prop := {
  bifunctor_bimap_id :> BimapId;
  bifunctor_bimap_cat :> BimapCat;
}.

End BifunctorLaws.

Section CoproductLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
Context (bif : binop obj).
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

Section MonoidalLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
Context (bif : binop obj).

Context {AssocR_bif : AssocR C bif}.
Context {AssocL_bif : AssocL C bif}.

(** [assoc_r] is a split monomorphism, i.e., a left-inverse,
    [assoc_l] is its retraction. *)
Class AssocRMono : Prop :=
  assoc_r_mono : forall a b c,
    assoc_r >=> assoc_l ⩯ id_ (bif (bif a b) c).

(** [assoc_r] is a split epimorphism, i.e., a right-inverse,
    [assoc_l] is its section. *)
Class AssocREpi : Prop :=
  assoc_r_epi : forall a b c,
    assoc_l >=> assoc_r ⩯ id_ (bif a (bif b c)).

Context (I : obj).
Context {UnitL_bif  : UnitL  C bif I}.
Context {UnitL'_bif : UnitL' C bif I}.
Context {UnitR_bif  : UnitR  C bif I}.
Context {UnitR'_bif : UnitR' C bif I}.

(** [unit_l] is a split monomorphism, i.e., a left-inverse,
    [unit_l'] is its retraction. *)
Class UnitLMono : Prop :=
  unit_l_mono : forall a,
    unit_l >=> unit_l' ⩯ id_ (bif I a).

(** [unit_l] is a split epimorphism, [unit_l'] is its section. *)
Class UnitLEpi : Prop :=
  unit_l_epi : forall a,
    unit_l' >=> unit_l ⩯ id_ a.

Class UnitRMono : Prop :=
  unit_r_mono : forall a,
    unit_r >=> unit_r' ⩯ id_ (bif a I).

Class UnitREpi : Prop :=
  unit_r_epi : forall a,
    unit_r' >=> unit_r ⩯ id_ a.

Context {Bimap_bif : Bimap C bif}.

(** The Triangle Diagram *)
Class AssocRUnit : Prop :=
  assoc_r_unit : forall a b,
    assoc_r >=> bimap (id_ a) unit_l ⩯ bimap unit_r (id_ b).

(** The Pentagon Diagram *)
Class AssocRAssocR : Prop :=
  assoc_r_assoc_r : forall a b c d,
          bimap (@assoc_r _ _ _ _ a b c) (id_ d)
      >=> assoc_r
      >=> bimap (id_ _) assoc_r
    ⩯ assoc_r >=> assoc_r.

Class AssocLAssocL : Prop :=
  assoc_l_assoc_l : forall a b c d,
          bimap (id_ a) (@assoc_l _ _ _ _ b c d)
      >=> assoc_l
      >=> bimap assoc_l (id_ _)
    ⩯ assoc_l >=> assoc_l.

End MonoidalLaws.

Section SymmetricLaws.

Context {obj : Type} (C : Hom obj).
Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
Context (bif : binop obj).
Context {Swap_bif : Swap C bif}.

Class SwapInvolutive : Prop :=
  swap_involutive : forall a b,
    swap >=> swap ⩯ id_ (bif a b).

Context (i : obj).
Context {UnitL_i : UnitL C bif i}.
Context {UnitR_i : UnitR C bif i}.

Class SwapUnitL : Prop :=
  swap_unit_l : forall a, swap >=> unit_l ⩯ @unit_r _ _ _ _ _ a.

Context {Bimap_bif : Bimap C bif}.
Context {AssocR_bif : AssocR C bif}.
Context {AssocL_bif : AssocL C bif}.

Class SwapAssocR : Prop :=
  swap_assoc_r : forall a b c,
    @assoc_r _ _ _ _ a _ _ >=> swap >=> assoc_r
  ⩯ bimap swap (id_ c) >=> assoc_r >=> bimap (id_ b) swap.

End SymmetricLaws.

Section CategoryFacts.

Context {obj : Type} (C : Hom obj).

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

Lemma initial_unique :
  forall a (f g : C i a), f ⩯ g.
Proof.
  intros.
  rewrite (initial_object _ i); symmetry; rewrite initial_object.
  reflexivity. auto.
Qed.

End CategoryFacts.

Section BifunctorFacts.

Context {obj : Type} (C : Hom obj).

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.
Context {Proper_cat : forall a b c,
          @Proper (C a b -> C b c -> C a c) (eq2 ==> eq2 ==> eq2) cat}.

Context {Category_C : Category C}.

Context (bif : binop obj).
Context {Bimap_bif : Bimap C bif}
        {Bifunctor_bif : Bifunctor C bif}.
Context {Proper_bimap : forall a b c d,
            @Proper (C a c -> C b d -> C _ _) (eq2 ==> eq2 ==> eq2) bimap}.

Lemma bimap_slide {a b c d} (ac: C a c) (bd: C b d) :
  bimap ac bd ⩯ bimap ac (id_ _) >=> bimap (id_ _) bd.
Proof.
  rewrite <- bimap_cat, cat_id_l, cat_id_r.
  reflexivity.
  all: typeclasses eauto.
Qed.

End BifunctorFacts.

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
Context {Coproduct_C : Coproduct C bif}.
Context {Proper_elim : forall a b c,
            @Proper (C a c -> C b c -> C _ c) (eq2 ==> eq2 ==> eq2) elim}.

Lemma cat_elim
      {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : elim ac bc >=> cd ⩯ elim (ac >=> cd) (bc >=> cd).
Proof.
  eapply elim_universal; [ typeclasses eauto | | ].
  - rewrite <- assoc_cat; [ | typeclasses eauto ].
    rewrite elim_inl; [ | typeclasses eauto ].
    reflexivity.
  - rewrite <- assoc_cat; [ | typeclasses eauto ].
    rewrite elim_inr; [ | typeclasses eauto ].
    reflexivity.
Qed.

Corollary elim_eta {a b} : id_ (bif a b) ⩯ elim coprod_inl coprod_inr.
Proof.
  eapply elim_universal; [ typeclasses eauto | | ].
  all: rewrite cat_id_r; [ reflexivity | typeclasses eauto ].
Qed.

Lemma elim_eta' {a b c} (f : C (bif a b) c) :
  f ⩯ elim (coprod_inl >=> f) (coprod_inr >=> f).
Proof.
  eapply elim_universal; [ typeclasses eauto | | ]; reflexivity.
Qed.

Lemma coprod_split {a b c} (f g : C (bif a b) c) :
  (coprod_inl >=> f ⩯ coprod_inl >=> g) ->
  (coprod_inr >=> f ⩯ coprod_inr >=> g) ->
  f ⩯ g.
Proof.
  intros. rewrite (elim_eta' g).
  eapply elim_universal; auto.
  typeclasses eauto.
Qed.

(** The coproduct is a bifunctor. *)

Global Instance Proper_Bimap_Coproduct {a b c d}:
  @Proper (C a b -> C c d -> _)
          (eq2 ==> eq2 ==> eq2) bimap.
Proof.
  intros ac ac' eqac bd bd' eqbd.
  unfold bimap, Bimap_Coproduct.
  rewrite eqac, eqbd; reflexivity.
Qed.

Global Instance BimapId_Coproduct : BimapId C bif.
Proof.
  intros A B.
  symmetry. unfold bimap, Bimap_Coproduct.
  rewrite 2 cat_id_l.
  apply elim_eta.
  all: typeclasses eauto.
Qed.

Global Instance BimapCat_Coproduct : BimapCat C bif.
Proof.
  red; intros.
  unfold bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite <- assoc_cat, !elim_inl, !assoc_cat, elim_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- assoc_cat, !elim_inr, !assoc_cat, elim_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance Bifunctor_Coproduct : Bifunctor C bif.
Proof.
  constructor; typeclasses eauto.
Qed.

(** It is commutative *)

Global Instance SwapInvolutive_Coproduct : SwapInvolutive C bif.
Proof.
  intros a b.
  unfold swap, Swap_Coproduct.
  rewrite cat_elim, elim_inl, elim_inr.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

(** It is associative *)

Global Instance AssocRMono_Coproduct : AssocRMono C bif.
Proof.
  intros a b c.
  unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_elim.
  rewrite !assoc_cat, !elim_inr, !elim_inl.
  rewrite <- cat_elim, <- elim_eta, cat_id_l, <- elim_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance AssocREpi_Coproduct : AssocREpi C bif.
Proof.
  intros a b c.
  unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_elim.
  rewrite !assoc_cat, !elim_inl, !elim_inr.
  rewrite <- cat_elim, <- elim_eta, cat_id_l, <- elim_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

Global Instance UnitLMono_Coproduct : UnitLMono C bif i.
Proof.
  intros a.
  unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite cat_elim, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

Global Instance UnitRMono_Coproduct : UnitRMono C bif i.
Proof.
  intros a.
  unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite cat_elim, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

Global Instance UnitLEpi_Coproduct : UnitLEpi C bif i.
Proof.
  intros a.
  unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite elim_inr. reflexivity. typeclasses eauto.
Qed.

Global Instance UnitREpi_Coproduct : UnitREpi C bif i.
Proof.
  intros a.
  unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite elim_inl. reflexivity. typeclasses eauto.
Qed.

Lemma coprod_inr_unit_l {a} : coprod_inr >=> unit_l ⩯ id_ a.
Proof.
  apply unit_l_epi. typeclasses eauto.
Qed.

Lemma coprod_inl_unit_r {a} : coprod_inl >=> unit_r ⩯ id_ a.
Proof.
  pose proof (unit_r_epi C bif i a); auto.
Qed.

Global Instance AssocRUnit_Coproduct : AssocRUnit C bif i.
Proof.
  intros a b.
  unfold assoc_r, AssocR_Coproduct, bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  eapply elim_universal.
  all: try typeclasses eauto.
  - rewrite <- assoc_cat, elim_inl.
    rewrite cat_elim, elim_inl.
    unfold unit_r, UnitR_Coproduct.
    rewrite cat_elim, cat_id_l.
    apply Proper_elim.
    reflexivity.
    eapply initial_unique; auto.
    all: typeclasses eauto.
  - rewrite <- assoc_cat, elim_inr.
    rewrite assoc_cat, elim_inr.
    rewrite <- assoc_cat, coprod_inr_unit_l, cat_id_l.
    reflexivity.
    all: typeclasses eauto.
Qed.

(* TODO: automate this *)
Global Instance AssocRAssocR_Coproduct : AssocRAssocR C bif.
Proof.
  intros a b c d.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  rewrite !cat_elim.
  unfold assoc_r, AssocR_Coproduct.
  apply coprod_split. all: try typeclasses eauto.
  - rewrite elim_inl.
    rewrite <- (assoc_cat _ coprod_inl).
    rewrite elim_inl.
    rewrite !assoc_cat.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (assoc_cat _ coprod_inl), !elim_inl).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (assoc_cat _ coprod_inl), !elim_inl).
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (assoc_cat _ coprod_inr), !elim_inr).
        rewrite assoc_cat.
        rewrite <- (assoc_cat _ coprod_inr), !elim_inr.
        rewrite assoc_cat.
        rewrite elim_inr.
        rewrite <- (assoc_cat _ coprod_inl _ coprod_inr), elim_inl.
        rewrite <- assoc_cat, elim_inl.
        reflexivity.
        all: typeclasses eauto.
    + repeat (rewrite <- (assoc_cat _ coprod_inr), !elim_inr).
      rewrite <- (assoc_cat _ coprod_inl), !elim_inl.
      rewrite !assoc_cat.
      rewrite <- (assoc_cat _ coprod_inr (elim _ _) _), !elim_inr.
      rewrite assoc_cat, elim_inr.
      rewrite <- (assoc_cat _ coprod_inl (elim _ _)), elim_inl.
      rewrite <- !assoc_cat, elim_inr.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !elim_inr.
    rewrite !assoc_cat.
    repeat (rewrite <- (assoc_cat _ coprod_inr (elim _ _)), !elim_inr).
    rewrite !assoc_cat, elim_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

(* TODO: automate this. This should follow from the above by symmetry. *)
Global Instance AssocLAssocL_Coproduct : AssocLAssocL C bif.
Proof.
  intros a b c d.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  rewrite !cat_elim.
  unfold assoc_l, AssocL_Coproduct.
  apply coprod_split. all: try typeclasses eauto.
  - rewrite !elim_inl.
    rewrite !assoc_cat.
    repeat (rewrite <- (assoc_cat _ coprod_inl (elim _ _)), !elim_inl).
    rewrite !assoc_cat, elim_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite elim_inr.
    rewrite <- (assoc_cat _ coprod_inr).
    rewrite elim_inr.
    rewrite !assoc_cat.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (assoc_cat _ coprod_inl), !elim_inl).
      rewrite <- (assoc_cat _ coprod_inr), !elim_inr.
      rewrite !assoc_cat.
      rewrite <- (assoc_cat _ coprod_inl (elim _ _) _), !elim_inl.
      rewrite assoc_cat, elim_inl.
      rewrite <- (assoc_cat _ coprod_inr (elim _ _)), elim_inr.
      rewrite <- !assoc_cat, elim_inl.
      reflexivity.
      all: typeclasses eauto.
    + repeat (rewrite <- (assoc_cat _ coprod_inr), !elim_inr).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (assoc_cat _ coprod_inl), !elim_inl).
        rewrite assoc_cat.
        rewrite <- (assoc_cat _ coprod_inl), !elim_inl.
        rewrite assoc_cat.
        rewrite elim_inl.
        rewrite <- (assoc_cat _ coprod_inr _ coprod_inl), elim_inr.
        rewrite <- assoc_cat, elim_inr.
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (assoc_cat _ coprod_inr), !elim_inr).
        reflexivity.
        all: typeclasses eauto.
Qed.

Global Instance SwapUnitL_Coproduct : SwapUnitL C bif i.
Proof.
  intros a.
  unfold swap, Swap_Coproduct, unit_l, UnitL_Coproduct, unit_r, UnitR_Coproduct.
  apply coprod_split.
  - rewrite <- assoc_cat, !elim_inl, elim_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- assoc_cat, !elim_inr, elim_inl.
    reflexivity.
    all: typeclasses eauto.
Qed.

(* TODO: automate *)
Lemma SwapAssocR_Coproduct : SwapAssocR C bif.
Proof.
  intros a b c.
  unfold assoc_r, AssocR_Coproduct, swap, Swap_Coproduct, bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite !assoc_cat.
    rewrite <- 2 (assoc_cat _ coprod_inl), !elim_inl.
    rewrite !assoc_cat.
    rewrite <- (assoc_cat _ coprod_inl), !elim_inl.
    all: try typeclasses eauto.
    apply coprod_split.
    + rewrite <- 2 (assoc_cat _ coprod_inl), !elim_inl.
      rewrite <- assoc_cat. rewrite elim_inl.
      rewrite <- assoc_cat, !elim_inr.
      rewrite assoc_cat, elim_inr.
      rewrite <- assoc_cat, elim_inl.
      reflexivity.
      all: typeclasses eauto.
    + rewrite <- 2 (assoc_cat _ coprod_inr), !elim_inr.
      rewrite assoc_cat.
      rewrite <- (assoc_cat _ coprod_inr), elim_inr, !elim_inl.
      rewrite <- assoc_cat, !elim_inl.
      rewrite cat_id_l.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !assoc_cat.
    rewrite <- 2 (assoc_cat _ coprod_inr), !elim_inr.
    rewrite cat_id_l.
    rewrite assoc_cat, <- (assoc_cat _ coprod_inr (elim _ _) _), !elim_inr, elim_inl, elim_inr.
    rewrite <- assoc_cat.
    rewrite elim_inr, assoc_cat, elim_inr, <- assoc_cat, elim_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Lemma swap_bimap {a b c d} (ab : C a b) (cd : C c d) :
  bimap ab cd ⩯ (swap >=> bimap cd ab >=> swap).
Proof.
  unfold bimap, Bimap_Coproduct, swap, Swap_Coproduct.
  apply coprod_split.
  - rewrite elim_inl.
    rewrite assoc_cat, <- assoc_cat, elim_inl.
    rewrite <- assoc_cat, elim_inr.
    rewrite assoc_cat, elim_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite elim_inr.
    rewrite assoc_cat, <- assoc_cat, elim_inr.
    rewrite <- assoc_cat, elim_inl.
    rewrite assoc_cat, elim_inl.
    reflexivity.
    all: typeclasses eauto.
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
