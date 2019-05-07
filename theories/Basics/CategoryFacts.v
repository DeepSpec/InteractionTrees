(** * General facts about categories *)

(* begin hide *)
From Coq Require Import
     Setoid Morphisms.

From ITree.Basics Require Import
     CategoryOps CategoryTheory.

Import Carrier.
Import CatNotations.
Local Open Scope cat.
(* end hide *)

(** ** Isomorphisms *)

Section IsoFacts.

Context {obj : Type} (C : Hom obj).
Context {Eq2C : Eq2 C} {IdC : Id_ C} {CatC : Cat C}.

Context {CatIdL_C : CatIdL C}.

(** [id_] is an isomorphism. *)
Global Instance SemiIso_Id {a} : SemiIso C (id_ a) (id_ a) := {}.
Proof. apply cat_id_l; assumption. Qed.

Context {Equivalence_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Section IsoCat.

Context {CatAssoc_C : CatAssoc C}.
Context {Proper_Cat_C : forall a b c,
            @Proper (C a b -> C b c -> _) (eq2 ==> eq2 ==> eq2) cat}.

(** Isomorphisms are closed under [cat]. *)
Global Instance SemiIso_Cat {a b c}
       (f : C a b) {f' : C b a} {SemiIso_f : SemiIso C f f'}
       (g : C b c) {g' : C c b} {SemiIso_g : SemiIso C g g'}
  : SemiIso C (f >>> g) (g' >>> f') := {}.
Proof.
  rewrite cat_assoc, <- (cat_assoc _ g), (semi_iso g), cat_id_l,
  (semi_iso f).
  reflexivity. all: typeclasses eauto.
Qed.

End IsoCat.

Section IsoBimap.

Context (bif : binop obj).
Context {Bimap_bif : Bimap C bif}.
Context {BimapId_bif : BimapId C bif}.
Context {BimapCat_bif : BimapCat C bif}.
Context {Proper_Bimap_bif : forall a b c d,
            @Proper (C a b -> C c d -> _) (eq2 ==> eq2 ==> eq2) bimap}.

(** Isomorphisms are closed under [bimap]. *)
Global Instance SemiIso_Bimap {a b c d} (f : C a b) (g : C c d)
         {f' : C b a} {SemiIso_f : SemiIso C f f'}
         {g' : C d c} {SemiIso_g : SemiIso C g g'} :
  SemiIso C (bimap f g) (bimap f' g') := {}.
Proof.
  rewrite bimap_cat, (semi_iso f), (semi_iso g), bimap_id.
  reflexivity. all: typeclasses eauto.
Qed.

End IsoBimap.

End IsoFacts.

(** ** Categories *)

Section CategoryFacts.

Context {obj : Type} (C : Hom obj).

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

(** The initial morphism is unique. *)
Lemma initial_unique :
  forall a (f g : C i a), f ⩯ g.
Proof.
  intros.
  rewrite (initial_object _ i); symmetry; rewrite initial_object.
  reflexivity. auto.
Qed.

End CategoryFacts.

(** ** Bifunctors *)

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
  bimap ac bd ⩯ bimap ac (id_ _) >>> bimap (id_ _) bd.
Proof.
  rewrite bimap_cat, cat_id_l, cat_id_r.
  reflexivity.
  all: typeclasses eauto.
Qed.

Lemma bimap_slide' {a b c d} (ac: C a c) (bd: C b d) :
  bimap ac bd ⩯ bimap (id_ _) bd >>> bimap ac (id_ _).
Proof.
  rewrite bimap_cat, cat_id_l, cat_id_r.
  reflexivity.
  all: typeclasses eauto.
Qed.

End BifunctorFacts.

(** ** Coproducts *)

Section CoproductFacts.

Context {obj : Type} (C : Hom obj).

Context {Eq2_C : Eq2 C}.
Context {E_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Context {Id_C : Id_ C} {Cat_C : Cat C}.
Context {Proper_cat : forall a b c,
          @Proper (C a b -> C b c -> C a c) (eq2 ==> eq2 ==> eq2) cat}.

Context {Category_C : Category C}.

Context (bif : binop obj).
Context {CoprodCase_C : CoprodCase C bif}
        {CoprodInl_C : CoprodInl C bif}
        {CoprodInr_C : CoprodInr C bif}.
Context {Coproduct_C : Coproduct C bif}.
Context {Proper_case_ : forall a b c,
            @Proper (C a c -> C b c -> C _ c) (eq2 ==> eq2 ==> eq2) case_}.

(** Commute [cat] and [case_]. *)
Lemma cat_case
      {a b c d} (ac : C a c) (bc : C b c) (cd : C c d)
  : case_ ac bc >>> cd ⩯ case_ (ac >>> cd) (bc >>> cd).
Proof.
  eapply case_universal; [ typeclasses eauto | | ].
  - rewrite <- cat_assoc; [ | typeclasses eauto ].
    rewrite case_inl; [ | typeclasses eauto ].
    reflexivity.
  - rewrite <- cat_assoc; [ | typeclasses eauto ].
    rewrite case_inr; [ | typeclasses eauto ].
    reflexivity.
Qed.

(** Case analysis with projections is the identity. *)
Corollary case_eta {a b} : id_ (bif a b) ⩯ case_ inl_ inr_.
Proof.
  eapply case_universal; [ typeclasses eauto | | ].
  all: rewrite cat_id_r; [ reflexivity | typeclasses eauto ].
Qed.

Lemma case_eta' {a b c} (f : C (bif a b) c) :
  f ⩯ case_ (inl_ >>> f) (inr_ >>> f).
Proof.
  eapply case_universal; [ typeclasses eauto | | ]; reflexivity.
Qed.

(** We can prove the equivalence of morphisms on coproducts
    by case analysis. *)
Lemma coprod_split {a b c} (f g : C (bif a b) c) :
  (inl_ >>> f ⩯ inl_ >>> g) ->
  (inr_ >>> f ⩯ inr_ >>> g) ->
  f ⩯ g.
Proof.
  intros. rewrite (case_eta' g).
  eapply case_universal; auto.
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
  apply case_eta.
  all: typeclasses eauto.
Qed.

Global Instance BimapCat_Coproduct : BimapCat C bif.
Proof.
  red; intros.
  unfold bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite <- cat_assoc, !case_inl, !cat_assoc, case_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, !case_inr, !cat_assoc, case_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance Bifunctor_Coproduct : Bifunctor C bif.
Proof.
  constructor; typeclasses eauto.
Qed.

(** The coproduct is commutative *)

Global Instance SwapInvolutive_Coproduct {a b : obj}
  : SemiIso C (swap_ a b) swap.
Proof.
  red; unfold swap, Swap_Coproduct.
  rewrite cat_case, case_inl, case_inr.
  symmetry; apply case_eta.
  all: typeclasses eauto.
Qed.

(** The coproduct is associative *)

Global Instance AssocRMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_r_ a b c) assoc_l.
Proof.
  red; unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_case.
  rewrite !cat_assoc, !case_inr, !case_inl.
  rewrite <- cat_case, <- case_eta, cat_id_l, <- case_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance AssocLMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_l_ a b c) assoc_r.
Proof.
  red; unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_case.
  rewrite !cat_assoc, !case_inl, !case_inr.
  rewrite <- cat_case, <- case_eta, cat_id_l, <- case_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

(** The coproduct has units. *)

Global Instance UnitLMono_Coproduct {a : obj}
  : SemiIso C (unit_l_ i a) unit_l'.
Proof.
  red; unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite cat_case, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply case_eta.
  all: typeclasses eauto.
Qed.

(* TODO: derive this by symmetry *)
Global Instance UnitRMono_Coproduct {a : obj}
  : SemiIso C (unit_r_ i a) unit_r'.
Proof.
  red; unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite cat_case, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply case_eta.
  all: typeclasses eauto.
Qed.

Global Instance UnitLEpi_Coproduct {a : obj}
  : SemiIso C (unit_l'_ i a) unit_l.
Proof.
  red; unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite case_inr. reflexivity. typeclasses eauto.
Qed.

Global Instance UnitREpi_Coproduct {a : obj}
  : SemiIso C (unit_r'_ i a) unit_r.
Proof.
  red; unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite case_inl. reflexivity. typeclasses eauto.
Qed.

Lemma inr_unit_l {a} : inr_ >>> unit_l ⩯ id_ a.
Proof.
  apply semi_iso; typeclasses eauto.
Qed.

Lemma inl_unit_r {a} : inl_ >>> unit_r ⩯ id_ a.
Proof.
  apply semi_iso; typeclasses eauto.
Qed.

Lemma inr_bimap {a b c d} (f : C a b) (g : C c d)
  : inr_ >>> bimap f g ⩯ g >>> inr_.
Proof.
  unfold bimap, Bimap_Coproduct.
  rewrite case_inr. reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance UnitLNatural_Coproduct : UnitLNatural C bif i.
Proof.
  red; intros.
  apply coprod_split.
  - rewrite <- !cat_assoc.
    transitivity (empty : C i b); [ | symmetry ]; auto using initial_object.
    all: typeclasses eauto.
  - rewrite <- !cat_assoc, inr_bimap, inr_unit_l, cat_assoc,
      inr_unit_l, cat_id_l, cat_id_r.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance UnitL'Natural_Coproduct : UnitL'Natural C bif i.
Proof.
  red; intros.
  unfold unit_l', UnitL'_Coproduct.
  rewrite inr_bimap.
  reflexivity.
Qed.

(** The coproduct satisfies the monoidal coherence laws. *)

Global Instance AssocRUnit_Coproduct : AssocRUnit C bif i.
Proof.
  intros a b.
  unfold assoc_r, AssocR_Coproduct, bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  eapply case_universal.
  all: try typeclasses eauto.
  - rewrite <- cat_assoc, case_inl.
    rewrite cat_case, case_inl.
    unfold unit_r, UnitR_Coproduct.
    rewrite cat_case, cat_id_l.
    apply Proper_case_.
    reflexivity.
    eapply initial_unique; auto.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, case_inr.
    rewrite cat_assoc, case_inr.
    rewrite <- cat_assoc, inr_unit_l, cat_id_l.
    reflexivity.
    all: typeclasses eauto.
Qed.

(* TODO: automate this *)
Global Instance AssocRAssocR_Coproduct : AssocRAssocR C bif.
Proof.
  intros a b c d.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  rewrite !cat_case.
  unfold assoc_r, AssocR_Coproduct.
  apply coprod_split. all: try typeclasses eauto.
  - rewrite case_inl.
    rewrite <- (cat_assoc _ inl_).
    rewrite case_inl.
    rewrite !cat_assoc.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ inl_), !case_inl).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ inl_), !case_inl).
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ inr_), !case_inr).
        rewrite cat_assoc.
        rewrite <- (cat_assoc _ inr_), !case_inr.
        rewrite cat_assoc.
        rewrite case_inr.
        rewrite <- (cat_assoc _ inl_ _ inr_), case_inl.
        rewrite <- cat_assoc, case_inl.
        reflexivity.
        all: typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ inr_), !case_inr).
      rewrite <- (cat_assoc _ inl_), !case_inl.
      rewrite !cat_assoc.
      rewrite <- (cat_assoc _ inr_ (case_ _ _) _), !case_inr.
      rewrite cat_assoc, case_inr.
      rewrite <- (cat_assoc _ inl_ (case_ _ _)), case_inl.
      rewrite <- !cat_assoc, case_inr.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !case_inr.
    rewrite !cat_assoc.
    repeat (rewrite <- (cat_assoc _ inr_ (case_ _ _)), !case_inr).
    rewrite !cat_assoc, case_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance Monoidal_Coproduct : Monoidal C bif i.
Proof.
  constructor.
  all: try typeclasses eauto.
  all: constructor; typeclasses eauto.
Qed.

(* TODO: automate this. This should follow from the above by symmetry. *)
Global Instance AssocLAssocL_Coproduct : AssocLAssocL C bif.
Proof.
  intros a b c d.
  unfold bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  rewrite !cat_case.
  unfold assoc_l, AssocL_Coproduct.
  apply coprod_split. all: try typeclasses eauto.
  - rewrite !case_inl.
    rewrite !cat_assoc.
    repeat (rewrite <- (cat_assoc _ inl_ (case_ _ _)), !case_inl).
    rewrite !cat_assoc, case_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite case_inr.
    rewrite <- (cat_assoc _ inr_).
    rewrite case_inr.
    rewrite !cat_assoc.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ inl_), !case_inl).
      rewrite <- (cat_assoc _ inr_), !case_inr.
      rewrite !cat_assoc.
      rewrite <- (cat_assoc _ inl_ (case_ _ _) _), !case_inl.
      rewrite cat_assoc, case_inl.
      rewrite <- (cat_assoc _ inr_ (case_ _ _)), case_inr.
      rewrite <- !cat_assoc, case_inl.
      reflexivity.
      all: typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ inr_), !case_inr).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ inl_), !case_inl).
        rewrite cat_assoc.
        rewrite <- (cat_assoc _ inl_), !case_inl.
        rewrite cat_assoc.
        rewrite case_inl.
        rewrite <- (cat_assoc _ inr_ _ inl_), case_inr.
        rewrite <- cat_assoc, case_inr.
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ inr_), !case_inr).
        reflexivity.
        all: typeclasses eauto.
Qed.

(** The coproduct satisfies the symmetric monoidal laws. *)

Global Instance SwapUnitL_Coproduct : SwapUnitL C bif i.
Proof.
  intros a.
  unfold swap, Swap_Coproduct, unit_l, UnitL_Coproduct, unit_r, UnitR_Coproduct.
  apply coprod_split.
  - rewrite <- cat_assoc, !case_inl, case_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, !case_inr, case_inl.
    reflexivity.
    all: typeclasses eauto.
Qed.

(* TODO: automate *)
Global Instance SwapAssocR_Coproduct : SwapAssocR C bif.
Proof.
  intros a b c.
  unfold assoc_r, AssocR_Coproduct, swap, Swap_Coproduct, bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ inl_), !case_inl.
    rewrite !cat_assoc.
    rewrite <- (cat_assoc _ inl_), !case_inl.
    all: try typeclasses eauto.
    apply coprod_split.
    + rewrite <- 2 (cat_assoc _ inl_), !case_inl.
      rewrite <- cat_assoc. rewrite case_inl.
      rewrite <- cat_assoc, !case_inr.
      rewrite cat_assoc, case_inr.
      rewrite <- cat_assoc, case_inl.
      reflexivity.
      all: typeclasses eauto.
    + rewrite <- 2 (cat_assoc _ inr_), !case_inr.
      rewrite cat_assoc.
      rewrite <- (cat_assoc _ inr_), case_inr, !case_inl.
      rewrite <- cat_assoc, !case_inl.
      rewrite cat_id_l.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ inr_), !case_inr.
    rewrite cat_id_l.
    rewrite cat_assoc, <- (cat_assoc _ inr_ (case_ _ _) _), !case_inr, case_inl, case_inr.
    rewrite <- cat_assoc.
    rewrite case_inr, cat_assoc, case_inr, <- cat_assoc, case_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance SwapAssocL_Coproduct : SwapAssocL C bif.
Proof.
  intros a b c.
  unfold assoc_l, AssocL_Coproduct, swap, Swap_Coproduct, bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ inl_), !case_inl.
    rewrite cat_id_l.
    rewrite cat_assoc, <- (cat_assoc _ inl_ (case_ _ _) _), !case_inl, case_inr, case_inl.
    rewrite <- cat_assoc.
    rewrite case_inl, cat_assoc, case_inl, <- cat_assoc, case_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ inr_), !case_inr.
    rewrite !cat_assoc.
    rewrite <- (cat_assoc _ inr_), !case_inr.
    all: try typeclasses eauto.
    apply coprod_split.
    + rewrite <- 2 (cat_assoc _ inl_), !case_inl.
      rewrite cat_assoc.
      rewrite <- (cat_assoc _ inl_), case_inl, !case_inr.
      rewrite <- cat_assoc, !case_inr.
      rewrite cat_id_l.
      reflexivity.
      all: typeclasses eauto.
    + rewrite <- 2 (cat_assoc _ inr_), !case_inr.
      rewrite <- cat_assoc. rewrite case_inr.
      rewrite <- cat_assoc, !case_inl.
      rewrite cat_assoc, case_inl.
      rewrite <- cat_assoc, case_inr.
      reflexivity.
      all: typeclasses eauto.
Qed.

Global Instance SymMonoidal_Coproduct : SymMonoidal C bif i.
Proof.
  constructor.
  all: try typeclasses eauto.
Qed.

Lemma swap_bimap {a b c d} (ab : C a b) (cd : C c d) :
  bimap ab cd ⩯ (swap >>> bimap cd ab >>> swap).
Proof.
  unfold bimap, Bimap_Coproduct, swap, Swap_Coproduct.
  apply coprod_split.
  - rewrite case_inl.
    rewrite cat_assoc, <- cat_assoc, case_inl.
    rewrite <- cat_assoc, case_inr.
    rewrite cat_assoc, case_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite case_inr.
    rewrite cat_assoc, <- cat_assoc, case_inr.
    rewrite <- cat_assoc, case_inl.
    rewrite cat_assoc, case_inl.
    reflexivity.
    all: typeclasses eauto.
Qed.

End CoproductFacts.

Hint Rewrite @case_inl : cocartesian.
Hint Rewrite @case_inr : cocartesian.
