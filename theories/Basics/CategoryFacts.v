From Coq Require Import
     Setoid Morphisms.

From ITree.Basics Require Import
     CategoryOps CategoryTheory.

Import Carrier.
Import CatNotations.
Local Open Scope cat.

Section IsoFacts.

Context {obj : Type} (C : Hom obj).
Context {Eq2C : Eq2 C} {IdC : Id_ C} {CatC : Cat C}.

Context {CatIdL_C : CatIdL C}.

Global Instance SemiIso_Id {a} : SemiIso C (id_ a) (id_ a) := {}.
Proof. apply cat_id_l; assumption. Qed.

Context {Equivalence_Eq2_C : forall a b, @Equivalence (C a b) eq2}.

Section IsoCat.

Context {CatAssoc_C : CatAssoc C}.
Context {Proper_Cat_C : forall a b c,
            @Proper (C a b -> C b c -> _) (eq2 ==> eq2 ==> eq2) cat}.

Global Instance SemiIso_Cat {a b c}
       (f : C a b) {f' : C b a} {SemiIso_f : SemiIso C f f'}
       (g : C b c) {g' : C c b} {SemiIso_g : SemiIso C g g'}
  : SemiIso C (f >=> g) (g' >=> f') := {}.
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
  rewrite bimap_cat, cat_id_l, cat_id_r.
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
  - rewrite <- cat_assoc; [ | typeclasses eauto ].
    rewrite elim_inl; [ | typeclasses eauto ].
    reflexivity.
  - rewrite <- cat_assoc; [ | typeclasses eauto ].
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
  - rewrite <- cat_assoc, !elim_inl, !cat_assoc, elim_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, !elim_inr, !cat_assoc, elim_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance Bifunctor_Coproduct : Bifunctor C bif.
Proof.
  constructor; typeclasses eauto.
Qed.

(** It is commutative *)

Global Instance SwapInvolutive_Coproduct {a b : obj}
  : SemiIso C (swap_ a b) swap.
Proof.
  red; unfold swap, Swap_Coproduct.
  rewrite cat_elim, elim_inl, elim_inr.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

(** It is associative *)

Global Instance AssocRMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_r_ a b c) assoc_l.
Proof.
  red; unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_elim.
  rewrite !cat_assoc, !elim_inr, !elim_inl.
  rewrite <- cat_elim, <- elim_eta, cat_id_l, <- elim_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Global Instance AssocLMono_Coproduct {a b c : obj}
  : SemiIso C (assoc_l_ a b c) assoc_r.
Proof.
  red; unfold assoc_r, assoc_l, AssocR_Coproduct, AssocL_Coproduct.
  rewrite !cat_elim.
  rewrite !cat_assoc, !elim_inl, !elim_inr.
  rewrite <- cat_elim, <- elim_eta, cat_id_l, <- elim_eta.
  reflexivity.
  all: typeclasses eauto.
Qed.

Context (i : obj).
Context {Initial_i : Initial C i}.
Context {InitialObject_i : InitialObject C i}.

Global Instance UnitLMono_Coproduct {a : obj}
  : SemiIso C (unit_l_ i a) unit_l'.
Proof.
  red; unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite cat_elim, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

(* TODO: derive this by symmetry *)
Global Instance UnitRMono_Coproduct {a : obj}
  : SemiIso C (unit_r_ i a) unit_r'.
Proof.
  red; unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite cat_elim, cat_id_l, (initial_object C i).
  rewrite <- initial_object.
  symmetry; apply elim_eta.
  all: typeclasses eauto.
Qed.

Global Instance UnitLEpi_Coproduct {a : obj}
  : SemiIso C (unit_l'_ i a) unit_l.
Proof.
  red; unfold unit_l, unit_l', UnitL_Coproduct, UnitL'_Coproduct.
  rewrite elim_inr. reflexivity. typeclasses eauto.
Qed.

Global Instance UnitREpi_Coproduct {a : obj}
  : SemiIso C (unit_r'_ i a) unit_r.
Proof.
  red; unfold unit_r, unit_r', UnitR_Coproduct, UnitR'_Coproduct.
  rewrite elim_inl. reflexivity. typeclasses eauto.
Qed.

Lemma coprod_inr_unit_l {a} : coprod_inr >=> unit_l ⩯ id_ a.
Proof.
  apply semi_iso; typeclasses eauto.
Qed.

Lemma coprod_inl_unit_r {a} : coprod_inl >=> unit_r ⩯ id_ a.
Proof.
  apply semi_iso; typeclasses eauto.
Qed.

Global Instance AssocRUnit_Coproduct : AssocRUnit C bif i.
Proof.
  intros a b.
  unfold assoc_r, AssocR_Coproduct, bimap, Bimap_Coproduct.
  rewrite !cat_id_l.
  eapply elim_universal.
  all: try typeclasses eauto.
  - rewrite <- cat_assoc, elim_inl.
    rewrite cat_elim, elim_inl.
    unfold unit_r, UnitR_Coproduct.
    rewrite cat_elim, cat_id_l.
    apply Proper_elim.
    reflexivity.
    eapply initial_unique; auto.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, elim_inr.
    rewrite cat_assoc, elim_inr.
    rewrite <- cat_assoc, coprod_inr_unit_l, cat_id_l.
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
    rewrite <- (cat_assoc _ coprod_inl).
    rewrite elim_inl.
    rewrite !cat_assoc.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ coprod_inl), !elim_inl).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ coprod_inl), !elim_inl).
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ coprod_inr), !elim_inr).
        rewrite cat_assoc.
        rewrite <- (cat_assoc _ coprod_inr), !elim_inr.
        rewrite cat_assoc.
        rewrite elim_inr.
        rewrite <- (cat_assoc _ coprod_inl _ coprod_inr), elim_inl.
        rewrite <- cat_assoc, elim_inl.
        reflexivity.
        all: typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ coprod_inr), !elim_inr).
      rewrite <- (cat_assoc _ coprod_inl), !elim_inl.
      rewrite !cat_assoc.
      rewrite <- (cat_assoc _ coprod_inr (elim _ _) _), !elim_inr.
      rewrite cat_assoc, elim_inr.
      rewrite <- (cat_assoc _ coprod_inl (elim _ _)), elim_inl.
      rewrite <- !cat_assoc, elim_inr.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !elim_inr.
    rewrite !cat_assoc.
    repeat (rewrite <- (cat_assoc _ coprod_inr (elim _ _)), !elim_inr).
    rewrite !cat_assoc, elim_inr.
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
  rewrite !cat_elim.
  unfold assoc_l, AssocL_Coproduct.
  apply coprod_split. all: try typeclasses eauto.
  - rewrite !elim_inl.
    rewrite !cat_assoc.
    repeat (rewrite <- (cat_assoc _ coprod_inl (elim _ _)), !elim_inl).
    rewrite !cat_assoc, elim_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite elim_inr.
    rewrite <- (cat_assoc _ coprod_inr).
    rewrite elim_inr.
    rewrite !cat_assoc.
    apply coprod_split. all: try typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ coprod_inl), !elim_inl).
      rewrite <- (cat_assoc _ coprod_inr), !elim_inr.
      rewrite !cat_assoc.
      rewrite <- (cat_assoc _ coprod_inl (elim _ _) _), !elim_inl.
      rewrite cat_assoc, elim_inl.
      rewrite <- (cat_assoc _ coprod_inr (elim _ _)), elim_inr.
      rewrite <- !cat_assoc, elim_inl.
      reflexivity.
      all: typeclasses eauto.
    + repeat (rewrite <- (cat_assoc _ coprod_inr), !elim_inr).
      apply coprod_split. all: try typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ coprod_inl), !elim_inl).
        rewrite cat_assoc.
        rewrite <- (cat_assoc _ coprod_inl), !elim_inl.
        rewrite cat_assoc.
        rewrite elim_inl.
        rewrite <- (cat_assoc _ coprod_inr _ coprod_inl), elim_inr.
        rewrite <- cat_assoc, elim_inr.
        reflexivity.
        all: typeclasses eauto.
      * repeat (rewrite <- (cat_assoc _ coprod_inr), !elim_inr).
        reflexivity.
        all: typeclasses eauto.
Qed.

Global Instance SwapUnitL_Coproduct : SwapUnitL C bif i.
Proof.
  intros a.
  unfold swap, Swap_Coproduct, unit_l, UnitL_Coproduct, unit_r, UnitR_Coproduct.
  apply coprod_split.
  - rewrite <- cat_assoc, !elim_inl, elim_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite <- cat_assoc, !elim_inr, elim_inl.
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
    rewrite <- 2 (cat_assoc _ coprod_inl), !elim_inl.
    rewrite !cat_assoc.
    rewrite <- (cat_assoc _ coprod_inl), !elim_inl.
    all: try typeclasses eauto.
    apply coprod_split.
    + rewrite <- 2 (cat_assoc _ coprod_inl), !elim_inl.
      rewrite <- cat_assoc. rewrite elim_inl.
      rewrite <- cat_assoc, !elim_inr.
      rewrite cat_assoc, elim_inr.
      rewrite <- cat_assoc, elim_inl.
      reflexivity.
      all: typeclasses eauto.
    + rewrite <- 2 (cat_assoc _ coprod_inr), !elim_inr.
      rewrite cat_assoc.
      rewrite <- (cat_assoc _ coprod_inr), elim_inr, !elim_inl.
      rewrite <- cat_assoc, !elim_inl.
      rewrite cat_id_l.
      reflexivity.
      all: typeclasses eauto.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ coprod_inr), !elim_inr.
    rewrite cat_id_l.
    rewrite cat_assoc, <- (cat_assoc _ coprod_inr (elim _ _) _), !elim_inr, elim_inl, elim_inr.
    rewrite <- cat_assoc.
    rewrite elim_inr, cat_assoc, elim_inr, <- cat_assoc, elim_inr.
    reflexivity.
    all: typeclasses eauto.
Qed.

Global Instance SwapAssocL_Coproduct : SwapAssocL C bif.
Proof.
  intros a b c.
  unfold assoc_l, AssocL_Coproduct, swap, Swap_Coproduct, bimap, Bimap_Coproduct.
  apply coprod_split.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ coprod_inl), !elim_inl.
    rewrite cat_id_l.
    rewrite cat_assoc, <- (cat_assoc _ coprod_inl (elim _ _) _), !elim_inl, elim_inr, elim_inl.
    rewrite <- cat_assoc.
    rewrite elim_inl, cat_assoc, elim_inl, <- cat_assoc, elim_inl.
    reflexivity.
    all: typeclasses eauto.
  - rewrite !cat_assoc.
    rewrite <- 2 (cat_assoc _ coprod_inr), !elim_inr.
    rewrite !cat_assoc.
    rewrite <- (cat_assoc _ coprod_inr), !elim_inr.
    all: try typeclasses eauto.
    apply coprod_split.
    + rewrite <- 2 (cat_assoc _ coprod_inl), !elim_inl.
      rewrite cat_assoc.
      rewrite <- (cat_assoc _ coprod_inl), elim_inl, !elim_inr.
      rewrite <- cat_assoc, !elim_inr.
      rewrite cat_id_l.
      reflexivity.
      all: typeclasses eauto.
    + rewrite <- 2 (cat_assoc _ coprod_inr), !elim_inr.
      rewrite <- cat_assoc. rewrite elim_inr.
      rewrite <- cat_assoc, !elim_inl.
      rewrite cat_assoc, elim_inl.
      rewrite <- cat_assoc, elim_inr.
      reflexivity.
      all: typeclasses eauto.
Qed.

Global Instance SymMonoidal_Coproduct : SymMonoidal C bif i.
Proof.
  constructor.
  all: try typeclasses eauto.
Qed.

Lemma swap_bimap {a b c d} (ab : C a b) (cd : C c d) :
  bimap ab cd ⩯ (swap >=> bimap cd ab >=> swap).
Proof.
  unfold bimap, Bimap_Coproduct, swap, Swap_Coproduct.
  apply coprod_split.
  - rewrite elim_inl.
    rewrite cat_assoc, <- cat_assoc, elim_inl.
    rewrite <- cat_assoc, elim_inr.
    rewrite cat_assoc, elim_inr.
    reflexivity.
    all: typeclasses eauto.
  - rewrite elim_inr.
    rewrite cat_assoc, <- cat_assoc, elim_inr.
    rewrite <- cat_assoc, elim_inl.
    rewrite cat_assoc, elim_inl.
    reflexivity.
    all: typeclasses eauto.
Qed.

End CoproductFacts.

Hint Rewrite @elim_inl : cocartesian.
Hint Rewrite @elim_inr : cocartesian.
