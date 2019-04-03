From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.FunctionFacts
     Basics.Category
     ITree
     KTree
     KTreeFacts
     Eq.UpToTausEquivalence.
From Coq Require Import
     Morphisms.

Require Import SubKTree.
Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.

Global Instance lift_SemiIso {A B: Type} {f: A -> B} {g: B -> A} `{@SemiIso _ Fun _ _ _ _ _ f g} {E}:
  @SemiIso _ (ktree E) Eq2_ktree (Id_ktree) Cat_ktree _ _ (lift_ktree f) (lift_ktree g).
Proof.
  red.
  rewrite compose_lift_ktree, semi_iso, lift_ktree_id; auto.
  reflexivity.
Qed.

Section Facts.

  Context {i: Type}.
  Context {F: i -> Type}.
  Context {iI: i}.
  Context {isum: i -> i -> i}.

  Context {iI_void: F iI -> void}.
  Context {void_iI: void -> F iI}.
  Context {iI_voi_iso: Iso Fun iI_void void_iI}.
  
  Context {isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B)}.
  Context {sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)}.
  Context {isum_sum_iso: forall A B, Iso Fun (@isum_sum A B) (@sum_isum A B)}.

  Context {E: Type -> Type}.

  Notation sktree := (@sktree i F E).

  Definition Case_sktree_ := @Case_sktree i F isum isum_sum.
  Existing Instance Case_sktree_.
  Definition Inl_sktree_ := @Inl_sktree i F isum sum_isum E.
  Existing Instance Inl_sktree_.
  Definition Inr_sktree_ := @Inr_sktree i F isum sum_isum E.
  Existing Instance Inr_sktree_.
  Definition Initial_iI_sktree_ := @Initial_iI_sktree i F iI iI_void.
  Existing Instance Initial_iI_sktree_.

  Ltac unfold_sktree :=
    unfold
      eq2, Eq2_sktree, eutt_sktree,
    cat, Cat_sktree,
    inl_, Inl_sktree_, Inl_sktree,
    inr_, Inr_sktree_, Inr_sktree,
    lift_sktree,
    case_, Case_sktree_, Case_sktree,
    id_, Id_sktree.

  Section CategoryLaws.
    Global Instance CatAssoc_sktree : CatAssoc sktree.
    Proof.
      intros A B C D f g h a.
      unfold cat, Cat_sktree.
      (* Can we make [cat_assoc] work here despite the specialization of the equation? *)
      rewrite CatAssoc_ktree.
      reflexivity.
    Qed.

    (** *** [id_sktree] respect identity laws *)
    Global Instance CatIdL_sktree : CatIdL sktree.
    Proof.
      intros A B f a; unfold cat, Cat_sktree.
      rewrite CatIdL_ktree.
      reflexivity.
    Qed.

    Global Instance CatIdR_sktree : CatIdR sktree.
    Proof.
      intros A B f a; unfold cat, Cat_sktree.
      rewrite CatIdR_ktree.
      reflexivity.
    Qed.

    Global Instance Category_sktree : Category sktree.
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Global Instance InitialObject_sktree : InitialObject sktree iI. 
    Proof.
      intros a f x; exfalso; apply iI_void in x; inversion x.
    Qed.

  End CategoryLaws.

  Section MonoidalCategoryLaws.

    (** *** [Unitors] lemmas *)

    Global Instance CaseInl_sktree: CaseInl sktree isum.
    Proof.
      red; intros; unfold_sktree.
      rewrite <- cat_assoc.
      rewrite (cat_assoc _ inl_).
      rewrite semi_iso.
      rewrite cat_id_r.
      rewrite case_inl.
      reflexivity.
      all: try typeclasses eauto.
    Qed.

    Global Instance CaseInr_sktree: CaseInr sktree isum.
    Proof.
      red; intros; unfold_sktree.
      rewrite <- cat_assoc.
      rewrite (cat_assoc _ inr_).
      rewrite semi_iso.
      rewrite cat_id_r.
      rewrite case_inr.
      reflexivity.
      all: try typeclasses eauto.
    Qed.

    Global Instance CaseUniversal_sktree: CaseUniversal sktree isum.
    Proof.
      red; unfold_sktree; intros.
      rewrite <- case_universal; try typeclasses eauto. 
      - instantiate (1 := (@sum_isuml _ _ isum sum_isum E a b >>> fg)).
        rewrite <- cat_assoc, semi_iso, cat_id_l.
        reflexivity.
        all: try typeclasses eauto.
      - rewrite <- cat_assoc, H.
        reflexivity.
        all: try typeclasses eauto.
      - rewrite <- cat_assoc, H0.
        reflexivity.
        all: try typeclasses eauto.
    Qed.

    Global Instance Coproduct_sktree : Coproduct sktree isum.
    Proof.
      constructor; try typeclasses eauto.
    Qed.

  End MonoidalCategoryLaws.

  Section TracedCategoryLaws.

    Notation sloop := (@sloop i F isum isum_sum sum_isum).

    Notation sum_isuml := (@sum_isuml i F isum sum_isum E).
    Notation isum_suml := (@isum_suml i F isum isum_sum E).

    Lemma bimap_cat:
      forall (I A B : i) (ab : sktree A B),
        @sum_isuml I A >>> bimap (id_ I) ab
      ⩯ bimap (id_ (F I)) ab >>> @sum_isuml I B.
    Proof with try typeclasses eauto.
      intros I A B ab.
      unfold bimap, Bimap_Coproduct.
      unfold_sktree.
      rewrite <- cat_assoc, semi_iso, 3 cat_id_l...
      unfold case_, sum_isuml, inl_, inr_, Inl_ktree, Inr_ktree.
      rewrite compose_lift_ktree.
      unfold Case_ktree, case_sum.
      match goal with
      | |- _ ⩯ ?f >>> lift_ktree ?h => rewrite (compose_ktree_lift f h)
      end.
      unfold lift_ktree.
      intros []; simpl.
      - rewrite map_ret.
        reflexivity.
      - unfold cat, Cat_ktree, ITree.cat.
        rewrite map_bind.
        apply eutt_bind; [intros ?| reflexivity].
        rewrite bind_ret, map_ret.
        reflexivity.
    Qed.

    Lemma cat_bimap:
      forall (I A B : i) (ab : sktree A B),
        ((@bimap _ sktree _ _ _ _ _ _ (@id_ Type (ktree E) _ (F I)) ab):ktree E _ _) >>> @isum_suml I B
       ⩯ (@isum_suml I A >>> bimap (id_ (F I)) ab).
    Proof with try typeclasses eauto.
      intros I A B ab.
      unfold bimap, Bimap_Coproduct.
      unfold_sktree.
      rewrite 2 cat_id_l...
      rewrite <- cat_assoc...
      rewrite <- cat_case...
      rewrite 2 cat_assoc, semi_iso, cat_id_r...
      reflexivity. 
    Qed.
      
    Lemma compose_sloop {I A B C}
          (bc_: sktree (isum I B) (isum I C)) (ab: sktree A B) :
      sloop (bimap (id_ _) ab >>> bc_)
    ⩯ ab >>> sloop bc_.
    Proof with try typeclasses eauto.
      unfold_sktree.
      unfold sloop.
      rewrite <- compose_loop.
      rewrite <- cat_assoc...
      rewrite bimap_cat.
      rewrite <- 2 cat_assoc...
      reflexivity.
    Qed.

    Lemma sloop_compose {I A B B'}
          (ab_: sktree (isum I A) (isum I B)) (bc: sktree B B') :
      sloop (ab_ >>> bimap (id_ _) bc)
           ⩯ sloop ab_ >>> bc.
    Proof with try typeclasses eauto.
      unfold_sktree.
      unfold sloop.
      rewrite <- loop_compose.
      rewrite <- cat_assoc...
      rewrite cat_assoc...
      rewrite cat_bimap.
      rewrite <- cat_assoc... 
      reflexivity.
    Qed.

  End TracedCategoryLaws.

End Facts.