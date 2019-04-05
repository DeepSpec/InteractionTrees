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

    Notation iI_voidl := (@iI_voidl i F iI iI_void E).
    Notation void_iIl := (@void_iIl i F iI void_iI E).

    Notation sum_isuml := (@sum_isuml i F isum sum_isum E).
    Notation isum_suml := (@isum_suml i F isum isum_sum E).

    Lemma swap_bimap_l:
      forall {A B C D : i} (ab : sktree A B) (cd: sktree C D),
        @sum_isuml C A >>> @bimap _ sktree _ _ _ _ _ _ cd ab
      ⩯ @bimap _ (ktree E) _ _ _ _ _ _ cd ab >>> @sum_isuml D B.
    Proof with try typeclasses eauto.
      intros A B C D ab cd.
      unfold bimap, Bimap_Coproduct; unfold_sktree.
      rewrite <- cat_assoc, semi_iso, cat_id_l...
      rewrite <- 2 cat_assoc, <- cat_case...
      reflexivity.
    Qed.

    Lemma swap_bimap_r:
      forall {A B C D : i} (ab : sktree A B) (cd : sktree C D),
        ((@bimap _ sktree _ _ _ _ _ _ cd ab):ktree E _ _) >>> @isum_suml D B
      ⩯ (@isum_suml C A >>> @bimap _ (ktree E) _ _ _ _ _ _ cd ab).
    Proof with try typeclasses eauto.
      intros A B C D ab cd.
      unfold bimap, Bimap_Coproduct; unfold_sktree.
      rewrite <- 2 cat_assoc...
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
      rewrite swap_bimap_l.
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
      rewrite swap_bimap_r.
      rewrite <- cat_assoc... 
      reflexivity.
    Qed.

    Lemma sloop_rename_internal {I J A B}
          (ab_: sktree (isum I A) (isum J B)) (ji: sktree J I) :
      sloop (ab_ >>> bimap ji (id_ _))
    ⩯ sloop (bimap ji (id_ _) >>> ab_).
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite 2 cat_assoc...
      rewrite swap_bimap_r.
      rewrite <- 3 cat_assoc...
      rewrite loop_rename_internal.
      rewrite swap_bimap_l.
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    Ltac fold_case:=
      match goal with
        |- context[Case_ktree ?A ?B ?C ?f ?g] => replace (Case_ktree A B C f g) with (case_ f g) by reflexivity
      end.

    Ltac fold_inl:=
      match goal with
        |- context[Inl_ktree ?A ?B] => replace (Inl_ktree A B) with (@inl_ _ _ _ _ A B) by reflexivity
      end.

    Ltac fold_inr:=
      match goal with
        |- context[Inr_ktree ?A ?B] => replace (Inr_ktree A B) with (@inr_ _ _ _ _ A B) by reflexivity
      end.

    Lemma swap_assoc_l: forall {I J B: i},
         isum_suml >>> bimap (id_ (F I)) (@isum_suml J B) >>> assoc_l 
       ⩯ (@assoc_l _ sktree isum _ I J B: ktree _ _ _) >>> isum_suml >>> bimap isum_suml (id_ (F B)).
    Proof with try typeclasses eauto.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_l,AssocL_Coproduct.
      unfold_sktree.
      repeat fold_case.
      repeat fold_inl.
      repeat fold_inr.
      rewrite 2 cat_id_l...
      rewrite cat_assoc, cat_case, case_inl...
      rewrite cat_assoc, case_inr...
      match goal with |- ?f ⩯ _ => set (g:=f) end.

      rewrite <- 2 cat_assoc...
      rewrite <- cat_case...
      rewrite <- cat_assoc...
      rewrite <- cat_case...
      rewrite <- cat_assoc...
      rewrite (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r...
      rewrite cat_assoc...
      rewrite cat_case...
      rewrite cat_assoc, case_inl, <- cat_assoc, (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r...
      rewrite cat_assoc, cat_case, case_inr...
      rewrite cat_assoc, case_inl...
      rewrite <- cat_assoc, (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r...
      subst g.
      reflexivity.
    Qed.

    Lemma swap_assoc_r: forall {I J B: i},
         assoc_r >>> bimap (id_ (F I)) (@sum_isuml J B) >>> sum_isuml
       ⩯ bimap (@sum_isuml I J) (id_ (F B)) >>> sum_isuml >>> (@assoc_r _ sktree isum _ I J B: ktree _ _ _).
    Proof with try typeclasses eauto.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_r,AssocR_Coproduct.
      unfold_sktree.
      repeat fold_case.
      repeat fold_inl.
      repeat fold_inr.
      rewrite 2 cat_id_l...
      rewrite cat_case, cat_assoc, case_inr...
      rewrite (cat_case _ _ inl_ _ _), case_inl...
      rewrite cat_assoc, case_inr...
      match goal with |- ?f ⩯ _ => set (g:=f) end.
      rewrite <- cat_assoc, (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r...
      rewrite cat_case...
      rewrite case_inr...
      rewrite cat_assoc, case_inl...
      rewrite <- cat_assoc, semi_iso, cat_id_l...
      rewrite <- cat_assoc, <- cat_case...
      rewrite <- cat_assoc, <- cat_case...
      subst g.
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    Lemma sloop_sloop {I J A B} (ab__: sktree (isum I (isum J A)) (isum I (isum J B))) :
      sloop (sloop ab__)
    ⩯ sloop (assoc_r >>> ab__ >>> assoc_l).
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite <- compose_loop, <- loop_compose.
      rewrite loop_loop. 
      match goal with |- _ ⩯ ?f => set (g := f) end.
      rewrite 4 cat_assoc...
      rewrite <- (cat_assoc _ isum_suml _ assoc_l).
      rewrite swap_assoc_l.
      repeat rewrite <- cat_assoc...
      rewrite loop_rename_internal.
      subst g.
      rewrite swap_assoc_r.
      repeat rewrite <- cat_assoc...
      rewrite bimap_cat, semi_iso, cat_id_r...
      rewrite bimap_id, cat_id_l... 
      reflexivity.
    Qed.

(*
    Lemma vanishing_sktree {A B: i} (f: sktree (isum iI A) (isum iI B)) :
      sloop f ⩯ unit_l' >>> f >>> unit_l.
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      unfold unit_l', unit_l, UnitL_Coproduct, UnitL'_Coproduct.

      set (f' := bimap void_iIl (id_ _) >>> sum_isuml >>> f >>> isum_suml >>> bimap iI_voidl (id_ _)).
      generalize (vanishing_ktree f'); intros eq.
      subst f'.
      symmetry; rewrite <- cat_id_l...
      Lemma intro_iso: forall {A B} `{SemiIso C f f'} (g: 
                         g ⩯ f >>> f' >>> g. 

      rewrite <- (semi_iso  .
      match goal with
      | |-  _ ⩯ ?g => replace g with (id_ >>> g)
      end.

      set (g' := g >>> @bimap _ (ktree E) _ _ _ _ _ _ iI_void (id_ _)).  >>> bimap iI_void (id_ _)).
      set (g' := g >>> bimap iI_void (id_ _)).
      rewrite <- vanishing_ktree.
      unfold unit_l', unit_l, UnitL_Coproduct, UnitL'_Coproduct.


      generalize (vanishing_ktree (bimap void_iI (id_ _) >>> sum_isuml >>> f >>> isum_suml >>> bimap iI_void (id_ _))).
      match goal with
      | |- loop ?f ⩯ _ => rewrite (vanishing_ktree f)
      end.
      intros a.
      rewrite vanishing1_loop.
      cbv.
      rewrite bind_ret.
      apply eutt_bind; try reflexivity.
      intros [ [] | ]; reflexivity.
    Qed.

*)

  End TracedCategoryLaws.

End Facts.