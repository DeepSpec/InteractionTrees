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

  (* We consider a subdomain of Type given by a Type [i] and its injection into Type [F] *)
  Context {i: Type}.
  Context {iEmbed: Embedding i}.
  (* We assume that we have an initial element and a bifunctor over i *)
  Context {iI: i}.
  Context {isum: i -> i -> i}.
  Context {FInit: Embedded_initial iI}.
  Context {iI_iso: Iso Fun iI_void void_iI}.
  Context {Fsum: Embedded_sum isum}.
  Context {sum_Iso: forall A B, Iso Fun (@isum_sum _ _ _ _ A B) sum_isum}.
 
  (* Context {i: Type}. *)
  (* Context {F: i -> Type}. *)
  (* Context {iI: i}. *)
  (* Context {isum: i -> i -> i}. *)

  (* Context {iI_void: F iI -> void}. *)
  (* Context {void_iI: void -> F iI}. *)
  (* Context {iI_voi_iso: Iso Fun iI_void void_iI}. *)
  
  (* Context {isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B)}. *)
  (* Context {sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)}. *)
  (* Context {isum_sum_iso: forall A B, Iso Fun (@isum_sum A B) (@sum_isum A B)}. *)

  Context {E: Type -> Type}.

  Notation sktree := (@sktree i iEmbed E).

  Definition Case_sktree_ := @Case_sktree i _ _ _ E.
  Existing Instance Case_sktree_.
  Definition Inl_sktree_ := @Inl_sktree i _ _ _ E.
  Existing Instance Inl_sktree_.
  Definition Inr_sktree_ := @Inr_sktree i _ _ _ E.
  Existing Instance Inr_sktree_.
  (* Definition Initial_iI_sktree_ := @Initial_iI_sktree i *)
  (* Existing Instance Initial_iI_sktree_. *)

  (* Notation sloop := (@sloop i F isum isum_sum sum_isum). *)

  (* Notation iI_voidl := (@iI_voidl i F iI iI_void E). *)
  (* Notation void_iIl := (@void_iIl i F iI void_iI E). *)

  (* Notation sum_isuml := (@sum_isuml i F isum sum_isum E). *)
  (* Notation isum_suml := (@isum_suml i F isum isum_sum E). *)

  Ltac unfold_sktree :=
    unfold
      eq2, Eq2_sktree, eutt_sktree,
    cat, Cat_sktree,
    inl_, Inl_sktree_, Inl_sktree,
    inr_, Inr_sktree_, Inr_sktree,
    lift_sktree,
    case_, Case_sktree_, Case_sktree,
    empty(* , Initial_iI_sktree_ *), Initial_iI_sktree,
    id_, Id_sktree.

  Ltac fold_eq:=
    match goal with
      |- context[Eq2_ktree ?A ?B ?f ?g] => replace (Eq2_ktree A B f g) with (eq2 f g) by reflexivity
    end.

  Ltac fold_cat:=
    match goal with
      |- context[Cat_ktree ?A ?B ?C ?f ?g] => replace (Cat_ktree A B C f g) with (cat f g) by reflexivity
    end.

  Ltac fold_id:=
    match goal with
      |- context[Id_ktree ?A] => replace (Id_ktree A) with (id_ A) by reflexivity
    end.

  Ltac fold_case:=
    match goal with
      |- context[Case_ktree ?A ?B ?C ?f ?g] => replace (Case_ktree A B C f g) with (case_ f g) by reflexivity
    end.

  Ltac fold_inl:=
    match goal with
      |- context[Inl_ktree ?A ?B] => replace (Inl_ktree A B) with (@inl_ Type (ktree E) _ _ A B) by reflexivity
    end.

  Ltac fold_inr:=
    match goal with
      |- context[Inr_ktree ?A ?B] => replace (Inr_ktree A B) with (@inr_ Type (ktree E) _ _ A B) by reflexivity
    end.

  Ltac fold_initial:=
    match goal with
      |- context[Initial_void_ktree ?A] => replace (Initial_void_ktree A) with (@empty Type (ktree E) _ _ A) by reflexivity
    end.

  Ltac fold_ktree := repeat (fold_eq || fold_cat || fold_id || fold_case || fold_inl || fold_inr || fold_initial).

  Section UnfoldingLemmas.

    Lemma unfold_bimap: forall {A B C D} (f: ktree E (F A) (F C)) (g: ktree E (F B) (F D)),
      @bimap i sktree isum _ _ _ _ _ f g
    ⩯ isum_suml >>> @bimap Type (ktree E) sum _ _ _ _ _ f g >>> sum_isuml.
    Proof with try typeclasses eauto.
      intros A B C D ab cd.
      unfold bimap, Bimap_Coproduct; unfold_sktree; fold_ktree.
      rewrite <- 2 cat_assoc, <- cat_case...
      rewrite cat_assoc...
      reflexivity.
    Qed.

    Lemma unfold_bimap_l:
      forall {A B C D : i} (ab : sktree A B) (cd: sktree C D),
        sum_isuml >>> @bimap _ sktree _ _ _ _ _ _ cd ab
      ⩯ @bimap _ (ktree E) _ _ _ _ _ _ cd ab >>> sum_isuml.
    Proof with try typeclasses eauto.
      intros A B C D ab cd.
      rewrite unfold_bimap.
      rewrite <- 2 cat_assoc, semi_iso, cat_id_l...
      reflexivity.
    Qed.

    Lemma unfold_bimap_r:
      forall {A B C D : i} (ab : sktree A B) (cd : sktree C D),
        ((@bimap _ sktree _ _ _ _ _ _ cd ab):ktree E _ _) >>> isum_suml
      ⩯ (isum_suml >>> @bimap _ (ktree E) _ _ _ _ _ _ cd ab).
    Proof with try typeclasses eauto.
      intros A B C D ab cd.
      rewrite unfold_bimap.
      rewrite cat_assoc, semi_iso, cat_id_r...
      reflexivity.
    Qed.

    Lemma unfold_unit_l {A: i}:
      @unit_l _ sktree _ _ _ A ⩯
      isum_suml >>> bimap iI_voidl (id_ _) >>> unit_l.
    Proof with try typeclasses eauto.
      unfold unit_l, UnitL_Coproduct, bimap, Bimap_Coproduct.
      unfold_sktree; fold_ktree.
      rewrite cat_id_l...
      rewrite cat_assoc...
      rewrite cat_case, cat_assoc, case_inl, case_inr...
      reflexivity.
    Qed.

    Lemma unfold_unit_l' {A: i}:
      @unit_l' _ sktree _ _ _ A ⩯
      unit_l' >>> bimap void_iIl (id_ _) >>> sum_isuml. 
    Proof with try typeclasses eauto.
      unfold unit_l', UnitL'_Coproduct, bimap, Bimap_Coproduct.
      unfold_sktree.
      fold_ktree.
      rewrite cat_id_l...
      rewrite case_inr...
      reflexivity.
    Qed.

    Lemma unfold_assoc_l {A B C}:
      @assoc_l i sktree isum _ A B C ⩯
       isum_suml >>> bimap (id_ (F A)) isum_suml >>> assoc_l >>> bimap sum_isuml (id_ (F C)) >>> sum_isuml.
    Proof with try typeclasses eauto.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_l,AssocL_Coproduct.
      unfold_sktree.
      fold_ktree.
      rewrite 2 cat_id_l...
      match goal with |- ?f ⩯ _ => set (g:=f) end.
      repeat rewrite cat_assoc...
      rewrite cat_case...
      rewrite <- cat_assoc, case_inl...
      rewrite 2 cat_assoc...
      rewrite <- (cat_assoc _ _ (case_ _ _) _), case_inl...
      rewrite <- (cat_assoc _ inr_ _ _), case_inr...
      rewrite cat_case...
      repeat rewrite cat_assoc...
      rewrite <- (cat_assoc _ _ (case_ _ _) _), case_inl...
      repeat rewrite <- cat_assoc...
      rewrite case_inr...
      subst g.
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    Lemma unfold_assoc_r {A B C}:
      @assoc_r i sktree isum _ A B C ⩯
       isum_suml >>> bimap isum_suml (id_ (F C)) >>> assoc_r >>> bimap (id_ (F A)) sum_isuml >>> sum_isuml.
    Proof with try typeclasses eauto.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_r,AssocR_Coproduct.
      unfold_sktree.
      fold_ktree.
      rewrite 2 cat_id_l...
      match goal with |- ?f ⩯ _ => set (g:=f) end.
      repeat rewrite cat_assoc...
      rewrite cat_case...
      rewrite <- cat_assoc, (cat_assoc _ _ inl_ _), case_inl...
      rewrite <- (cat_assoc _ inr_ _ _), case_inr...
      rewrite (cat_assoc _ inr_ _ _), <- (cat_assoc _ inr_ (case_ _ _) _), case_inr...
      rewrite cat_case...
      rewrite cat_assoc, cat_case, case_inl...
      rewrite (cat_assoc _ _ inr_ _), case_inr...
      subst g.
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    (* We might be able to simplify those two *)
    Lemma unfold_swap_assoc_l: forall {I J B: i},
         isum_suml >>> bimap (id_ (F I)) isum_suml >>> assoc_l 
       ⩯ (@assoc_l _ sktree isum _ I J B: ktree _ _ _) >>> isum_suml >>> bimap isum_suml (id_ (F B)).
    Proof with try typeclasses eauto.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_l,AssocL_Coproduct.
      unfold_sktree.
      fold_ktree.
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

    Lemma unfold_swap_assoc_r: forall {I J B: i},
         assoc_r >>> bimap (id_ (F I)) sum_isuml >>> sum_isuml
       ⩯ bimap sum_isuml (id_ (F B)) >>> sum_isuml >>> (@assoc_r _ sktree isum _ I J B: ktree _ _ _).
    Proof with try typeclasses eauto.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_r,AssocR_Coproduct.
      unfold_sktree.
      fold_ktree.
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

    Lemma unfold_swap {A B: i}:
      swap ⩯ sum_isuml >>> (@swap _ sktree _ _ A B:ktree _ _ _) >>> isum_suml.
    Proof with try typeclasses eauto.
      unfold swap, Swap_Coproduct.
      unfold_sktree; unfold sloop, case_; fold_ktree.
      rewrite <- cat_assoc, semi_iso, cat_id_l...
      rewrite <- cat_case, cat_assoc, semi_iso, cat_id_r...
      reflexivity.
    Qed.

  End UnfoldingLemmas.

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
      - instantiate (1 := sum_isuml >>> fg).
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

    Lemma compose_sloop {I A B C}
          (bc_: sktree (isum I B) (isum I C)) (ab: sktree A B) :
      sloop (bimap (id_ _) ab >>> bc_)
    ⩯ ab >>> sloop bc_.
    Proof with try typeclasses eauto.
      unfold_sktree.
      unfold sloop.
      rewrite <- compose_loop.
      rewrite <- cat_assoc...
      rewrite unfold_bimap.
      rewrite <- 2 (cat_assoc _ sum_isuml _ _), semi_iso, cat_id_l...
      repeat rewrite cat_assoc...
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
      rewrite unfold_bimap.
      rewrite (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r... 
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    Lemma sloop_rename_internal {I J A B}
          (ab_: sktree (isum I A) (isum J B)) (ji: sktree J I) :
      sloop (ab_ >>> bimap ji (id_ _))
    ⩯ sloop (bimap ji (id_ _) >>> ab_).
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite 2 cat_assoc...
      rewrite unfold_bimap.
      rewrite (cat_assoc _ _ sum_isuml _), semi_iso, cat_id_r...
      rewrite <- 3 cat_assoc...
      rewrite loop_rename_internal.
      rewrite unfold_bimap_l.
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    Lemma vanishing_sktree {A B: i} (f: sktree (isum iI A) (isum iI B)) :
      sloop f ⩯ unit_l' >>> f >>> unit_l.
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite unfold_unit_l, unfold_unit_l'.
      rewrite <- cat_assoc...
      rewrite 3 (cat_assoc _ unit_l' _ _)...
      rewrite <- vanishing_ktree.
      repeat rewrite (cat_assoc _ (bimap _ _) _ _).
      rewrite <- loop_rename_internal.
      repeat rewrite cat_assoc...
      rewrite bimap_cat, semi_iso, cat_id_l, bimap_id, cat_id_r...
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
      rewrite unfold_swap_assoc_l.
      repeat rewrite <- cat_assoc...
      rewrite loop_rename_internal.
      subst g.
      rewrite unfold_swap_assoc_r.
      repeat rewrite <- cat_assoc...
      rewrite bimap_cat, semi_iso, cat_id_r...
      rewrite bimap_id, cat_id_l... 
      reflexivity.
    Qed.

    Lemma bimap_sktree_loop {I A B C D}
          (ab : sktree (isum I A) (isum I B)) (cd : sktree C D) :
      bimap (sloop ab) cd
    ⩯ sloop (assoc_l >>> bimap ab cd >>> assoc_r).
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      repeat rewrite unfold_bimap.
      rewrite bimap_ktree_loop.
      rewrite <- compose_loop, <- loop_compose.
      rewrite unfold_assoc_r, unfold_assoc_l.
      repeat rewrite <- cat_assoc...
      rewrite semi_iso, cat_id_l...
      rewrite (cat_assoc _ _ (sum_isuml) _), semi_iso, cat_id_r...
      rewrite (cat_assoc _ _ (sum_isuml) _), semi_iso, cat_id_r...
      rewrite (cat_assoc _ _ (sum_isuml) _), semi_iso, cat_id_r...
      rewrite (cat_assoc _ _ (bimap _ _) (bimap _ _) ), bimap_cat...
      rewrite (cat_assoc _ _ (bimap _ _) (bimap _ _) ), bimap_cat...
      rewrite cat_id_l, cat_id_r...
      repeat rewrite cat_assoc...
      reflexivity.
    Qed.

    (* The automation in this proof is slightly brutal... *)
    Lemma loop_bimap_sktree {I A B C D}
          (ab : sktree A B) (cd : sktree (isum I C) (isum I D)) :
      bimap ab (sloop cd)
    ⩯ sloop (assoc_l >>> bimap swap (id_ _)
                     >>> assoc_r
                     >>> bimap ab cd
                     >>> assoc_l >>> bimap swap (id_ _) >>> assoc_r).
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite unfold_bimap.
      rewrite loop_bimap_ktree.
      rewrite <- compose_loop, <- loop_compose.
      repeat (rewrite unfold_assoc_l || rewrite unfold_assoc_r || rewrite unfold_swap || rewrite unfold_bimap).
      repeat rewrite cat_assoc...
      repeat (rewrite <- (cat_assoc _ sum_isuml isum_suml _), semi_iso, cat_id_l)...
      repeat (rewrite <- (cat_assoc _ (bimap _ _) (bimap _ _) _), bimap_cat)...
      repeat (rewrite cat_id_l || rewrite cat_id_r)...
      repeat rewrite cat_assoc...
      rewrite semi_iso, cat_id_r...
      reflexivity.
    Qed.

    Lemma yanking_sktree {A: i}:
      @sloop _ _ _ _ _ _ _ _ swap ⩯ id_ A.
    Proof with try typeclasses eauto.
      unfold_sktree; unfold sloop.
      rewrite <- yanking_ktree.
      rewrite unfold_swap.
      reflexivity.
    Qed.

  End TracedCategoryLaws.

End Facts.
