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

  (* Context {iI_init: forall E, Initial (@ktree E) (F iI)}. *)
  Context {iI_void: F iI -> void}.
  Context {void_iI: void -> F iI}.
  Context {iI_voi_iso: Iso Fun iI_void void_iI}.
  
  Context {isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B)}.
  Context {sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)}.
  Context {isum_sum_iso: forall A B, Iso Fun (@isum_sum A B) (@sum_isum A B)}.
  (* Arguments iI_init {E}. *)

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

    (*
    Lemma unit_l_sktree (A : Type) :
      unit_l ⩯ @lift_sktree _ _ E _ A unit_l.
    Proof.
      apply unit_l_ktree.
    Qed.

    Lemma unit_l'_sktree (A : Type) :
      unit_l' ⩯ @lift_sktree _ _ E A (void + A)%type unit_l'.
    Proof.
      reflexivity.
    Qed.
     
    Lemma unit_r_sktree (A : Type) :
      unit_r ⩯ @lift_sktree E _ A unit_r.
    Proof.
      intros [|[]]. reflexivity.
    Qed.

    Lemma unit_r'_sktree (A : Type) :
      unit_r' ⩯ @lift_sktree E A (A + void) unit_r'.
    Proof.
      reflexivity.
    Qed.
     *)

    (*
    Lemma case_l_sktree {A B: i} (ab: sktree A (isum iI B)) :
      ab >>> unit_l ⩯ (fun a: F A => ITree.map unit_l (ab a)).
    Proof.
      rewrite unit_l_sktree.
      reflexivity.
    Qed.

    Lemma case_l_sktree' {A B: Type} (f: @sktree E (void + A) (void + B)) :
      unit_l' >>> f ⩯ fun a => f (inr a).
    Proof.
      rewrite unit_l'_sktree.
      intro. unfold cat, Cat_sktree, ITree.cat, lift_sktree.
      rewrite bind_ret_; reflexivity.
    Qed.

    Lemma case_r_sktree' {A B: Type} (f: @sktree E (A + void) (B + void)) :
      unit_r' >>> f ⩯ fun a => f (inl a).
    Proof.
      rewrite unit_r'_sktree.
      intro. unfold cat, Cat_sktree, ITree.cat, lift_sktree.
      rewrite bind_ret_; reflexivity.
    Qed.

    Lemma case_r_sktree {A B: Type} (ab: @sktree E A (B + void)) :
      ab >>> unit_r ⩯ (fun a: A => ITree.map unit_r (ab a)).
    Proof.
      rewrite unit_r_sktree.
      reflexivity.
    Qed.

    (** *** [bimap] lemmas *)

    Fact bimap_id_lift {A B C} (f : B -> C) :
      bimap (id_ A) (@lift_sktree E _ _ f) ⩯ lift_sktree (bimap (id_ A) f).
    Proof.
      unfold bimap, Bimap_Coproduct.
      rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_sktree.
      reflexivity.
      all: typeclasses eauto.
    Qed.

    Fact bimap_lift_id {A B C} (f : A -> B) :
      bimap (@lift_sktree E _ _ f) (id_ C) ⩯ lift_sktree (bimap f id).
    Proof.
      unfold bimap, Bimap_Coproduct.
      rewrite !cat_id_l, <- lift_case_sum, <- compose_lift_sktree.
      reflexivity.
      all: typeclasses eauto.
    Qed.
     *)

    (* Case_sktree is useless as such because the isum_sum parameter cannot be inferred. *)
    (*  Fix? *)
    (*  *)
    Lemma lift_compose_ktree':
      forall {E A B C} (f: A -> B) (bc: ktree E B C), lift_ktree f >>> bc ⩯ f >>> bc.
    Proof.
      intros; rewrite lift_compose_ktree; reflexivity.
    Qed.

    (* Does this do anything? *)
(*
    Global Instance subrelation_euttktree_euttsktree i F E a b :
      @subrelation (F a -> itree E (F b)) (@eq2 _ (ktree E) _ (F a) (F b)) (@eq2 _ sktree i F E a b).
    Proof.
      repeat intros; reflexivity.
    Qed.
 *)

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

End Facts.