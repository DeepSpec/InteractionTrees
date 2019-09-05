From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.FunctionFacts
     Basics.Category
     Basics.MonadTheory
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     ITree
     Core.ITreeMonad
     KTree
     KTreeFacts
     SubKTree
     Eq.Eq.

From Coq Require Import
     Program
     Morphisms
     Setoid.


Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.

Global Instance lift_SemiIso {A B: Type} {f: A -> B} {g: B -> A} `{@SemiIso _ Fun _ _ _ _ _ f g} {E}:
  SemiIso (ktree E) (lift_ktree f) (lift_ktree g).
Proof.
  red.  rewrite compose_pure, semi_iso, pure_id; auto; reflexivity.
Qed.

Section Facts.

  Context {i: Type}.
  Context {iEmbed: Embedding i}.
  Context {iI: i}.
  Context {isum: i -> i -> i}.
  Context {FInit: Embedded_initial iI}.
  Context {iI_iso: Iso Fun iI_void void_iI}.
  Context {Fsum: Embedded_sum isum}.
  Context {sum_Iso: forall A B, Iso Fun (@isum_sum _ _ _ _ A B) sum_isum}.

  Context {E: Type -> Type}.

  Notation sktree := (@sktree i iEmbed E).

  Global Instance Eq2_sktree_equivalence {a b} : Equivalence (@Eq2_sktree i iEmbed E a b).
  Proof.
    unfold Eq2_sktree, eutt_sktree.
    constructor; repeat intro.
    - reflexivity.
    - symmetry. auto.
    - etransitivity; eauto.
  Qed.
    

  Global Instance Proper_Eq2sktree {a b:i} : Proper ((@Eq2_sktree i iEmbed E a b) ==>
                                                     (@Eq2_sktree i iEmbed E a b) ==>
                                                     iff) (@eq2 _ (ktree E) _ _ _).
  repeat red.
  intros x y H x0 y0 H0.
  split; intros.
  - unfold Eq2_sktree, eutt_sktree in *. rewrite <- H. rewrite <- H0. assumption.
  - unfold Eq2_sktree, eutt_sktree in *. rewrite H. rewrite H0. assumption.
  Qed.


  Global Instance Proper_sktreeEq2 {a b:i} : Proper ((@eq2 _ (ktree E) _ (F a) (F b)) ==>
                                                     (@eq2 _ (ktree E) _ (F a) (F b)) ==>
                                                     iff) (@eq2 _ (sktree) _ _ _).
  Proof.
    repeat red.
    intros.
    unfold eq2, Eq2_sktree, eutt_sktree.
    split; intros.
    - rewrite <- H. rewrite <- H0. assumption.
    - rewrite H. rewrite H0. assumption.
  Qed.
  
  (** A bit of Ltac support to unfold [sktree] instances of typeclasses **)
  Ltac unfold_sktree :=
      unfold lift_sktree;
      let ccc := fresh "ccc" in
      let eccc := fresh "eq" ccc in
      try (remember (@cat _ _ Cat_sktree) as ccc eqn:eccc;
        unfold cat, Cat_sktree in eccc; subst ccc);
      try (remember (@id_ _ _ Id_sktree) as ccc eqn:eccc;
        unfold id_, Id_sktree in eccc; subst ccc);
      try (remember (@inl_ _ _ _ Inl_sktree) as ccc eqn:eccc;
        unfold inl_, Inl_sktree in eccc; subst ccc);
      try (remember (@inr_ _ _ _ Inr_sktree) as ccc eqn:eccc;
        unfold inr_, Inr_sktree in eccc; subst ccc);
      try (remember (@case_ _ _ _ Case_sktree) as ccc eqn:eccc;
        unfold case_, Case_sktree in eccc; subst ccc);
      try (remember (@empty _ _ _ Initial_iI_sktree) as ccc eqn:eccc;
        unfold empty, Initial_iI_sktree in eccc; subst ccc).

  Ltac fold_eq:=
    match goal with
      |- context[Eq2_Kleisli ?m ?M ?A ?B ?f ?g] => replace (Eq2_Kleisli m A B f g) with (eq2 f g) by reflexivity
    end.

  Ltac fold_cat:=
    match goal with
      |- context[Cat_Kleisli ?m ?M ?A ?B ?C ?f ?g] => replace (Cat_Kleisli m A B C f g) with (cat f g) by reflexivity
    end.

  Ltac fold_id:=
    match goal with
      |- context[Id_Kleisli ?m ?A] => replace (Id_Kleisli m A) with (@id_ _ (ktree E) _ A) by reflexivity
    end.

  Ltac fold_case:=
    match goal with
      |- context[CoprodCase_Kleisli ?m ?A ?B ?C ?f ?g] => replace (CoprodCase_Kleisli m A B C f g) with (case_ f g) by reflexivity
    end.

  Ltac fold_inl:=
    match goal with
      |- context[CoprodInl_Kleisli ?m _ ?A ?B] => replace (CoprodInl_Kleisli m A B) with (@inl_ Type (ktree E) _ _ A B) by reflexivity
    end.

  Ltac fold_inr:=
    match goal with
      |- context[CoprodInr_Kleisli ?m _ ?A ?B] => replace (CoprodInr_Kleisli m A B) with (@inr_ Type (ktree E) _ _ A B) by reflexivity
    end.

  Ltac fold_initial:=
    match goal with
      |- context[Initial_Kleisli ?A] => replace (Initial_Kleisli A) with (@empty Type (ktree E) _ _ A) by reflexivity
    end.

  Ltac fold_ktree := repeat (fold_eq || fold_cat || fold_id || fold_case || fold_inl || fold_inr || fold_initial).

  (** Unfolding lemmas for the instances that are derived from the Coproduct **)
  Section UnfoldingLemmas.

    Lemma unfold_bimap: forall {A B C D} (f: ktree E (F A) (F C)) (g: ktree E (F B) (F D)),
      (@eq2 _ (ktree E) _ _ _)
      (@bimap i sktree isum _ _ _ _ _ f g)
      (isum_suml >>> @bimap Type (ktree E) sum _ _ _ _ _ f g >>> sum_isuml).
    Proof.
      intros A B C D ab cd.
      unfold bimap, Bimap_Coproduct.
      rewrite cat_assoc, cat_case, 2 cat_assoc.
      reflexivity.
    Qed.

    Lemma unfold_bimap_l:
      forall {A B C D : i} (ab : sktree A B) (cd: sktree C D),
       (sum_isuml >>> @bimap _ sktree _ _ _ _ _ _ cd ab)
         ⩯
         (@bimap _ (ktree E) _ _ _ _ _ _ cd ab >>> sum_isuml).
    Proof.
      intros A B C D ab cd.
      rewrite unfold_bimap.
      rewrite <- 2 cat_assoc, (semi_iso _ _), cat_id_l.
      reflexivity.
    Qed.

    Lemma unfold_bimap_r:
      forall {A B C D : i} (ab : sktree A B) (cd : sktree C D),
        ((@bimap _ sktree _ _ _ _ _ _ cd ab):ktree E _ _) >>> isum_suml
      ⩯ (isum_suml >>> @bimap _ (ktree E) _ _ _ _ _ _ cd ab).
    Proof.
      intros A B C D ab cd.
      rewrite unfold_bimap.
      rewrite cat_assoc, (semi_iso _ _), cat_id_r.
      reflexivity.
    Qed.

    Lemma unfold_unit_l {A: i}:
      (@eq2 _ (ktree E) _ _ _)
      (@unit_l _ sktree _ _ _ A)
      (isum_suml >>> bimap iI_voidl (id_ _) >>> unit_l).
    Proof.
      unfold unit_l, UnitL_Coproduct, bimap, Bimap_Coproduct.
      rewrite cat_id_l.
      rewrite cat_assoc, cat_case, cat_assoc, case_inl, case_inr.
      reflexivity.
    Qed.

    Lemma unfold_unit_l' {A: i}:
      (@eq2 _ (ktree E) _ _ _)
      (@unit_l' _ sktree _ _ _ A)
      (unit_l' >>> bimap void_iIl (id_ _) >>> sum_isuml).
    Proof.
      unfold unit_l', UnitL'_Coproduct, bimap, Bimap_Coproduct.
      rewrite cat_id_l, case_inr.
      reflexivity.
    Qed.

    Lemma unfold_assoc_l {A B C}:
      (@eq2 _ (ktree E) _ _ _)
      (@assoc_l i sktree isum _ A B C)
      (isum_suml >>> bimap (id_ (F A)) isum_suml >>> assoc_l >>> bimap sum_isuml (id_ (F C)) >>> sum_isuml).
    Proof.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_l, AssocL_Coproduct.
      rewrite 2 cat_id_l.
      rewrite (cat_assoc isum_suml).
      rewrite cat_case, case_inl, (cat_assoc _ inr_), case_inr.
      rewrite (cat_assoc isum_suml), cat_case, !cat_assoc, case_inl.
      rewrite (cat_case _ inr_), case_inr.
      rewrite (cat_assoc inr_), case_inl.
      rewrite cat_case.
      rewrite (cat_assoc isum_suml), cat_case.
      rewrite <- 2 cat_assoc. rewrite 2 (cat_assoc _ _ sum_isuml).
      reflexivity.
    Qed.

    Lemma unfold_assoc_r {A B C}:
      (@eq2 _ (ktree E) _ _ _)
      (@assoc_r i sktree isum _ A B C)
      (isum_suml >>> bimap isum_suml (id_ (F C)) >>> assoc_r >>> bimap (id_ (F A)) sum_isuml >>> sum_isuml).
    Proof.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_r,AssocR_Coproduct.
      unfold_sktree.
      rewrite 2 cat_id_l.
      match goal with |- ?f ⩯ _ => set (g:=f) end.
      repeat rewrite cat_assoc.
      rewrite cat_case.
      rewrite <- cat_assoc, (cat_assoc _ inl_ _), case_inl.
      rewrite <- (cat_assoc inr_ _ _), case_inr.
      rewrite (cat_assoc inr_ _ _), <- (cat_assoc inr_ (case_ _ _) _), case_inr.
      rewrite cat_case.
      rewrite cat_assoc, cat_case, case_inl.
      rewrite (cat_assoc _ inr_ _), case_inr.
      subst g.
      repeat rewrite cat_assoc.
      reflexivity.
    Qed.

    (* We might be able to simplify those two *)
    Lemma unfold_swap_assoc_l: forall {I J B: i},
      (@eq2 _ (ktree E) _ _ _)        
      (isum_suml >>> bimap (id_ (F I)) isum_suml >>> assoc_l) 
      ((@assoc_l _ sktree isum _ I J B: ktree _ _ _) >>> isum_suml >>> bimap isum_suml (id_ (F B))).
    Proof.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_l,AssocL_Coproduct.
      unfold_sktree.
      rewrite 2 cat_id_l.
      rewrite cat_assoc, cat_case, case_inl.
      rewrite cat_assoc, case_inr.
      match goal with |- ?f ⩯ _ => set (g:=f) end.

      rewrite <- 2 cat_assoc.
      rewrite <- cat_case.
      rewrite <- cat_assoc.
      rewrite <- cat_case.
      rewrite <- cat_assoc.
      rewrite (cat_assoc _ sum_isuml _), (semi_iso _ _), cat_id_r.
      rewrite cat_assoc.
      rewrite cat_case.
      rewrite cat_assoc, case_inl, <- cat_assoc, (cat_assoc _ sum_isuml _), (semi_iso _ _), cat_id_r.
      rewrite cat_assoc, cat_case, case_inr.
      rewrite cat_assoc, case_inl.
      rewrite <- cat_assoc, (cat_assoc _ sum_isuml _), (semi_iso _ _), cat_id_r.
      subst g.
      reflexivity.
    Qed.

    Lemma unfold_swap_assoc_r: forall {I J B: i},
      (@eq2 _ (ktree E) _ _ _)        
      (assoc_r >>> bimap (id_ (F I)) sum_isuml >>> sum_isuml)
      (bimap sum_isuml (id_ (F B)) >>> sum_isuml >>> (@assoc_r _ sktree isum _ I J B: ktree _ _ _)).
    Proof.
      intros.
      unfold bimap, Bimap_Coproduct.
      unfold assoc_r,AssocR_Coproduct.
      unfold_sktree.
      fold_ktree.
      rewrite 2 cat_id_l.
      rewrite cat_case, cat_assoc, case_inr.
      rewrite (cat_case inl_), case_inl.
      rewrite cat_assoc, case_inr...
      match goal with |- ?f ⩯ _ => set (g:=f) end.
      rewrite <- cat_assoc, (cat_assoc _ sum_isuml _), (semi_iso _ _), cat_id_r.
      rewrite cat_case.
      rewrite case_inr.
      rewrite cat_assoc, case_inl.
      rewrite <- cat_assoc, (semi_iso _ _), cat_id_l.
      rewrite <- cat_assoc, <- cat_case.
      rewrite <- cat_assoc, <- cat_case.
      subst g.
      repeat rewrite cat_assoc.
      reflexivity.
    Qed.

    Lemma unfold_swap {A B: i}:
      swap ⩯ sum_isuml >>> (@swap _ sktree _ _ A B:ktree _ _ _) >>> isum_suml.
    Proof.
      unfold swap, Swap_Coproduct.
      unfold_sktree.
      rewrite <- cat_assoc, (semi_iso _ _), cat_id_l.
      rewrite <- cat_case, cat_assoc, (semi_iso _ _), cat_id_r.
      reflexivity.
    Qed.

    Lemma sym_sktree_unfold {A B}:
      (@eq2 _ (sktree) _ _ _)
      (@lift_sktree _ _ E _ _ (@swap _ iFun _ _ A B))
      swap.
    Proof.
      generalize (@pure_swap (itree E) _ _ _ (F A) (F B)).
      unfold swap, Swap_Coproduct; intros EQ.
      unfold_sktree.
      rewrite <- cat_case, <- EQ.
      unfold isum_inl, isum_inr, case_isum.
      rewrite <- case_pure, cat_case.
      unfold sum_isuml, isum_suml.
      rewrite 2 compose_pure, case_pure, compose_pure.
      reflexivity.
    Qed.

    (* To redo, iFun is poorly handled *)
    Lemma unfold_assoc_l_iFun {A B C}:
      @assoc_l _ iFun _ _ A B C ⩯
      isum_sum >>> bimap (id_ (F A)) isum_sum >>> @assoc_l _ Fun _ _ _ _ _ >>> bimap sum_isum (id_ (F C)) >>> sum_isum.
    Proof.
      unfold assoc_l, AssocL_Coproduct.
      unfold case_ at 1 2, case_isum. 
      unfold inl_, isum_inl, inr_, isum_inr, sum_isum.
      unfold cat at 2, Cat_iFun.
      rewrite cat_assoc.
      unfold cat, Cat_Fun,  bimap, Bimap_Coproduct, case_, case_sum.
      intros ?.
      destruct (isum_sum a).
      simpl.
      unfold cat.
      cbv. reflexivity.
      cbv. 
      destruct Fsum.
      destruct (isum_sum B C f).
      reflexivity.
      reflexivity.
    Qed.

    (* To redo, iFun is poorly handled *)
    Lemma unfold_assoc_r_iFun {A B C}:
      @assoc_r _ iFun _ _ A B C ⩯
      isum_sum >>> @bimap _ Fun sum _ _ _ _ _ isum_sum (id_ (F C)) >>> @assoc_r _ Fun _ _ _ _ _ >>> bimap (id_ (F A)) sum_isum >>> sum_isum.
    Proof.
      unfold assoc_r, AssocR_Coproduct.
      unfold case_ at 1 2, case_isum. 
      unfold inl_, isum_inr, inl_, isum_inl, isum_sum.
      destruct Fsum; simpl.
      unfold cat, Cat_iFun, Cat_Fun.
      unfold bimap, Bimap_Coproduct, case_, case_sum, CoprodCase_Kleisli, case_sum.
      intros ?.
      repeat match goal with
      | |- context[match ?x with | _ => _ end] => simpl; destruct x eqn:?EQ
             end; try reflexivity.
    Qed.

    Lemma assoc_l_sktree {A B C} :
      assoc_l ⩯ @lift_sktree _ _ E _ _ (@assoc_l _ iFun _ _ A B C).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite unfold_assoc_l, assoc_l_kleisli.
      rewrite unfold_assoc_l_iFun.
      unfold isum_suml, sum_isuml.
      rewrite !bimap_pure_id, !bimap_id_pure.
      repeat rewrite compose_pure.
      reflexivity.
    Qed.

    Lemma assoc_r_sktree {A B C} :
      assoc_r ⩯ @lift_sktree _ _ E _ _ (@assoc_r _ iFun _ _ A B C).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite unfold_assoc_r, assoc_r_ktree.
      rewrite unfold_assoc_r_iFun.
      unfold isum_suml, sum_isuml.
      rewrite !bimap_pure_id, !bimap_id_pure.
      repeat rewrite compose_pure.
      reflexivity.
    Qed.

    Global Instance Category_Fun : Category Fun.
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Global Instance Coproduct_Fun : Coproduct Fun sum.
    Proof.
      constructor.
      - intros a b c f g.
        cbv; reflexivity.
      - intros a b c f g.
        cbv; reflexivity.
      - intros a b c f g fg Hf Hg [x | y]; cbv in *; auto.
      - typeclasses eauto.
    Qed.

    Instance cat_iFun_CatIdL : CatIdL iFun.
    Proof. red; reflexivity. Qed.

    Instance cat_iFun_CatIdR : CatIdR iFun.
    Proof. red; reflexivity. Qed.

    Instance cat_iFun_assoc : CatAssoc iFun.
    Proof. red; reflexivity. Qed.

    Instance Proper_cat_iFun {a b c}
      : @Proper (iFun a b -> iFun b c -> iFun a c) (eq2 ==> eq2 ==> eq2) cat.
    Proof.
      typeclasses eauto.
    Qed.

    Global Instance Category_iFun : Category iFun.
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Global Instance Proper_case_iFun {A B C} :
      @Proper (iFun A C -> iFun B C -> _)
              (eq2 ==> eq2 ==> eq2) case_.
    Proof.
      intros x x' EQx y y' EQy z.
      unfold case_, case_isum.
      rewrite EQy, EQx; reflexivity.
    Qed.

    Global Instance Coproduct_iFun : Coproduct iFun isum.
    Proof with try typeclasses eauto.
      constructor.
      - intros a b c f g.
        unfold case_, case_isum, inl_, isum_inl.
        unfold cat at 1, Cat_iFun.
        rewrite (cat_assoc inl_ sum_isum _), <- (cat_assoc sum_isum _ _), semi_iso, cat_id_l...
        unfold eq2, Eq2_iFun; rewrite case_inl...
        reflexivity.
      - intros a b c f g.
        unfold case_, case_isum, inr_, isum_inr.
        unfold cat at 1, Cat_iFun.
        rewrite (cat_assoc inr_ sum_isum _), <- (cat_assoc sum_isum _ _), semi_iso, cat_id_l...
        unfold eq2, Eq2_iFun; rewrite case_inr...
        reflexivity.
      - intros a b c f g fg Hf Hg x.
        unfold case_, case_isum, inl_, isum_inl, inr_, isum_inr in *.
        rewrite <- Hf, <- Hg.
        destruct Fsum; cbv.
        destruct (isum_sum a b x) eqn:EQ.
        + setoid_rewrite <- EQ.
          destruct (sum_Iso a b).
          specialize (iso_mono x); setoid_rewrite iso_mono; reflexivity.
        + setoid_rewrite <- EQ.
          destruct (sum_Iso a b).
          specialize (iso_mono x); setoid_rewrite iso_mono; reflexivity.
      - typeclasses eauto.
   Qed.

    Lemma unfold_bimap_iFun: forall {A B C D} (f: F A -> F C) (g: F B -> F D),
      @bimap _ iFun _ _ _ _ _ _ f g
    ⩯ isum_sum >>> @bimap _ Fun _ _ _ _ _ _ f g >>> sum_isum.
    Proof with try typeclasses eauto.
      unfold eq2, Eq2_iFun.
      intros A B C D ab cd.
      unfold bimap, Bimap_Coproduct.
      unfold cat at 1 2, Cat_iFun.
      unfold case_ at 1, case_isum.
      unfold inl_ at 1, inr_ at 1, isum_inl, isum_inr.
      rewrite cat_assoc, cat_case...
      rewrite 2 cat_assoc...
      reflexivity.
    Qed.

  End UnfoldingLemmas.

  (* Good behaviour of [lift_sktree] *)
  Section Lift_sktree.

    Lemma bimap_id_slift {A B C} (f : F B -> F C) :
      bimap (id_ A) (@lift_sktree _ _ E _ _ f) ⩯ lift_sktree (bimap (id_ A) f).
    Proof.
      unfold_sktree. unfold lift_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite unfold_bimap, bimap_id_pure.
      rewrite unfold_bimap_iFun.
      unfold isum_suml, sum_isuml.
      repeat rewrite compose_pure.
      reflexivity.
    Qed.

    Lemma bimap_slift_id {A B C} (f : F A -> F B) :
      bimap (@lift_sktree _ _ E _ _ f) (id_ C) ⩯ lift_sktree (bimap f (id_ _)).
    Proof.
      unfold_sktree. unfold lift_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite unfold_bimap, bimap_pure_id.
      rewrite unfold_bimap_iFun.
      unfold isum_suml, sum_isuml.
      repeat rewrite compose_pure.
      reflexivity.
    Qed.

    Global Instance eq_lift_sktree {A B: i} :
      Proper (@eq2 _ iFun _ A B ==> eq2) (@lift_sktree _ _ E A B).
    Proof.
      intros ? ? ?.
      unfold lift_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite H; reflexivity. 
    Qed.

    Lemma lift_sktree_id {A: i}: id_ A ⩯ @lift_sktree _ _ E A A (id_ A).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.
      reflexivity.
    Qed.

    Fact compose_lift_sktree {A B C} (ab : F A -> F B) (bc : F B -> F C) :
      @lift_sktree _ _ E _ _ ab >>> lift_sktree bc ⩯ lift_sktree (ab >>> bc).
    Proof.
      unfold lift_sktree, cat, Cat_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.      
      rewrite compose_pure; reflexivity.
    Qed.

    Fact compose_lift_sktree_l {A B C D} (f: F A -> F B) (g: F B -> F C) (k: sktree C D) :
      lift_sktree f >>> (lift_sktree g >>> k) ⩯ lift_sktree (f >>> g) >>> k.
    Proof.
      unfold lift_sktree, cat, Cat_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.      
      rewrite compose_pure_l; reflexivity.
    Qed.

    Fact compose_lift_sktree_r {A B C D} (f: F B -> F C) (g: F C -> F D) (k: sktree A B) :
      (k >>> lift_sktree f) >>> lift_sktree g ⩯ k >>> lift_sktree (f >>> g).
    Proof.
      unfold lift_sktree, cat, Cat_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite compose_pure_r; reflexivity.
    Qed.

    Fact lift_compose_sktree {A B C} (f: F A -> F B) (bc: sktree B C):
        lift_sktree f >>> bc ⩯ fun a => bc (f a).
    Proof.
      unfold lift_sktree, cat, Cat_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite pure_cat; reflexivity.
    Qed.

    Fact compose_sktree_lift {A B C}: forall (ab: sktree A B) (g: F B -> F C),
        (ab >>> lift_sktree g)
          ⩯ (fun a => ITree.map g (ab a)).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.
      reflexivity.
    Qed.

  End Lift_sktree.

  Section CategoryLaws.

    Global Instance CatAssoc_sktree : CatAssoc sktree.
    Proof with try typeclasses eauto.
      intros A B C D f g h.
      unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite cat_assoc...
      reflexivity.
    Qed.

    (** *** [id_sktree] respect identity laws *)
    Global Instance CatIdL_sktree : CatIdL sktree.
    Proof with try typeclasses eauto.
      intros A B f.
      unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite cat_id_l...
      reflexivity.
    Qed.
    
    Global Instance CatIdR_sktree : CatIdR sktree.
    Proof with try typeclasses eauto.
      intros A B f.
      unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite cat_id_r...
      reflexivity.
    Qed.

    Instance Proper_cat_sktree {a b c}
      : @Proper (sktree a b -> sktree b c -> sktree a c) (eq2 ==> eq2 ==> eq2) cat.
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.
      repeat intro.
      apply Proper_cat_Kleisli. apply H. apply H0.
    Qed.

    Global Instance Category_sktree : Category sktree.
    Proof with try typeclasses eauto.
      constructor...
    Qed.

    Global Instance InitialObject_sktree : InitialObject sktree iI. 
    Proof.
      intros a f x; exfalso; apply iI_void in x; inversion x.
    Qed.

    Lemma empty_ktree_is_empty: forall a,
        @empty Type (ktree E) _ _ a ⩯ lift_ktree (@empty Type _ _ _ a). 
    Proof.
      intros x [].
    Qed.

    Lemma unit_l_sktree (A : i) :
      unit_l ⩯ @lift_sktree _ _ E _ _ (@unit_l _ iFun _ _ _ A).
    Proof.
      unfold unit_l, UnitL_Coproduct, lift_sktree.
      unfold_sktree.
      unfold isum_suml, iI_voidl.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite pure_id, empty_ktree_is_empty.
      rewrite compose_pure.
      rewrite case_pure.
      rewrite compose_pure.
      reflexivity.
    Qed.

    Lemma unit_l'_sktree (A : i) :
      unit_l' ⩯ @lift_sktree _ _ E _ _ (@unit_l' _ iFun _ iI _ A).
    Proof.
      unfold unit_l', UnitL'_Coproduct.
      unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      unfold inr_ at 2; unfold isum_inr.
      rewrite <- compose_pure.
      reflexivity.
    Qed.

    Lemma unit_r_sktree (A : i) :
      unit_r ⩯ @lift_sktree _ _ E _ _ (@unit_r _ iFun _ _ _ A).
    Proof.
      unfold unit_r, UnitR_Coproduct, lift_sktree.
      unfold_sktree.
      unfold isum_suml, iI_voidl.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite pure_id, empty_ktree_is_empty.
      rewrite compose_pure.
      rewrite case_pure.
      rewrite compose_pure.
      reflexivity.
    Qed.

    Lemma unit_r'_sktree (A : i) :
      unit_r' ⩯ @lift_sktree _ _ E _ _ (@unit_r' _ iFun _ iI _ A).
    Proof.
      unfold unit_r', UnitR'_Coproduct, lift_sktree.
      unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      unfold inl_ at 2; unfold isum_inl.
      rewrite <- compose_pure.
      reflexivity.
    Qed.

    Lemma case_l_sktree {A B: i} (ab: sktree A (isum iI B)) :
      ab >>> unit_l ⩯ (fun a: F A => ITree.map unit_l (ab a)).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.      
      rewrite unit_l_sktree.
      reflexivity.
    Qed.

    Lemma case_l_sktree' {A B: i} (f: sktree (isum iI A) (isum iI B)) :
      unit_l' >>> f ⩯ fun a => f (@inr_ _ iFun _ _ _ _ a).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.            
      rewrite unit_l'_sktree.
      unfold_sktree; unfold isum_inr.
      unfold unit_l', UnitL'_Coproduct.
      intro. unfold cat, Cat_Kleisli, lift_ktree; cbn.
      rewrite bind_ret; reflexivity.
    Qed.

    Lemma case_r_sktree' {A B: i} (f: sktree (isum A iI) (isum B iI)) :
      unit_r' >>> f ⩯ fun a => f (@inl_ _ iFun _ _ _ _ a).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.                  
      rewrite unit_r'_sktree.
      unfold_sktree; unfold isum_inr.
      unfold unit_l', UnitL'_Coproduct.
      intro. unfold cat, Cat_Kleisli, lift_ktree; cbn.
      rewrite bind_ret_; reflexivity.
    Qed.

    Lemma case_r_sktree {A B: i} (ab: sktree A (isum B iI)) :
      ab >>> unit_r ⩯ (fun a: F A => ITree.map unit_r (ab a)).
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.                  
      rewrite unit_r_sktree.
      reflexivity.
    Qed.

  End CategoryLaws.

  Section MonoidalCategoryLaws.

    (** *** [Unitors] lemmas *)

    Global Instance CaseInl_sktree: CaseInl sktree isum.
    Proof.
      red; intros; unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.            
      rewrite <- cat_assoc.
      rewrite (cat_assoc inl_).
      rewrite semi_iso.
      rewrite cat_id_r.
      rewrite case_inl.
      reflexivity.
      all: try typeclasses eauto.
    Qed.

    Global Instance CaseInr_sktree: CaseInr sktree isum.
    Proof.
      red; intros; unfold_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.            
      rewrite <- cat_assoc.
      rewrite (cat_assoc inr_).
      rewrite semi_iso.
      rewrite cat_id_r.
      rewrite case_inr.
      reflexivity.
      all: try typeclasses eauto.
    Qed.

    Global Instance CaseUniversal_sktree: CaseUniversal sktree isum.
    Proof.
      red; unfold_sktree; intros.
      unfold eq2, Eq2_sktree, eutt_sktree.                  
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

    Global Instance Proper_case_sktree {A B C} :
      @Proper (sktree A C -> sktree B C -> _)
              (eq2 ==> eq2 ==> eq2) case_.
    Proof.
      unfold eq2, Eq2_sktree, eutt_sktree.            
      intros x x' EQx y y' EQy.
      unfold case_, Case_sktree.
      rewrite EQy, EQx; reflexivity.
    Qed.

    Global Instance Coproduct_sktree : Coproduct sktree isum.
    Proof.
      constructor; try typeclasses eauto.
    Qed.

  End MonoidalCategoryLaws.

  Section IterativeCategoryLaws.

    (* This proof is weirdly low level, some other proper instances migth be missing *)
    Instance eq_sktree_iter {A B} :
      @Proper (sktree A (isum A B) -> sktree A B) (eq2 ==> eq2) iter.
    Proof.
      intros f g H.
      apply eq2_ktree_iter.
      unfold eq2, Eq2_sktree, eutt_sktree in H.         
      rewrite H.
      reflexivity.
    Qed.

    Global Instance eq_sktree_compose {A B C} :
      @Proper (sktree A B -> sktree B C -> _) (eq2 ==> eq2 ==> eq2) cat.
    Proof.
      intros ab ab' eqAB bc bc' eqBC.
      unfold eq2, Eq2_sktree, eutt_sktree in *.
      rewrite eqAB, eqBC.
      reflexivity.
    Qed.

    Instance IterUnfold_sktree : IterUnfold sktree isum.
    Proof.
      red; intros.
      unfold iter, Iter_sktree, case_, Case_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite iter_unfold at 1.
      rewrite cat_assoc.
      reflexivity.
    Qed.

    Instance IterNatural_sktree : IterNatural sktree isum.
    Proof.
      red; intros.
      unfold cat, Cat_sktree, iter, Iter_sktree.
      rewrite iter_natural.
      apply eq2_ktree_iter.
      pose proof (@unfold_bimap).
      rewrite (cat_assoc _ _ isum_suml).
      rewrite unfold_bimap.
      rewrite (cat_assoc _ _ isum_suml).
      rewrite (semi_iso _ _), cat_id_r.
      rewrite cat_assoc. reflexivity.
    Qed.

    Instance IterDinatural_sktree : IterDinatural sktree isum.
    Proof.
      red; intros.
      unfold cat, Cat_sktree, case_, Case_sktree, inr_, Inr_sktree, iter, Iter_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite 2 cat_assoc, cat_case, cat_assoc, (semi_iso _ _), cat_id_r.
      rewrite <- cat_assoc.
      rewrite iter_dinatural.
      rewrite !cat_assoc.
      rewrite cat_case, cat_assoc, (semi_iso _ _), cat_id_r.
      reflexivity.
    Qed.

    Instance IterCodiagonal_sktree : IterCodiagonal sktree isum.
    Proof.
      red; intros.
      unfold cat, Cat_sktree, case_, Case_sktree, inl_, Inl_sktree, iter, Iter_sktree.
      unfold eq2, Eq2_sktree, eutt_sktree.
      rewrite iter_natural.
      rewrite iter_codiagonal.
      rewrite cat_assoc, bimap_case, cat_id_l, cat_id_r.
      symmetry.
      rewrite 2 cat_assoc.
      rewrite cat_case, cat_assoc, (semi_iso _ _), cat_id_r.
      unfold id_, Id_sktree. rewrite cat_id_l.
      rewrite cat_assoc.
      reflexivity.
    Qed.

    Global Instance Iterative_sktree : Iterative sktree isum.
    Proof.
      split; typeclasses eauto.
    Qed.

  End IterativeCategoryLaws.

End Facts.
