From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.HeterogeneousRelations
     Basics.Function
     Basics.Tacs.

(* Structure of the [Rel] category. Mainly for fun and to understand its
   structure for now, we are not using it at the moment. *)

Section Operations.

  Import RelNotations.
  Local Open Scope relationH_scope.

  (* Objects: [Type]
     Arrows : [relationH ≜ forall A B, A -> B -> Prop]
   *)

  (* Equivalence of morphisms is extensional equivalence *)
  Global Instance Eq2_rel : Eq2 relationH := @eq_rel.

  (* Importantly, note that composition of relations [R >>> S] posits
     the existence of an intermediate witness at the intermediate type
     [(R >>> S) x z <-> exists y, R x y /\ S y z]
   *)
  Global Instance Cat_rel : Cat relationH := fun _ _ _ f g => rel_compose g f.

  (* Identities are defined by the [eq] relations *)
  Global Instance Id_rel : Id_ relationH := @eq.

  (* As usual, [void] is the initial element *)
  Global Instance Initial_rel : Initial relationH void :=
    fun _ v => match v : void with end.

  (* [sum] with its injection functions seen as relations form the coproduct *)
  Global Instance Case_rel : Case relationH sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  Global Instance Inl_rel : Inl relationH sum :=
    fun A B => fun_rel inl.

  Global Instance Inr_rel : Inr relationH sum :=
    fun _ _ => fun_rel inr.

  (* Interestingly, it is also [sum] and not [prod] that forms the product *)

  Global Instance Pair_rel : Pair relationH sum :=
    fun A B C l r c => case_sum _ _ _ (l c) (r c).

  Global Instance Fst_rel : Fst relationH sum :=
    fun _ _ x a => x = inl a.

  Global Instance Snd_rel : Snd relationH sum :=
    fun _ _ x a => x = inr a.

  (* My first intuition for the product was indeed to use [prod] as follows.
     However this fails to satisfy the necessary equations: if you think of
     [pair f g >>> fst ≈ f]
     This cannot hold since if [g] is the empty relation, then so is [pair f g]
   *)
  (* Global Instance Pair_rel : Pair relationH prod := *)
  (*   fun _ _ _ l r c '(a,b) => l c a /\ r c b. *)

  (* Global Instance Fst_rel : Fst relationH prod := *)
  (*   fun A B => fun_rel fst. *)

  (* Global Instance Snd_rel : Snd relationH prod := *)
  (*   fun _ _ => fun_rel snd. *)

  (* Both ⊕ and ⊗ are bimaps with respect to with relationH forms a monoidal category.
     I am not sure if they are isomorphic to the bimaps derived from the product and coproduct?
   *)
  Global Instance Bimap_sum_rel : Bimap relationH sum :=
    fun (a b c d : Type) R S => R ⊕ S.

  Global Instance AssocR_sum : AssocR relationH sum :=
    fun A B C ab_c a_bc =>
      match ab_c, a_bc with
      | inl (inl a), inl a'       => a = a'
      | inl (inr b), inr (inl b') => b = b'
      | inr c, inr (inr c')       => c = c'
      | _, _                      => False
      end.

  Global Instance AssocL_sum : AssocL relationH sum :=
    fun A B C ab_c a_bc =>
      match ab_c, a_bc with
      | inl a, inl (inl a')       => a = a'
      | inr (inl b), inl (inr b') => b = b'
      | inr (inr c), inr c'       => c = c'
      | _, _                      => False
      end.

  Global Instance UnitL_sum : UnitL relationH sum void :=
    fun _ ma a' => match ma with
                | inl abs => match abs with end
                | inr a => a = a'
                end.

  Global Instance UnitR_sum : UnitR relationH sum void :=
    fun _ ma a' => match ma with
                | inr abs => match abs with end
                | inl a => a = a'
                end.

  Global Instance UnitL'_sum : UnitL' relationH sum void :=
    fun _ a ma' => match ma' with
                | inl abs => match abs with end
                | inr a' => a = a'
                end.

  Global Instance UnitR'_sum : UnitR' relationH sum void :=
    fun _ a ma' => match ma' with
                | inr abs => match abs with end
                | inl a' => a = a'
                end.

  Global Instance Bimap_prod_rel : Bimap relationH prod :=
    fun (a b c d : Type) R S => R ⊗ S.

  Global Instance AssocR_prod : AssocR relationH prod :=
    fun A B C '(a,b,c) '(a',(b',c')) => a = a' /\ b = b' /\ c = c'.

  Global Instance AssocL_prod : AssocL relationH prod :=
    fun A B C '(a,(b,c)) '(a',b',c') => a = a' /\ b = b' /\ c = c'.

  Global Instance UnitL_prod : UnitL relationH prod unit :=
    fun _ '(_,a) a' =>  a = a'.

  Global Instance UnitR_prod : UnitR relationH prod unit :=
    fun _ '(a,_) a' => a = a'.

  Global Instance UnitL'_prod : UnitL' relationH prod unit :=
    fun _ a '(_,a') => a = a'.

  Global Instance UnitR'_prod : UnitR' relationH prod unit :=
    fun _ a '(a',_) => a = a'.

  (* The [transpose] operation forms a [dagger] category *)

  Global Instance Dagger_rel : Dagger relationH :=
    fun a b R =>  transpose R.

End Operations.

(** The following instances prove that the operations claimed above to be what
they are are indeed what the are **)

Section Facts.

  Section CategoryRel.

    Global Instance CatIdL_rel: CatIdL relationH.
    Proof.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, rel_compose; intros.
      - edestruct H as (B' & EQ & R). rewrite <- EQ in R.
        assumption.
      - exists x. split. reflexivity. assumption.
    Qed.

    Global Instance CatIdR_rel: CatIdR relationH.
    Proof.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, rel_compose; intros.
      - edestruct H as (B' & R & EQ). rewrite EQ in R.
        assumption.
      - exists y. split. assumption. reflexivity.
    Qed.

    Global Instance CatAssoc_rel: CatAssoc relationH.
    Proof.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, rel_compose;
        intros A D H.
      - edestruct H as (C & (B & Rf & Rg) & Rh); clear H.
        exists B. split; [assumption | ].
        exists C. split; assumption.
      - edestruct H as (B & Rf & (C & Rg & Rh)); clear H.
        exists C. split; [ | assumption].
        exists B; split; assumption.
    Qed.

    Global Instance ProperCat_rel: forall a b c,
        @Proper (relationH a b -> relationH b c -> relationH a c)
                (eq2 ==> eq2 ==> eq2) cat.
    Proof.
      intros a b c.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, rel_compose;
        intros A C He.
      - edestruct He as (B & Hx & Hx0).
        unfold eq2, Eq2_rel, eq_rel, subrelationH in *.
        destruct H, H0.
        exists B. split. specialize (H A B Hx). assumption.
        specialize (H0 _ _ Hx0). assumption.
      - edestruct He as (B & Hy & Hy0).
        unfold eq2, Eq2_rel, eq_rel, subrelationH in *.
        destruct H, H0.
        exists B. split. specialize (H1 _ _ Hy). assumption.
        specialize (H2 _ _ Hy0). assumption.
    Qed.

    Global Instance Category_rel : Category relationH.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End CategoryRel.

  Global Instance InitialObject_rel : InitialObject relationH void.
  Proof.
    split; intros [].
  Qed.

  Section CoproductRel.

    Global Instance CaseInl_rel : CaseInl relationH sum.
    Proof.
      split.
      intros ? ? [[] [H1 H2]]; inversion H1; subst; apply H2.
      intros x ? ?.
      exists (inl x); split; auto; reflexivity.
    Qed.

    Global Instance CaseInr_rel : CaseInr relationH sum.
    Proof.
      split.
      intros ? ? [[] [H1 H2]]; inversion H1; subst; apply H2.
      intros x ? ?.
      exists (inr x); split; auto; reflexivity.
    Qed.

    Global Instance CaseUniversal_rel : CaseUniversal relationH sum.
    Proof.
      intros a b c R S T [TR RT] [TS ST].
      split.
      intros [] ? ?; cbn; [apply TR | apply TS]; eexists; split; eauto; reflexivity.
      intros [] ? HR; [apply RT in HR | apply ST in HR];
        destruct HR as [? [EQ ?]]; repeat red in EQ; subst; auto.
    Qed.

    Global Instance Proper_Case_rel : forall a b c : Type, Proper (eq2 ==> eq2 ==> eq2) (@case_ _ _ _ _ a b c).
    Proof.
      intros ? ? ? R S [RS SR] T U [TU UT]; split; intros [] ? ?; cbn in *;
        [apply RS | apply TU | apply SR | apply UT]; auto.
    Qed.

    Global Instance Coproduct_rel : Coproduct relationH sum.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End CoproductRel.

  Section ProductRel.

    Global Instance PairFst_rel : PairFst relationH sum.
    Proof.
      split.
      - intros ? ? ([] & ? & EQ); inversion EQ; subst; auto.
      - intros ? ? ?.
        exists (inl y); cbv; auto.
    Qed.

    Global Instance PairSnd_rel : PairSnd relationH sum.
    Proof.
      split.
      - intros ? ? ([] & ? & EQ); inversion EQ; subst; auto.
      - intros ? ? ?.
        exists (inr y); cbv; auto.
    Qed.

    Global Instance PairUniversal_rel : PairUniversal relationH sum.
    Proof.
      intros ? ? ? R S RS [RSR RRS] [RSS SRS]; split.
      - cbv. intros ? [] ?; [apply RSR | apply RSS];
               (eexists; split; [| reflexivity]; auto).
      - cbv. intros ? [] EQ; [apply RRS in EQ | apply SRS in EQ]; destruct EQ as [[] [? EQ]];
               inversion EQ; subst; auto.
    Qed.

    Global Instance Proper_pair_rel : forall a b c : Type, Proper (eq2 ==> eq2 ==> eq2) (@pair_ _ _ _ _ a b c).
    Proof.
      intros ? ? ? R S [RS SR] T U [TU UT]; split.
      cbv; intros ? [] ?; [apply RS | apply TU]; auto.
      cbv; intros ? [] ?; [apply SR | apply UT]; auto.
    Qed.

    Global Instance Product_rel : Product relationH sum.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End ProductRel.

  Section DaggerRel.

    Global Instance DaggerInvolution_rel : DaggerInvolution relationH.
    Proof.
      split; intros ? ? H; apply H.
    Qed.

    Local Existing Instance Eq2_Op.
    Local Existing Instance Id_Op.
    Local Existing Instance Cat_Op.

    Global Instance DaggerFunctor_rel : Functor (op relationH) relationH id (@dagger _ _ _).
    Proof.
      constructor.
      - split; intros ? ? H; inversion H; subst; reflexivity.
      - split; intros ? ? (? & ? & ?); eexists; eauto.
      - intros a b x y [INCL1 INCL2].
        split; intros ? ? H; [apply INCL1 | apply INCL2]; apply H.
    Qed.

    Global Instance DaggerLaws_rel : DaggerLaws relationH.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End DaggerRel.

  Section BifunctorProd.

    Global Instance BimapId_prod_rel : BimapId relationH prod.
    Proof.
      split.
      cbv; intros ? ? ?; subst; auto.
      destruct x, y.
      cbv; intros. inversion H; subst; auto.
      red. intros. destruct x, y. inversion H. subst. repeat red.
      repeat red in H. intuition. 
    Qed.

    Global Instance BimapCat_prod_rel : BimapCat relationH prod.
    Proof.
      split.
      - cbv; intros [] [] ([] & H1 & H2).
        inv H1; inv H2; eauto 6.
      - cbv; intros [] [] H; inv H.
        destruct H3 as (? & ? & ?), H5 as (? & ? & ?).
        eauto.
    Qed.

    Global Instance Bifunctor_prod_rel : Bifunctor relationH prod.
    Proof.
      constructor; try typeclasses eauto.
    Qed.

    Global Instance Iso_Assoc_prod_rel : forall a b c : Type, Iso relationH (@assoc_r _ relationH prod _ a b c) assoc_l.
    Proof.
      split.
      - cbv; split.
        + intros ? ? ?; repeat destructn prod.
          destructn ex; repeat destructn prod; repeat destructn and; subst; auto.
        + intros ((? & ?) & ?) ((x & y) & z) EQ; inv EQ.
          exists (x,(y,z)); intuition.
      - cbv; split.
        + intros ? ? ?; destructn ex; repeat destructn prod; intuition subst; auto.
        + intros ? (x & y & z) ->; repeat destructn prod.
          exists (x,y,z); intuition.
    Qed.

    Global Instance Iso_UnitL_prod_rel: forall a : Type, Iso relationH (@unit_l _ relationH prod _ _ a) unit_l'.
    Proof.
      split; cbv; split; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit); intuition subst; auto.
      eexists; intuition.
      exists (tt,y); auto.
    Qed.

    Global Instance Iso_UnitR_prod_rel: forall a : Type, Iso relationH (@unit_r _ relationH prod _ _ a) unit_r'.
    Proof.
      split; cbv; split; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit); intuition subst; auto.
      eexists; intuition.
      exists (y,tt); auto.
    Qed.

    Global Instance UnitLNatural_prod_rel : UnitLNatural relationH prod unit.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit || destructn and
                             || invn prod_rel).
      eexists; intuition subst; eauto.
      eexists; intuition subst; eauto.
    Qed.

    Global Instance UnitL'Natural_prod_rel : UnitL'Natural relationH prod unit.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit || destructn and
                             || invn prod_rel).
      eexists; intuition subst; eauto.
      exists (tt,x); intuition subst; auto.
    Qed.

    Global Instance AssocRUnit_prod_rel : AssocRUnit relationH prod unit.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit || destructn and
                             || invn prod_rel);
      econstructor; eauto. split. Unshelve. 3 : { exact ((a0, (tt, b0))). }
      cbn. intuition. econstructor; reflexivity.
    Qed.

    Global Instance AssocRAssocR_prod_rel : AssocRAssocR relationH prod.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn prod || invn @eq || destructn unit || destructn and
                             || invn prod_rel).
      exists (a1,b1,(c1,d1)); intuition; auto.
      exists (a1,(b1,c1,d1)); intuition; auto.
      exists (a1,(b1,c1),d1); intuition; auto.
    Qed.

    Global Instance Monoidal_prod_rel : Monoidal relationH prod unit.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End BifunctorProd.

  Section BifunctorSum.

    Global Instance BimapId_sum_rel : BimapId relationH sum.
    Proof.
      split.
      red. intros ? ? ?. repeat red in H.
      destruct x, y; subst; inversion H; subst; repeat red; auto.
      inversion H; inversion H2; subst; reflexivity.
      inversion H; inversion H2; subst; reflexivity.
      red. intros ? ? ?. repeat red in H.
      subst. repeat red. destruct y; econstructor; reflexivity.
    Qed.

    Global Instance BimapCat_sum_rel : BimapCat relationH sum.
    Proof.
      split.
      cbv. intros; destruct x, y; destruct H as (? & ? & ?); inversion H;
             inversion H0; subst; inversion H5; subst; econstructor; eauto.
      repeat intro. inversion H; inversion H0; inversion H3; repeat red; subst; eauto. 
      exists (inl x0). split; econstructor; eauto.
      exists (inr x0). split; econstructor; eauto.
    Qed.

    Global Instance Bifunctor_sum_rel : Bifunctor relationH sum.
    Proof.
      constructor; try typeclasses eauto.
    Qed.

    Global Instance Iso_Assoc_sum_rel : forall a b c : Type, Iso relationH (@assoc_r _ relationH sum _ a b c) assoc_l.
    Proof.
      split.
      - cbv; split;
          intros;
          repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit || destructn and
                  || invn prod_rel); intuition.
        exists (inl a0); intuition.
        exists (inr (inl b0)); intuition.
        exists (inr (inr c0)); intuition.
      - cbv; split; intros;
          repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit || destructn and
                  || invn prod_rel); intuition.
        exists (inl (inl a0)); intuition.
        exists (inl (inr b0)); intuition.
        exists (inr c0); intuition.
    Qed.

    Global Instance Iso_UnitL_sum_rel: forall a : Type, Iso relationH (@unit_l _ relationH sum _ _ a) unit_l'.
    Proof.
      split; cbv; split; intros; repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit); intuition subst; auto.
      eexists; intuition.
      exists (inr y); auto.
    Qed.

    Global Instance Iso_UnitR_sum_rel: forall a : Type, Iso relationH (@unit_r _ relationH sum _ _ a) unit_r'.
    Proof.
      split; cbv; split; intros; repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit); intuition subst; auto.
      eexists; intuition.
      exists (inl y); auto.
    Qed.

    Global Instance UnitLNatural_sum_rel : UnitLNatural relationH sum void.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit || destructn and
                             || invn sum_rel || invn void).
      eexists; intuition subst; eauto.
      eexists; intuition subst; eauto.
    Qed.

    Global Instance UnitL'Natural_sum_rel : UnitL'Natural relationH sum void.
    Proof.
      split;
        cbv; intros; repeat (subst || destructn ex || destructn sum || invn @eq || destructn unit || destructn and
                             || invn sum_rel || invn void).
      eexists; intuition subst; eauto.
      exists (inr x); intuition subst; auto.
    Qed.

    Global Instance AssocRUnit_sum_rel : AssocRUnit relationH sum void.
    Proof.
      split; cbv; intros.
      destruct H.
      destruct x; try destruct s; try destruct x0; try inversion H; try inversion H1; subst; eauto;
        try econstructor; try contradiction; eauto.
      destruct s; try contradiction; subst; eauto.
      inversion H; subst; eauto; try destruct a1; try contradiction; subst.
      inv H. exists (inl a2); eauto. 
      inv H; exists (inr (inr b2)); eauto. 
    Qed.

    Global Instance AssocRAssocR_sum_rel : AssocRAssocR relationH sum.
    Proof.
      split;
        cbv; intros;
          repeat (invn False || subst || destructn ex || destructn and || invn sum_rel
                  || destructn sum || invn @eq || destructn unit).
      - exists (inl (inl a2)); intuition; auto.
      - exists (inl (inr b0)); intuition; auto.
      - exists (inr (inl c0)); intuition; auto.
      - exists (inr (inr d0)); intuition; auto.
      - exists (inl a1); intuition; auto.
        exists (inl (inl a1)); intuition; auto.
      - exists (inr (inl (inl b1))); intuition; econstructor; auto.
        split. econstructor. Unshelve. 3 : exact ((inr (inl b1))). intuition; auto.
        intuition.
      - exists (inr (inl (inr c0))); intuition; econstructor; auto.
        split. Unshelve. econstructor. Unshelve.
        3 : refine ((inr (inr c0))). intuition; econstructor; auto.
        intuition.
      - exists (inr (inr d0)); intuition; econstructor; auto.
        split. Unshelve. econstructor. reflexivity. cbn. auto.
     Qed.

    Global Instance Monoidal_sum_rel : Monoidal relationH sum void.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End BifunctorSum.

End Facts.
