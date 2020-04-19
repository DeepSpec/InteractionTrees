From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Tacs
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.Function
     Basics.HeterogeneousRelations.

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
  Global Instance Cat_rel : Cat relationH := fun _ _ _ f g => compose g f.

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

  (* I'm not sure how we would actually want to work with these
       since we have two instances of [Bimap], ⊕ and ⊗, that we actually use.
       Additionally of course we have the two that are derived from
       the respective product and coproduct, which should be provably
       isomorphic to respectively ⊗ and ⊕.
   *)
  Global Instance Bimap_sum_rel : Bimap relationH sum :=
    fun (a b c d : Type) R S => R ⊕ S.

  Global Instance Bimap_prod_rel : Bimap relationH prod :=
    fun (a b c d : Type) R S => R ⊗ S.

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
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros.
      - edestruct H as (B' & EQ & R). rewrite <- EQ in R.
        assumption.
      - exists x. split. reflexivity. assumption.
    Qed.

    Global Instance CatIdR_rel: CatIdR relationH.
    Proof.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros.
      - edestruct H as (B' & R & EQ). rewrite EQ in R.
        assumption.
      - exists y. split. assumption. reflexivity.
    Qed.

    Global Instance CatAssoc_rel: CatAssoc relationH.
    Proof.
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose;
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
      constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose;
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
      intros ? ? [[] [H1 H2]]; inv H1; apply H2.
      intros x ? ?.
      exists (inl x); split; auto; reflexivity.
    Qed.

    Global Instance CaseInr_rel : CaseInr relationH sum.
    Proof.
      split.
      intros ? ? [[] [H1 H2]]; inv H1; apply H2.
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
      - intros ? ? ([] & ? & EQ); inv EQ; auto.
      - intros ? ? ?.
        exists (inl y); cbv; auto.
    Qed.

    Global Instance PairSnd_rel : PairSnd relationH sum.
    Proof.
      split.
      - intros ? ? ([] & ? & EQ); inv EQ; auto.
      - intros ? ? ?.
        exists (inr y); cbv; auto.
    Qed.

    Global Instance PairUniversal_rel : PairUniversal relationH sum.
    Proof.
      intros ? ? ? R S RS [RSR RRS] [RSS SRS]; split.
      - cbv. intros ? [] ?; [apply RSR | apply RSS];
               (eexists; split; [| reflexivity]; auto).
      - cbv. intros ? [] EQ; [apply RRS in EQ | apply SRS in EQ]; destruct EQ as [[] [? EQ]]; inv EQ; auto.
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
      - split; intros ? ? H; inv H; reflexivity.
      - split; intros ? ? (? & ? & ?); eexists; eauto.
      - intros a b x y [INCL1 INCL2].
        split; intros ? ? H; [apply INCL1 | apply INCL2]; apply H.
    Qed.

    Global Instance DaggerLaws_rel : DaggerLaws relationH.
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End DaggerRel.

End Facts.
