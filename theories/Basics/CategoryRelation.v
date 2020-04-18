From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.Function
     Basics.HeterogeneousRelations.

Section Operations.

  Import RelNotations.
  Local Open Scope relationH_scope.

  Global Instance Eq2_rel : Eq2 relationH := @eq_rel.

  Global Instance Cat_rel : Cat relationH := fun _ _ _ f g => compose g f.

  Global Instance Id_rel : Id_ relationH := @eq.

  Global Instance Initial_rel : Initial relationH void :=
    fun _ v => match v : void with end.

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

  Global Instance Case_rel : Case relationH sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  Global Instance Inl_rel : Inl relationH sum :=
    fun A B => fun_rel inl.

  Global Instance Inr_rel : Inr relationH sum :=
    fun _ _ => fun_rel inr.

  Global Instance Pair_rel : Pair relationH prod :=
    fun _ _ _ l r c '(a,b) => l c a /\ r c b.

  Global Instance Fst_rel : Fst relationH prod :=
    fun A B => fun_rel fst.

  Global Instance Snd_rel : Snd relationH prod :=
    fun _ _ => fun_rel snd.

End Operations.

Global Instance CatIdL_rel: CatIdL relationH.
constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros.
- edestruct H as (B' & EQ & R). rewrite <- EQ in R.
  assumption.
- exists x. split. reflexivity. assumption.
Qed.

Global Instance rel_CatIdR: CatIdR relationH.
constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros.
- edestruct H as (B' & R & EQ). rewrite EQ in R.
  assumption.
- exists y. split. assumption. reflexivity.
Qed.

Global Instance rel_CatAssoc: CatAssoc relationH.
constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose;
  intros A D H.
- edestruct H as (C & (B & Rf & Rg) & Rh); clear H.
  exists B. split; [assumption | ].
  exists C. split; assumption.
- edestruct H as (B & Rf & (C & Rg & Rh)); clear H.
  exists C. split; [ | assumption].
  exists B; split; assumption.
Qed.

Global Instance rel_ProperCat: forall a b c,
    @Proper (relationH a b -> relationH b c -> relationH a c)
            (eq2 ==> eq2 ==> eq2) cat.
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


Global Instance rel_Category : Category relationH :=
  {|
  category_cat_id_l := CatIdL_rel;
  category_cat_id_r := rel_CatIdR;
  category_cat_assoc := rel_CatAssoc;
  category_proper_cat := rel_ProperCat
  |}.

