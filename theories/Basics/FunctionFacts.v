(** * Theorems for [ITree.Basics.Function] *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Axioms
     Basics.Basics
     Basics.Category
     Basics.Function.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

#[global]
Instance subrelation_eeq_eqeq {A B} :
  @subrelation (A -> B) eq2 (@eq A ==> @eq B)%signature.
Proof. congruence. Qed.

#[global]
Instance Equivalence_eeq {A B} : @Equivalence (Fun A B) eq2.
Proof. constructor; congruence. Qed.

#[global]
Instance Proper_cat {A B C : Type} :
  @Proper (Fun A B -> Fun B C -> Fun A C) (eq2 ==> eq2 ==> eq2) cat.
Proof. cbv; congruence. Qed.

#[global]
Instance cat_Fun_CatIdL : CatIdL Fun.
Proof. red; reflexivity. Qed.

#[global]
Instance cat_Fun_CatIdR : CatIdR Fun.
Proof. red; reflexivity. Qed.

#[global]
Instance cat_Fun_assoc : CatAssoc Fun.
Proof. red; reflexivity. Qed.

#[global]
Instance InitialObject_void : InitialObject Fun void :=
  fun _ _ v => match v : void with end.

#[global]
Instance TerminalObject_unit : TerminalObject Fun unit.
Proof. red. intros. intro. destruct (f a0). reflexivity. Qed.

#[global]
Instance eeq_case_sum {A B C} :
  @Proper (Fun A C -> Fun B C -> Fun (A + B) C)
          (eq2 ==> eq2 ==> eq2) case_.
Proof. cbv; intros; subst; destruct _; auto. Qed.

#[global]
Instance Category_Fun : Category Fun.
Proof.
  constructor; typeclasses eauto.
Qed.

#[global]
Instance Coproduct_Fun : Coproduct Fun sum.
Proof.
  constructor.
  - intros a b c f g.
    cbv; reflexivity.
  - intros a b c f g.
    cbv; reflexivity.
  - intros a b c f g fg Hf Hg [x | y]; cbv in *; auto.
  - typeclasses eauto.
Qed.

#[global]
Instance PairFst_Fun : PairFst Fun prod.
Proof.
  split.
Qed.

#[global]
Instance PairSnd_Fun : PairSnd Fun prod.
Proof.
  split.
Qed.

#[global]
Instance PairUniversal_Fun : PairUniversal Fun prod.
Proof.
  repeat intro.
  unfold pair_, Pair_Fun. specialize (H a0). specialize (H0 a0). rewrite <- H.
  rewrite <- H0. unfold cat, Cat_Fun.
  destruct (fg a0). reflexivity.
Qed.

#[global]
Instance Proper_pair_Fun : forall a b c, Proper (eq2 ==> eq2 ==> eq2) (@pair_ _ _ _ _ a b c).
Proof.
  intros ? ? ? f1 f2 F g1 g2 G c.
  unfold pair_, Pair_Fun. rewrite F. rewrite G. reflexivity.
Qed.  

Section Products.
  Existing Instance Bimap_Product.

  #[global]
  Instance BimapId_Fun_prod : BimapId Fun prod.
  Proof.
    repeat intro.
    destruct a0. reflexivity.
  Qed.
   
  #[global]
  Instance BimapCat_Fun_prod : BimapCat Fun prod.
  Proof.
    repeat intro.
    destruct a.
    reflexivity.
  Qed.

  #[global]
  Instance BimapProper_Fun_prod :
    forall A B C D,
      @Proper ((A -> C) -> (B -> D) -> (A * B -> C * D)) (eq2 ==> eq2 ==> eq2) bimap.
  Proof.
    repeat intro.
    unfold bimap, Bimap_Product. rewrite H. rewrite H0. reflexivity.
  Qed.

  #[global]
  Instance Bifunctor_Fun_prod : Bifunctor Fun prod.
  Proof.
    constructor.
    - exact BimapId_Fun_prod.
    - exact BimapCat_Fun_prod.
    - exact BimapProper_Fun_prod.
  Qed.

  #[global]
  Instance Product_Fun : Product Fun prod.
  Proof.
    constructor; typeclasses eauto.
  Qed.  
  
End Products.

Section CartesianClosure.

  #[global]
  Instance CurryApply_Fun : CurryApply Fun prod Fun.
  Proof.
    red. repeat intro. destruct a0. unfold curry_, Curry_Fun, cat, Cat_Fun. reflexivity.
  Qed.

  (* Properness of currying requires(?) functional extensionality *)
  #[global]
  Instance CartesianClosed_Fun : CartesianClosed Fun unit prod Fun.
  Proof.
    constructor; try typeclasses eauto.
    repeat intro. unfold curry_, Curry_Fun. apply functional_extensionality.
    intros. apply H.
  Qed.
End CartesianClosure.
