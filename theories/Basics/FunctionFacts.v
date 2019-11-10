(** * Theorems for [ITree.Basics.Function] *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.Function.

Import CatNotations.
Local Open Scope cat_scope.
(* end hide *)

Instance subrelation_eeq_eqeq {A B} :
  @subrelation (A -> B) eq2 (@eq A ==> @eq B)%signature.
Proof. congruence. Qed.

Instance Equivalence_eeq {A B} : @Equivalence (Fun A B) eq2.
Proof. constructor; congruence. Qed.

Instance Proper_cat {A B C : Type} :
  @Proper (Fun A B -> Fun B C -> Fun A C) (eq2 ==> eq2 ==> eq2) cat.
Proof. cbv; congruence. Qed.

Instance cat_Fun_CatIdL : CatIdL Fun.
Proof. red; reflexivity. Qed.

Instance cat_Fun_CatIdR : CatIdR Fun.
Proof. red; reflexivity. Qed.

Instance cat_Fun_assoc : CatAssoc Fun.
Proof. red; reflexivity. Qed.

Instance InitialObject_void : InitialObject Fun void :=
  fun _ _ v => match v : void with end.

Instance eeq_case_sum {A B C} :
  @Proper (Fun A C -> Fun B C -> Fun (A + B) C)
          (eq2 ==> eq2 ==> eq2) case_.
Proof. cbv; intros; subst; destruct _; auto. Qed.

Instance Category_Fun : Category Fun.
Proof.
  constructor; typeclasses eauto.
Qed.

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
