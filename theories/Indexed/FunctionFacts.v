(** * Theorems for [ITree.Indexed.Function] *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Indexed.Function
     Indexed.Sum
     Indexed.Relation.

Set Universe Polymorphism.
(* end hide *)

Instance Proper_apply_IFun {E F : Type -> Type} {T : Type}
         (RE : forall T, E T -> E T -> Prop)
         (RF : forall T, F T -> F T -> Prop)
  : Proper (i_respectful RE RF ==> RE T ==> RF T) apply_IFun.
Proof.
  repeat red; eauto.
Qed.

Lemma fold_apply_IFun {E F : Type -> Type} {T : Type}
  : forall (f : E ~> F) (t : E T),
    f _ t = apply_IFun f t.
Proof.
  reflexivity.
Qed.

(* Instance subrelation_eeq_eqeq {A B: Type -> Type} {T} : *)
(*   @subrelation (A ~> B) eq2 (eq2 A ==> eq2 B)%signature := {}. *)
(* Proof. congruence. Qed. *)

Instance Equivalence_eeq {A B} : @Equivalence (IFun A B) eq2.
Proof. constructor; congruence. Qed.

Instance Proper_cat {A B C : Type -> Type} :
  @Proper (IFun A B -> IFun B C -> IFun A C) (eq2 ==> eq2 ==> eq2) cat.
Proof. cbv; congruence. Qed.

Instance cat_IFun_CatIdL : CatIdL IFun.
Proof. red; reflexivity. Qed.

Instance cat_IFun_CatIdR : CatIdR IFun.
Proof. red; reflexivity. Qed.

Instance cat_IFun_assoc : CatAssoc IFun.
Proof. red; reflexivity. Qed.

Instance InitialObject_void : InitialObject IFun void1 :=
  fun _ _ _ v => match v : void1 _ with end.

Instance eeq_case_sum {A B C} :
  @Proper (IFun A C -> IFun B C -> IFun (A +' B) C)
          (eq2 ==> eq2 ==> eq2) case_.
Proof. cbv; intros; subst; destruct _; auto. Qed.

Instance Category_IFun : Category IFun.
Proof.
  constructor; typeclasses eauto.    
Qed.

Instance Coproduct_IFun : Coproduct IFun sum1.
Proof.
  constructor.
  - intros a b c f g.
    cbv; reflexivity.
  - intros a b c f g.
    cbv; reflexivity.
  - intros a b c f g fg Hf Hg ? [x | y]; cbv in *; auto.
  - typeclasses eauto.
Qed.
