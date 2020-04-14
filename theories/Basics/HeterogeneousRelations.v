From Coq Require Import
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Basics
     Basics.CategoryTheory
     Basics.CategoryOps
.

(* Heterogeneous relation definition, modified from https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)

Section Relation_Definition.

  Definition relation (A B : Type) := A -> B -> Prop.

  Definition compose {A B C} (g : relation B C) (f : relation A B) :=
    fun (a : A) (c : C) => exists b, (f a b) /\ (g b c).

End Relation_Definition.

Module RelNotations.

  Declare Scope relation_scope.
  Open Scope relation_scope.

  Notation " g ∘ f " := (compose g f)
    (at level 40, left associativity) : relation_scope.

End RelNotations.

Import RelNotations.
Open Scope relation_scope.

(* IY : Probably good to typeclassify this. *)
Section Relations_of_Relations.

  (* Heterogeneous notion of subrelation.  *)
  Definition inclusion {A B} (R1 R2 : relation A B) : Prop :=
    forall (x : A) (y : B), R1 x y -> R2 x y.

  (* For future: Maybe add transpose of relation? *)

End Relations_of_Relations.

(* SAZ: There is probably a nice way to typeclassify the eq_rel proofs *)
Section Relation_Classes.

Definition eq_rel {A B} (R : A -> B -> Prop) (S : A -> B -> Prop) :=
  inclusion R S /\ inclusion S R.

Lemma eq_rel_prod_eq : forall A B, eq_rel (prod_rel eq eq) (eq : A * B -> A * B -> Prop).
Proof.
  intros.
  unfold eq_rel; split; unfold inclusion; intros.
  - inversion H; subst. reflexivity.
  - destruct x; destruct y; inversion H; subst; constructor; reflexivity.
Qed.

Global Instance eq_rel_Reflexive {A B} : Reflexive (@eq_rel A B).
Proof.
  red. unfold eq_rel, inclusion. tauto.
Qed.

Global Instance eq_rel_Symmetric {A B} : Symmetric (@eq_rel A B).
Proof.
  red. unfold eq_rel, inclusion. tauto.
Qed.

Global Instance eq_rel_Transitive {A B} : Transitive (@eq_rel A B).
Proof.
  red. unfold eq_rel, inclusion. intros.
  destruct H, H0. split; eauto.
Qed.

Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
Proof.
  repeat red; unfold eq_rel, inclusion; split; intros;
  destruct H, H0, H1; split; eauto.
Qed.

End Relation_Classes.

Section Relation_Category.

  Instance rel_Eq2C : Eq2 relation := fun _ _ f g => eq_rel f g.

  Instance rel_IdC : Id_ relation := fun _ => eq.

  Instance rel_Cat : Cat relation := fun _ _ _ f g => compose g f.

  Global Instance rel_CatIdL: CatIdL relation.
    constructor; unfold inclusion, cat, id_, rel_Cat, rel_IdC, compose; intros.
    - edestruct H as (B' & EQ & R). rewrite <- EQ in R.
      assumption.
    - exists x. split. reflexivity. assumption.
  Qed.

  Global Instance rel_CatIdR: CatIdR relation.
    constructor; unfold inclusion, cat, id_, rel_Cat, rel_IdC, compose; intros.
    - edestruct H as (B' & R & EQ). rewrite EQ in R.
      assumption.
    - exists y. split. assumption. reflexivity.
  Qed.

  Global Instance rel_CatAssoc: CatAssoc relation.
  constructor; unfold inclusion, cat, id_, rel_Cat, rel_IdC, compose;
    intros A D H.
  - edestruct H as (C & (B & Rf & Rg) & Rh); clear H.
    exists B. split; [assumption | ].
    exists C. split; assumption.
  - edestruct H as (B & Rf & (C & Rg & Rh)); clear H.
    exists C. split; [ | assumption].
    exists B; split; assumption.
  Qed.

  Global Instance rel_ProperCat: forall a b c,
      @Proper (relation a b -> relation b c -> relation a c)
              (eq2 ==> eq2 ==> eq2) cat.
  intros a b c.
  constructor; unfold inclusion, cat, id_, rel_Cat, rel_IdC, compose;
    intros A C He.
  - edestruct He as (B & Hx & Hx0).
    unfold eq2, rel_Eq2C, eq_rel, inclusion in *.
    destruct H, H0.
    exists B. split. specialize (H A B Hx). assumption.
    specialize (H0 _ _ Hx0). assumption.
  - edestruct He as (B & Hy & Hy0).
    unfold eq2, rel_Eq2C, eq_rel, inclusion in *.
    destruct H, H0.
    exists B. split. specialize (H1 _ _ Hy). assumption.
    specialize (H2 _ _ Hy0). assumption.
  Qed.


  Global Instance rel_Category : Category relation :=
    {|
      category_cat_id_l := rel_CatIdL;
      category_cat_id_r := rel_CatIdR;
      category_cat_assoc := rel_CatAssoc;
      category_proper_cat := rel_ProperCat
    |}.

End Relation_Category.
