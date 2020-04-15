From Coq Require Import
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Tacs
     Basics.Basics
     Basics.CategoryTheory
     Basics.CategoryOps
.

(* Heterogeneous relation definition, modified from https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)

Section Relation_Definition.

  Definition relation (A B : Type) := A -> B -> Prop.

  (* Heterogeneous notion of subrelation.  *)
  Definition inclusion {A B} (R S : relation A B) : Prop :=
    forall (x : A) (y : B), R x y -> S x y.

  Definition transpose {A B: Type} (R: A -> B -> Prop): B -> A -> Prop :=
    fun b a => R a b.

  Definition eq_rel {A B} (R : A -> B -> Prop) (S : A -> B -> Prop) :=
    inclusion R S /\ inclusion S R.

  Definition compose {A B C} (S : relation B C) (R : relation A B) :=
    fun (a : A) (c : C) => exists b, (R a b) /\ (S b c).

End Relation_Definition.

Arguments compose [A B C] S R.
Arguments inclusion [A B] R S.
Arguments transpose [A B] R.

Module RelNotations.

  Declare Scope relation_scope.
  Open Scope relation_scope.

  (* Notice the levels: (R ⊕ S ⊗ T ∘ U) is parsed as ((R ⊕ (S ⊗ T)) ∘ U) *)
  Infix "∘" := compose (at level 40, left associativity) : relation_scope.
  Infix "⊕" := sum_rel (at level 39, left associativity) : relation_scope.
  Infix "⊗" := prod_rel (at level 38, left associativity) : relation_scope.

  Infix "⊑" := inclusion (at level 90, no associativity) : relation_scope.
  Notation "† R" := (transpose R) (at level 5) : relation_scope.

  Infix "≡" := eq_rel (at level 89, no associativity) : relation_scope.

End RelNotations.

Import RelNotations.
Local Open Scope relation_scope.

(* SAZ: There is probably a nice way to typeclassify the eq_rel proofs *)
Section Relation_Classes.

  (* The names are picked to line up with the categorical names we will have later, where composition is the other way around *)
  Lemma eq_id_r: forall {A B} (R : relation A B),
    eq ∘ R ≡ R.
  Proof.
    split; intros!.
    - invn compose; invn and; subst; auto.
    - exists y; auto.
  Qed.

  Lemma eq_id_l: forall {A B} (R : relation A B),
    R ∘ eq ≡ R.
  Proof.
    split; intros!.
    - invn compose; invn and; subst; auto.
    - exists x; auto.
  Qed.

  Lemma eq_rel_prod_eq : forall A B, eq_rel (prod_rel eq eq) (eq : relation (A * B) (A * B)).
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

  Global Instance eq_rel_Equiv {A B} : Equivalence (@eq_rel A B).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
  Proof.
    repeat red; unfold eq_rel, inclusion; split; intros;
      destruct H, H0, H1; split; eauto.
  Qed.

  Global Instance transpose_Reflexive {A} (R : relation A A) {RR: Reflexive R} : Reflexive † R.
  Proof.
    red. intros x. unfold transpose. reflexivity.
  Qed.

  Global Instance transpose_Symmetric {A} (R : relation A A) {RS: Symmetric R} : Symmetric † R.
  Proof.
    red; intros x; unfold transpose; intros. symmetry. assumption.
  Qed.


  Global Instance transpose_Transitive {A} (R : relation A A) {RT : Transitive R} : Transitive † R.
  Proof.
    red; intros x; unfold transpose; intros. etransitivity; eauto.
  Qed.

End Relation_Classes.

Section SumRelInstances.
  Context {A B : Type}.
  Context (R : relation A A).
  Context (S : relation B B).

  Global Instance sum_rel_refl {RR: Reflexive R} {SR: Reflexive S} : Reflexive (R ⊕ S).
  Proof.
    intros []; auto.
  Qed.

  Global Instance sum_rel_sym {RS: Symmetric R} {SS: Symmetric S}  : Symmetric (R ⊕ S).
  Proof.
    intros ? ? []; auto.
  Qed.

  Global Instance sum_rel_trans {RT: Transitive R} {ST: Transitive S}  : Transitive (R ⊕ S).
  Proof.
    intros ? ? ? H1 H2; inv H1; inv H2; eauto.
  Qed.

  Global Instance sum_rel_eqv {RE: Equivalence R} {SE: Equivalence S} : Equivalence (R ⊕ S).
  Proof.
    constructor; typeclasses eauto.
  Qed.

End SumRelInstances.

Section SumRelProps.

  Lemma sum_compose {A B C D E F: Type}
        (R: relation A B) (S: relation B C)
        (T: relation D E) (U: relation E F)
  : eq_rel ((S ∘ R) ⊕ (U ∘ T)) ((S ⊕ U) ∘ (R ⊕ T)).
  Proof.
    split; intros!.
    - invn sum_rel; invn compose; invn and.
      all: eexists; split; econstructor; eauto.
    - invn compose; invn and; do 2 invn sum_rel.
      eauto.
      all: econstructor; eexists; eauto.
  Qed.

End SumRelProps.

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
