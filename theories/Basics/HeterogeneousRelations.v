From Coq Require Import
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.Tacs
     Basics.Basics
     Basics.Function
     (* Basics.CategoryTheory *)
     (* Basics.CategoryOps *)
.

(* Heterogeneous relation definition, modified from https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)

Section RelationH_Definition.

  Definition relationH (A B : Type) := A -> B -> Prop.

  Definition compose {A B C} (S : relationH B C) (R : relationH A B) :=
    fun (a : A) (c : C) => exists b, (R a b) /\ (S b c).

  (* Heterogeneous notion of [subrelation] *)
  Class subrelationH {A B} (R S : relationH A B) : Prop :=
    is_subrelationH: forall (x : A) (y : B), R x y -> S x y.

  Definition eq_rel {A B} (R : A -> B -> Prop) (S : A -> B -> Prop) :=
    subrelationH R S /\ subrelationH S R.

  Definition transpose {A B: Type} (R: A -> B -> Prop): B -> A -> Prop :=
    fun b a => R a b.

  (* The graph of a function forms a relation *)
  Definition fun_rel {A B: Type} (f: A -> B): relationH A B :=
    fun a b => b = f a.

  (** ** Relations for morphisms/parametricity *)

  (** Logical relation for the [sum] type. *)
  Variant sum_rel {A1 A2 B1 B2 : Type}
          (RA : relationH A1 A2) (RB : relationH B1 B2)
    : relationH (A1 + B1) (A2 + B2) :=
  | inl_morphism a1 a2 : RA a1 a2 -> sum_rel RA RB (inl a1) (inl a2)
  | inr_morphism b1 b2 : RB b1 b2 -> sum_rel RA RB (inr b1) (inr b2)
  .

  (** Logical relation for the [prod] type. *)
  Variant prod_rel {A1 A2 B1 B2 : Type}
          (RA : relationH A1 A2) (RB : relationH B1 B2)
    : relationH (A1 * B1) (A2 * B2) :=
  | prod_morphism a1 a2 b1 b2 : RA a1 a2 -> RB b1 b2 -> prod_rel RA RB (a1, b1) (a2, b2)
  .

End RelationH_Definition.

Arguments compose [A B C] S R.
Arguments subrelationH [A B] R S.
Arguments transpose [A B] R.
Arguments sum_rel [A1 A2 B1 B2] RA RB.
Arguments inl_morphism {A1 A2 B1 B2 RA RB}.
Arguments inr_morphism {A1 A2 B1 B2 RA RB}.
Arguments prod_rel [A1 A2 B1 B2] RA RB.
Arguments prod_morphism {A1 A2 B1 B2 RA RB}.
Hint Constructors sum_rel.
Hint Constructors prod_rel.

Delimit Scope relationH_scope with relationH.

Module RelNotations.

  (* Declare Scope relationH_scope. *)

  (* Notice the levels: (R ⊕ S ⊗ T ∘ U) is parsed as ((R ⊕ (S ⊗ T)) ∘ U) *)
  Infix "∘" := compose (at level 40, left associativity) : relationH_scope.
  Infix "⊕" := sum_rel (at level 39, left associativity) : relationH_scope.
  Infix "⊗" := prod_rel (at level 38, left associativity) : relationH_scope.

  Infix "⊑" := subrelationH (at level 90, no associativity) : relationH_scope.
  Notation "† R" := (transpose R) (at level 5) : relationH_scope.

  Infix "≡" := eq_rel (at level 89, no associativity) : relationH_scope.

End RelNotations.

Import RelNotations.
Local Open Scope relationH_scope.

Section SubRelationH.

  Global Instance subrelationH_refl {A B: Type} (R: relationH A B): R ⊑ R.
  Proof.
    intros!; auto.
  Qed.

  (* TODO: Instances for directed rewriting by [subrelationH] *)
  Global Instance subrelationH_sum
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
    : R ⊕ S ⊑ R' ⊕ S'.
  Proof.
    intros!; invn sum_rel; constructor; appn subrelationH; auto.
  Qed.

  Global Instance subrelationH_prod
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
    : R ⊗ S ⊑ R' ⊗ S'.
  Proof.
    intros!; invn prod_rel; constructor; appn subrelationH; auto.
  Qed.

  Global Instance subrelationH_transpose
         {A B: Type} (R S: relationH A B) `{R ⊑ S}
    : †R ⊑ †S.
  Proof.
    unfold transpose; intros!; appn subrelationH; auto.
  Qed.

End SubRelationH.

Section ProdRelInstances.
  Context {R S : Type}.
  Context (RR : R -> R -> Prop).
  Context (SS : S -> S -> Prop).

  Global Instance prod_rel_refl `{Reflexive _ RR} `{Reflexive _ SS} : Reflexive (prod_rel RR SS).
  Proof.
    red. destruct x. constructor; auto.
  Qed.

  Global Instance prod_rel_sym `{Symmetric _ RR} `{Symmetric _ SS}  : Symmetric (prod_rel RR SS).
  Proof.
    red. intros.
    inversion H1. subst.
    constructor; symmetry; auto.
  Qed.

  Global Instance prod_rel_trans `{Transitive _ RR} `{Transitive _ SS}  : Transitive (prod_rel RR SS).
  Proof.
    red.
    intros.
    inversion H1.
    inversion H2.
    subst.
    inversion H9; subst.
    constructor; etransitivity; eauto.
  Qed.

  Global Instance prod_rel_eqv `{Equivalence _ RR} `{Equivalence _ SS} : Equivalence (prod_rel RR SS).
  Proof.
    constructor; typeclasses eauto.
  Qed.

End ProdRelInstances.



(* SAZ: There is probably a nice way to typeclassify the eq_rel proofs *)
Section RelationH_Classes.

  (* The names are picked to line up with the categorical names we will have later, where composition is the other way around *)
  Lemma eq_id_r: forall {A B} (R : relationH A B),
    eq ∘ R ≡ R.
  Proof.
    split; intros!.
    - invn compose; invn and; subst; auto.
    - exists y; auto.
  Qed.

  Lemma eq_id_l: forall {A B} (R : relationH A B),
      R ∘ eq ≡ R.
  Proof.
    split; intros!.
    - invn compose; invn and; subst; auto.
    - exists x; auto.
  Qed.

  Lemma eq_rel_prod_eq : forall A B, eq_rel (prod_rel eq eq) (eq : relationH (A * B) (A * B)).
  Proof.
    intros.
    unfold eq_rel; split; unfold subrelationH; intros.
    - inversion H; subst. reflexivity.
    - destruct x; destruct y; inversion H; subst; constructor; reflexivity.
  Qed.

  Global Instance eq_rel_Reflexive {A B} : Reflexive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  Global Instance eq_rel_Symmetric {A B} : Symmetric (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  Global Instance eq_rel_Transitive {A B} : Transitive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. intros.
    destruct H, H0. split; eauto.
  Qed.

  Global Instance eq_rel_Equiv {A B} : Equivalence (@eq_rel A B).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
  Proof.
    repeat red; unfold eq_rel, subrelationH; split; intros;
      destruct H, H0, H1; split; eauto.
  Qed.


  (* SAZ: Unfortunately adding these typeclass instances can cause typeclass resolution
   to loop when looking for a reflexive instance.
   e.t. in InterpFacts we get a loop.

   *)
  Global Instance transpose_Reflexive {A} (R : relationH A A) {RR: Reflexive R} : Reflexive † R | 100.
  Proof.
    red. intros x. unfold transpose. reflexivity.
  Qed.

  Global Instance transpose_Symmetric {A} (R : relationH A A) {RS: Symmetric R} : Symmetric † R | 100.
  Proof.
    red; intros x; unfold transpose; intros. symmetry. assumption.
  Qed.

  Global Instance transpose_Transitive {A} (R : relationH A A) {RT : Transitive R} : Transitive † R | 100.
  Proof.
    red; intros x; unfold transpose; intros. etransitivity; eauto.
  Qed.


  (* This instance allows to rewrite [H: R ≡ S] in a goal of the form [R x y] *)
  Global Instance eq_rel_rewrite {A B}: subrelationH eq_rel (pointwise_relation A (pointwise_relation B iff)).
  Proof.
    intros!; destructn @eq_rel; split; intro; appn subrelationH; auto.
  Qed.

  Lemma transpose_compose {A B C : Type}
        (R : relationH A B) (S : relationH B C)
    : † (S ∘ R) ≡ (†R ∘ †S).
  Proof.
    split; unfold transpose; cbn; intros!;
                                        invn compose; invn and; eexists; eauto.
  Qed.

  Lemma transpose_sym {A : Type} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; symmetry; auto.
  Qed.


End RelationH_Classes.

Section SumRelInstances.
  Context {A B : Type}.
  Context (R : relationH A A).
  Context (S : relationH B B).

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
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
  : (S ∘ R) ⊕ (U ∘ T) ≡ (S ⊕ U) ∘ (R ⊕ T).
  Proof.
    split; intros!.
    - invn sum_rel; invn compose; invn and.
      all: eexists; split; econstructor; eauto.
    - invn compose; invn and; do 2 invn sum_rel.
      eauto.
      all: econstructor; eexists; eauto.
  Qed.

  Lemma transpose_sum {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊕ R) ≡ (†S ⊕ †R).
  Proof.
    split; unfold transpose; cbn; intros!; invn sum_rel; auto.
  Qed.

  (* What's the right way to avoid having to refer to H here? *)
  Global Instance Proper_sum_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@sum_rel A B C D).
  Proof.
    intros!; split; intros!; invn sum_rel; econstructor; (apply H || apply H0); auto.
  Qed.


End SumRelProps.

Section ProdRelProps.

  Lemma prod_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
  : (S ∘ R) ⊗ (U ∘ T) ≡ (S ⊗ U) ∘ (R ⊗ T).
  Proof.
    split; intros!.
    - invn prod_rel; invn compose; invn and.
      inversion H0. destruct H.
      all: eexists; split; econstructor; eauto.
    - invn compose; invn and; do 2 invn prod_rel.
      eauto.
      all: econstructor; eexists; eauto.
  Qed.

  Lemma transpose_prod {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊗ R) ≡ (†S ⊗ †R).
  Proof.
    split; unfold transpose; cbn; intros!; invn prod_rel; auto.
  Qed.

  (* What's the right way to avoid having to refer to H here? *)
  Global Instance Proper_prod_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@prod_rel A B C D).
  Proof.
    intros!; split; intros!; invn prod_rel; econstructor; (apply H || apply H0); auto.
  Qed.

End ProdRelProps.

(* Section RelationH_Category. *)

(*   Section Operations. *)

(*     Global Instance Eq2_rel : Eq2 relationH := @eq_rel. *)

(*     Global Instance Cat_rel : Cat relationH := fun _ _ _ f g => compose g f. *)

(*     Global Instance Id_rel : Id_ relationH := @eq. *)

(*     Global Instance Initial_rel : Initial relationH void := *)
(*       fun _ v => match v : void with end. *)

(*     (* I'm not sure how we would actually want to work with these *)
(*        since we have two instances of [Bimap], ⊕ and ⊗, that we actually use. *)
(*        Additionally of course we have the two that are derived from *)
(*        the respective product and coproduct, which should be provably *)
(*        isomorphic to respectively ⊗ and ⊕. *)
(*      *) *)
(*     Global Instance Bimap_sum_rel : Bimap relationH sum := *)
(*       fun (a b c d : Type) R S => R ⊕ S. *)

(*     Global Instance Bimap_prod_rel : Bimap relationH prod := *)
(*       fun (a b c d : Type) R S => R ⊗ S. *)

(*     Global Instance Case_rel : Case relationH sum := *)
(*       fun _ _ _ l r => case_sum _ _ _ l r. *)

(*     Global Instance Inl_rel : Inl relationH sum := *)
(*       fun A B => fun_rel inl. *)

(*     Global Instance Inr_rel : Inr relationH sum := *)
(*       fun _ _ => fun_rel inr. *)

(*     Global Instance Pair_rel : Pair relationH prod := *)
(*       fun _ _ _ l r c '(a,b) => l c a /\ r c b. *)

(*     Global Instance Fst_rel : Fst relationH prod := *)
(*       fun A B => fun_rel fst. *)

(*     Global Instance Snd_rel : Snd relationH prod := *)
(*       fun _ _ => fun_rel snd. *)

(*   End Operations. *)

(*   Global Instance CatIdL_rel: CatIdL relationH. *)
(*   constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros. *)
(*   - edestruct H as (B' & EQ & R). rewrite <- EQ in R. *)
(*     assumption. *)
(*   - exists x. split. reflexivity. assumption. *)
(*   Qed. *)

(*   Global Instance rel_CatIdR: CatIdR relationH. *)
(*   constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; intros. *)
(*   - edestruct H as (B' & R & EQ). rewrite EQ in R. *)
(*     assumption. *)
(*   - exists y. split. assumption. reflexivity. *)
(*   Qed. *)

(*   Global Instance rel_CatAssoc: CatAssoc relationH. *)
(*   constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; *)
(*     intros A D H. *)
(*   - edestruct H as (C & (B & Rf & Rg) & Rh); clear H. *)
(*     exists B. split; [assumption | ]. *)
(*     exists C. split; assumption. *)
(*   - edestruct H as (B & Rf & (C & Rg & Rh)); clear H. *)
(*     exists C. split; [ | assumption]. *)
(*     exists B; split; assumption. *)
(*   Qed. *)

(*   Global Instance rel_ProperCat: forall a b c, *)
(*       @Proper (relationH a b -> relationH b c -> relationH a c) *)
(*               (eq2 ==> eq2 ==> eq2) cat. *)
(*   intros a b c. *)
(*   constructor; unfold subrelationH, cat, id_, Cat_rel, Id_rel, compose; *)
(*     intros A C He. *)
(*   - edestruct He as (B & Hx & Hx0). *)
(*     unfold eq2, Eq2_rel, eq_rel, subrelationH in *. *)
(*     destruct H, H0. *)
(*     exists B. split. specialize (H A B Hx). assumption. *)
(*     specialize (H0 _ _ Hx0). assumption. *)
(*   - edestruct He as (B & Hy & Hy0). *)
(*     unfold eq2, Eq2_rel, eq_rel, subrelationH in *. *)
(*     destruct H, H0. *)
(*     exists B. split. specialize (H1 _ _ Hy). assumption. *)
(*     specialize (H2 _ _ Hy0). assumption. *)
(*   Qed. *)


(*   Global Instance rel_Category : Category relationH := *)
(*     {| *)
(*     category_cat_id_l := CatIdL_rel; *)
(*     category_cat_id_r := rel_CatIdR; *)
(*     category_cat_assoc := rel_CatAssoc; *)
(*     category_proper_cat := rel_ProperCat *)
(*     |}. *)

(* End RelationH_Category. *)
