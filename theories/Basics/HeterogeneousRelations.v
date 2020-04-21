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
(* A categorical account of this file is given in [CategoryRelation.v] *)

Definition relationH (A B : Type) := A -> B -> Prop.

Section RelationH_Operations.

  Definition compose {A B C} (S : relationH B C) (R : relationH A B): relationH A C :=
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

End RelationH_Operations.

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

(** ** subrelationH *)
Section SubRelationH.

  (* YZ TODO: Study how [subrelation] is manipulated. Notably:
     * Relevance of using [flip] exactly, and how it relates to us using [transpose]
     * Definition of [relation_equivalence] in terms of [predicate_equivalence]
   *)
  (* TODO: Instances for directed rewriting by [subrelationH] *)

  Global Instance subrelationH_Reflexive {A B: Type} (R: relationH A B): R ⊑ R.
  Proof.
    intros!; auto.
  Qed.

  (* TODO: Figure out how all of this should be organized w.r.t. typeclasses.
     Should be an instance of [Preorder eq_rel subrelationH] most likely?
   *)
  Definition subrelationH_antisym {A B: Type} (R S: relationH A B) `{R ⊑ S} `{S ⊑ R}: R ≡ S.
  Proof.
    split; auto.
  Qed.

  Global Instance subrelationH_trans {A B: Type} (R S T: relationH A B)
         `{R ⊑ S} `{S ⊑ T} : R ⊑ T.
  Proof.
    intros!; auto.
  Qed.

  Global Instance subrelationH_refl_eq {A: Type} (R: relationH A A) `{Reflexive _ R}: eq ⊑ R.
  Proof.
    intros!; subst; auto.
  Qed.

End SubRelationH.

Section RelationEqRel.

  (* [eq_rel] is an equivalence relation *)
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

  (* YZ: I believe that this instance is redundant with the [Transitive] instance, as illustrated by its proof *)
  Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
  Proof.
    intros ? ? EQ1 ? ? EQ2.
    rewrite EQ1,EQ2; reflexivity.
  Qed.

  (* This instance should allow to rewrite [H: R ≡ S] in a goal of the form [R x y] *)
  (* It works in simple contxets, however, it fails weirdly quickly. See:
     https://github.com/coq/coq/issues/12141
   *)
  Global Instance eq_rel_rewrite {A B}: subrelationH eq_rel (pointwise_relation A (pointwise_relation B iff)).
  Proof.
    intros!; destructn @eq_rel; split; intro; appn subrelationH; auto.
  Qed.

End RelationEqRel.

Section RelationCompose.

  (* [eq] define identities *)
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

  (* Composition is associative *)

  Lemma compose_assoc: forall {A B C D} (R : relationH A B) (S : relationH B C) (T : relationH C D),
      T ∘ S ∘ R ≡ (T ∘ S) ∘ R.
  Proof.
    split; intros!; repeat (destructn compose || destructn and); repeat (eexists; split; eauto).
  Qed.

  Global Instance Proper_compose: forall A B C,
      @Proper (relationH B C -> relationH A B -> relationH A C)
              (eq_rel ==> eq_rel ==> eq_rel) (@compose A B C).
  Proof.
    intros ? ? ? S S' EQS R R' EQR.
    split; intros ? ? EQ; destruct EQ as (? & ? & ?); econstructor; split; (apply EQR || apply EQS); eauto.
  Qed.

End RelationCompose.

Section TransposeFacts.

  (* SAZ: Unfortunately adding these typeclass instances can cause typeclass resolution
   to loop when looking for a reflexive instance.
   e.t. in InterpFacts we get a loop.

     YZ: If it's indeed too much of a problem, one solution is to not declare them [Global] and use
     [Existing Instance] locally in section where we them.
   *)

  (* begin
     [transpose] is closed on equivalence relations
   *)
  (* YZ: Would it be worth to typeclass this property? *)
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
  (* end
     [transpose] is closed on equivalence relations
   *)

  (* begin
     [transpose] is a functor (from the opposite category into itself)
   *)
  Lemma transpose_eq {A: Type}
    : † (@eq A) ≡ eq.
  Proof.
    split; unfold transpose; intros!; subst; auto.
  Qed.

  Lemma transpose_sym {A : Type} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; symmetry; auto.
  Qed.

  Lemma transpose_compose {A B C : Type}
        (R : relationH A B) (S : relationH B C)
    : † (S ∘ R) ≡ (†R ∘ †S).
  Proof.
    split; unfold transpose; cbn; intros!; invn compose; invn and; eexists; eauto.
  Qed.

  Global Instance Proper_transpose {A B : Type}
    : Proper (eq_rel ==> eq_rel) (@transpose A B).
  Proof.
    intros ? ? EQ; split; unfold transpose; intros!; apply EQ; auto.
  Qed.

  (* end
     [transpose] is a functor
   *)

  (* [transpose] is an involution *)
  (* YZ: Why do we need these parentheses?
     TODO: Fix notation?
   *)
  Lemma transpose_involution : forall {A B} (R : relationH A B),
      († † R) ≡ R.
  Proof.
    intros A B R.
    split.
    - unfold subrelationH. unfold transpose. tauto.
    - unfold subrelationH, transpose. tauto.
  Qed.

  Lemma transpose_inclusion : forall {A B} (R1 : relationH A B) (R2 : relationH A B),
      R1 ⊑ R2 <-> († R1 ⊑ † R2).
  Proof.
    intros A B R1 R2.
    split.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
  Qed.

  Global Instance transpose_Proper :forall A B, Proper (@eq_rel A B ==> eq_rel) (@transpose A B).
  Proof.
    intros A B R1 R2 (Hab & Hba).
    split.
    - apply transpose_inclusion in Hab. assumption.
    - apply transpose_inclusion in Hba. assumption.
  Qed.

  (* [transpose] is the identity over symmetric relations *)
  Lemma transpose_sym_eq_rel {A : Type} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; symmetry; auto.
  Qed.

  (* [transpose] is monotone *)
  Global Instance transpose_monotone
         {A B: Type} (R S: relationH A B) `{R ⊑ S}
    : †R ⊑ †S.
  Proof.
    unfold transpose; intros!; appn subrelationH; auto.
  Qed.

End TransposeFacts.

Section ProdRelFacts.

  (* [prod_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {R S : Type}.
    Context (RR : R -> R -> Prop).
    Context (SS : S -> S -> Prop).

    Global Instance prod_rel_refl `{Reflexive _ RR} `{Reflexive _ SS} : Reflexive (RR ⊗ SS).
    Proof.
      intros []; auto.
    Qed.

    Global Instance prod_rel_sym `{Symmetric _ RR} `{Symmetric _ SS}  : Symmetric (RR ⊗ SS).
    Proof.
      intros ? ? ?; invn prod_rel; auto.
    Qed.

    Global Instance prod_rel_trans `{Transitive _ RR} `{Transitive _ SS}  : Transitive (RR ⊗ SS).
    Proof.
      intros!; do 2 invn prod_rel; eauto.
    Qed.

    Global Instance prod_rel_eqv `{Equivalence _ RR} `{Equivalence _ SS} : Equivalence (RR ⊗ SS).
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End Equivalence.

  (* [prod_rel] is monotone in both parameters *)
  Global Instance prod_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
  : R ⊗ S ⊑ R' ⊗ S'.
  Proof.
    intros!; invn prod_rel; constructor; appn subrelationH; auto.
  Qed.

  (* begin
   [prod_rel] is a bifunctor
   *)

  Lemma prod_rel_eq : forall A B,  eq ⊗ eq ≡ @eq (A * B).
  Proof.
    intros.
    unfold eq_rel; split; unfold subrelationH; intros.
    - inversion H; subst. reflexivity.
    - destruct x; destruct y; inversion H; subst; constructor; reflexivity.
  Qed.

  Lemma prod_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
    : (S ∘ R) ⊗ (U ∘ T) ≡ (S ⊗ U) ∘ (R ⊗ T).
  Proof.
    split; intros!.
    - repeat (invn prod_rel || invn compose || invn and).
      eexists; eauto.
    - repeat (invn prod_rel || invn compose || invn and).
      do 2 eexists; eauto.
  Qed.

  Global Instance Proper_prod_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@prod_rel A B C D).
  Proof.
    intros!; split; intros!; invn prod_rel;
      econstructor; appn @eq_rel; auto.
  Qed.

  (* end
   [prod_rel] is a bifunctor
   *)

(* Note: we also have associators and unitors, forming a monoidal category.
     See [CategoryRelation.v] if needed.
 *)

  (* Distributivity of [transpose] over [prod_rel] *)
  Lemma transpose_prod {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊗ R) ≡ (†S ⊗ †R).
  Proof.
    split; unfold transpose; cbn; intros!; invn prod_rel; auto.
  Qed.

End ProdRelFacts.

Section SumRelFacts.

  (* [sum_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
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

  End Equivalence.

  (* [sum_rel] is monotone in both parameters *)
  Global Instance sum_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
    : R ⊕ S ⊑ R' ⊕ S'.
  Proof.
    intros!; invn sum_rel; constructor; appn subrelationH; auto.
  Qed.

  (* begin
   [sum_rel] is a bifunctor
   *)

  Lemma sum_rel_eq : forall A B,  eq ⊕ eq ≡ @eq (A + B).
  Proof.
    intros.
    split; intros!; [invn sum_rel | destructn sum; subst]; eauto.
  Qed.

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

  Global Instance Proper_sum_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@sum_rel A B C D).
  Proof.
    intros!; split; intros!; invn sum_rel; econstructor; appn @eq_rel; eauto.
  Qed.

  (* end
   [sum_rel] is a bifunctor
   *)

(* Note: we also have associators and unitors, forming a monoidal category.
     See [CategoryRelation.v] if needed.
 *)

  (* Distributivity of [transpose] over [sum_rel] *)
  Lemma transpose_sum {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊕ R) ≡ (†S ⊕ †R).
  Proof.
    split; unfold transpose; cbn; intros!; invn sum_rel; auto.
  Qed.

End SumRelFacts.


