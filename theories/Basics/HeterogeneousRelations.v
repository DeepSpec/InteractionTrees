From Coq Require Import
     Morphisms
     Setoid
     Relation_Definitions
     RelationClasses
.

From ITree Require Import Basics.Utils Indexed.Sum.

Set Warnings "-future-coercion-class-field".

(* Heterogeneous relation definition, modified from
   https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)
(* A categorical account of this file is given in [CategoryRelation.v] *)

#[global] Tactic Notation "intros !" := repeat intro.

Definition relationH (A B : Type) := A -> B -> Prop.

Section RelationH_Operations.

  Definition rel_compose {A B C} (S : relationH B C) (R : relationH A B): relationH A C :=
    fun x y => exists b, R x b /\ S b y.

  (** ** Relations for morphisms/parametricity *)

  (* Heterogeneous notion of [subrelation] *)
  Definition subrelationH {A B} (R S : relationH A B) : Prop :=
    forall (x : A) (y : B), R x y -> S x y.

  Definition eq_rel {A B} (R S : relationH A B) :=
      subrelationH R S /\ subrelationH S R.

  Definition transpose {A B: Type} (R: relationH A B): relationH B A :=
    fun x y => R y x.

  (* The graph of a function forms a relation *)
  Definition fun_rel {A B: Type} (f: A -> B): relationH A B :=
    fun x y => y = f x.

  (** ** Relations for morphisms/parametricity *)

  (** Logical relation for the [sum] type. *)
  Variant sum_rel {A1 A2 B1 B2 : Type}
      (RA : relationH A1 A2) (RB : relationH B1 B2)
  : relationH (A1 + B1) (A2 + B2) :=
  | inl_morphism a1 a2 : RA a1 a2 -> sum_rel RA RB (inl a1) (inl a2)
  | inr_morphism b1 b2 : RB b1 b2 -> sum_rel RA RB (inr b1) (inr b2).

  (** Logical relation for the [prod] type. *)
  Record prod_rel {A1 A2 B1 B2 : Type}
      (RA : relationH A1 A2) (RB : relationH B1 B2)
      (p1 : A1 * B1) (p2 : A2 * B2) : Prop := prod_morphism
  { fst_rel : RA (fst p1) (fst p2)
  ; snd_rel : RB (snd p1) (snd p2) }.

End RelationH_Operations.

#[global] Hint Constructors prod_rel: core.
#[global] Hint Constructors sum_rel: core.

Arguments inl_morphism {A1 A2 B1 B2 RA RB}.
Arguments inr_morphism {A1 A2 B1 B2 RA RB}.
Arguments fst_rel {A1 A2 B1 B2 RA RB}.
Arguments snd_rel {A1 A2 B1 B2 RA RB}.

Arguments rel_compose [A B C] S R.
Arguments subrelationH [A B] R S.
Arguments transpose [A B] R.
Arguments sum_rel [A1 A2 B1 B2] RA RB.
Arguments prod_rel [A1 A2 B1 B2] RA RB.

Declare Scope relationH_scope.
Delimit Scope relationH_scope with relationH.

Module RelNotations.

  (* Notice the levels: (R ⊕ S ⊗ T ∘ U) is parsed as ((R ⊕ (S ⊗ T)) ∘ U) *)
  Infix "∘" := rel_compose (at level 40, left associativity) : relationH_scope.
  Infix "⊕" := sum_rel (at level 39, left associativity) : relationH_scope.
  Infix "⊗" := prod_rel (at level 38, left associativity) : relationH_scope.

  Infix "⊑" := subrelationH (at level 70, no associativity) : relationH_scope.
  Notation "† R" := (transpose R) (at level 5, right associativity) : relationH_scope.

  Infix "≡" := eq_rel (at level 70, no associativity) : relationH_scope.

End RelNotations.

Import RelNotations.
#[local] Open Scope relationH_scope.

Definition relationH_of_Type (A : Type) : relationH A A :=
  fun x y => x = y.

#[global]
Instance Proper_relation {A: Type} (R : relationH A A) :
  Proper (@eq A ==> @eq A ==> iff) R.
Proof.
  repeat intro.
  repeat red.
  split; intros.
  - rewrite <- H,<- H0. auto.
  - rewrite H, H0. auto.
Qed.


(* Properties of Heterogeneous Relations ************************************ *)

Class ReflexiveH {A: Type} (R : relationH A A) : Prop :=
  reflexive : forall (a:A), R a a.

Class SymmetricH {A: Type} (R : relationH A A) : Prop :=
  symmetric : forall x y, R x y -> R y x.

Class TransitiveH {A: Type} (R : relationH A A) : Prop :=
  transitive : forall x y z, R x y -> R y z -> R x z.

Class PER {A : Type} (R : relationH A A) : Prop :=
  {
    per_symm : SymmetricH R;
    per_trans : TransitiveH R
  }.
#[global] Existing Instance per_symm.
#[global] Existing Instance per_trans.

Class Preorder {A : Type} (R : relationH A A) : Prop :=
  {
    pre_refl : ReflexiveH R;
    pre_trans : TransitiveH R
  }.
#[global] Existing Instance pre_refl.
#[global] Existing Instance pre_trans.

Class EquivalenceH {A : Type} (R : relationH A A) : Prop :=
  {
    equiv_refl : ReflexiveH R;
    equiv_symm : SymmetricH R;
    equiv_trans : TransitiveH R
  }.
#[global] Existing Instance equiv_refl.
#[global] Existing Instance equiv_symm.
#[global] Existing Instance equiv_trans.

#[global]
Instance relationH_reflexive : forall (A:Type), ReflexiveH (@eq A).
Proof.
  repeat intro.
  reflexivity.
Defined.

#[global]
Instance relationH_symmetric : forall (A:Type), SymmetricH (@eq A).
Proof.
  repeat intro. cbn; auto.
Defined.

#[global]
Instance relationH_transitive : forall (A:Type), TransitiveH (@eq A).
Proof.
  repeat intro. cbn in *. etransitivity.
  apply H. apply H0.
Defined.

#[global]
Instance relationH_PER {A : Type} : PER (@eq A).
Proof.
  constructor; typeclasses eauto.
Defined.

#[global]
Instance relationH_Preorder {A : Type} : Preorder (@eq A).
Proof.
  constructor; typeclasses eauto.
Defined.

#[global]
Instance relationH_Equiv {A : Type} : EquivalenceH (@eq A).
Proof.
  constructor; typeclasses eauto.
Defined.

Lemma ReflexiveH_Reflexive {A: Type} (R : relationH A A) :
  ReflexiveH R <-> Reflexive R.
Proof.
  split; intros.
  - red. apply H.
  - apply H.
Qed.

Lemma SymmetricH_Symmetric {A: Type} (R : relationH A A) :
  SymmetricH R <-> Symmetric R.
Proof.
  split; intros.
  - red. unfold SymmetricH in H. intros. specialize (H x y). cbn in H.
    apply H. assumption.
  - red. intros p HP. cbn in *. apply H.
Qed.

Lemma TransitiveH_Transitive {A: Type} (R : relationH A A) :
  TransitiveH R <-> Transitive R.
Proof.
  split; intros.
  - red. intros x y z H0 H1. unfold TransitiveH in H. eapply H; eauto.
  - red. intros p q HP HQ EQ.
    unfold Transitive in H. cbn in EQ.
    eapply H; eauto.
Qed.


(** ** subrelationH *)
Section SubRelationH.

  (* YZ TODO: Study how [subrelation] is manipulated. Notably:
     * Relevance of using [flip] exactly, and how it relates to us using [transpose]
     * Definition of [relation_equivalence] in terms of [predicate_equivalence]
   *)
  Lemma subrelationH_Reflexive {A B: Type} (R: relationH A B): R ⊑ R.
  Proof.
    intros!; auto.
  Qed.

  Lemma subrelationH_antisym {A B: Type} (R S: relationH A B) `{R ⊑ S} `{S ⊑ R}: R ≡ S.
  Proof.
    split; auto.
  Qed.

  Lemma subrelationH_trans {A B: Type} (R S T: relationH A B)
         `{R ⊑ S} `{S ⊑ T} : R ⊑ T.
  Proof.
    intros!; auto.
  Qed.

  Lemma subrelationH_refl_eq {A: Type} (R: relationH A A) (H : Reflexive R) : @eq A ⊑ R.
  Proof.
    intros!.
    rewrite H0. cbn. apply H.
  Qed.


End SubRelationH.

Section RelationEqRel.

  (* [eq_rel] is an equivalence relation *)
  #[global]
  Instance eq_rel_Reflexive {A B} : Reflexive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  #[global]
  Instance eq_rel_Symmetric {A B} : Symmetric (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  #[global]
  Instance eq_rel_Transitive {A B} : Transitive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. intros.
    destruct H, H0. split; eauto.
  Qed.

  #[global]
  Instance eq_rel_Equiv {A B} : Equivalence (@eq_rel A B).
  Proof.
    split; typeclasses eauto.
  Qed.

  (* YZ: I believe that this instance is redundant with the [Transitive] instance, as illustrated by its proof *)
  #[global]
  Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
  Proof.
    intros ? ? EQ1 ? ? EQ2.
    rewrite EQ1,EQ2; reflexivity.
  Qed.

  (* This instance should allow to rewrite [H: R ≡ S] in a goal of the form [R x y] *)
  (* It works in simple contxets, however, it fails weirdly quickly. See:
     https://github.com/coq/coq/issues/12141
   *)

  (* Global Instance eq_rel_rewrite {A B}: subrelationH eq_rel (pointwise_relation A (pointwise_relation B iff)). *)
  (* Proof. *)
  (*   intros!; destructn eq_rel; split; intro; appn subrelationH; auto. *)
  (* Qed. *)
End RelationEqRel.

Section RelationCompose.

  (* [eq] define identities *)
  Lemma eq_id_r: forall {A B : Type} (R : relationH A B),
    ((@eq B) ∘ R) ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & HR & EQ).
      rewrite <- EQ. assumption.
    - cbn. exists y. split; auto.
  Qed.

  Lemma eq_id_l: forall {A B} (R : relationH A B),
      R ∘ (@eq A) ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & EQ & HR).
      rewrite EQ. assumption.
    - cbn. exists x. split; auto.
  Qed.

  (* Composition is associative *)

  Lemma compose_assoc: forall {A B C D} (R : relationH A B) (S : relationH B C) (T : relationH C D),
      T ∘ S ∘ R ≡ (T ∘ S) ∘ R.
  Proof.
    split; intros!; cbn in *.
    - repeat destruct H. repeat destruct H0.
      repeat (eexists; split; eauto).
    - repeat destruct H. repeat destruct H0.
      repeat (eexists; split; eauto).
  Qed.


  #[global]
  Instance Proper_compose: forall A B C,
      Proper
        (* (relationH B C -> relationH A B -> relationH A C) *)
        (eq_rel ==> eq_rel ==> eq_rel) (@rel_compose A B C).
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
  (* YZ: Would it be worth to Typeeclass this property? *)
  Instance transpose_Reflexive {A} (R : relationH A A) {RR: Reflexive R} : Reflexive † R | 100.
  Proof.
    red. intros x. apply RR.
  Qed.

  Instance transpose_Symmetric {A} (R : relationH A A) {RS: Symmetric R} : Symmetric † R | 100.
  Proof.
    red; intros x; unfold transpose; intros. apply SymmetricH_Symmetric in RS.
    apply RS. assumption.
  Qed.

  Instance transpose_Transitive {A} (R : relationH A A) {RT : Transitive R} : Transitive † R | 100.
  Proof.
    red; intros x; unfold transpose; intros.
    apply TransitiveH_Transitive in RT.
    unfold TransitiveH in RT.
    (* destruct A. cbn in *. destruct R. cbn in *. *)
    specialize (RT z y x). apply RT; eauto.
  Qed.

  (* [transpose] is closed on equivalence relations *)

  (* [transpose] is a functor (from the opposite category into itself) *)

  Lemma transpose_eq {A: Type}
    : † (@eq A) ≡ (@eq A).
  Proof.
    split; unfold transpose; intros!; subst; auto.
  Qed.

  Lemma transpose_sym {A : Type} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; cbn in *.
    apply SymmetricH_Symmetric in RS. red in RS.
    apply (RS y x). assumption.
    apply SymmetricH_Symmetric in RS. red in RS.
    apply (RS x y). assumption.
  Qed.

  Lemma transpose_compose {A B C : Type}
        (R : relationH A B) (S : relationH B C)
    : † (S ∘ R) ≡ (†R ∘ †S).
  Proof.
    split; unfold transpose; cbn; intros!; cbn in *.
    - destruct H as (b & HR & HS). exists b. tauto.
    - destruct H as (b & HR & HS). exists b. tauto.
  Qed.

  #[global]
  Instance Proper_transpose {A B : Type}
    : Proper (eq_rel ==> eq_rel) (@transpose A B).
  Proof.
    intros ? ? EQ; split; unfold transpose; intros!; apply EQ; auto.
  Qed.

  (*    [transpose] is a functor *)

  (* [transpose] is an involution *)
  Lemma transpose_involution : forall {A B} (R : relationH A B),
      † † R ≡ R.
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

  #[global]
  Instance transpose_Proper :forall A B, Proper (@eq_rel A B ==> eq_rel) (@transpose A B).
  Proof.
    intros A B R1 R2 (Hab & Hba).
    split.
    - apply transpose_inclusion in Hab. assumption.
    - apply transpose_inclusion in Hba. assumption.
  Qed.

  (* [transpose] is the identity over symmetric relations *)
  Lemma transpose_sym_eq_rel {A} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; cbn in *.
    - apply SymmetricH_Symmetric in RS. unfold SymmetricH in RS. apply (RS y x). assumption.
    - apply SymmetricH_Symmetric in RS. unfold SymmetricH in RS. apply (RS x y). assumption.
  Qed.

  (* [transpose] is monotone *)
  Lemma transpose_monotone
         {A B} (R S: relationH A B) `{R ⊑ S}
    : †R ⊑ †S.
  Proof.
    unfold transpose; intros!.
    apply H. auto.
  Qed.

End TransposeFacts.

Section ProdRelFacts.


  (* [prod_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {R S : Type}.
    Context (RR : relationH R R).
    Context (SS : relationH S S).

    #[global]
    Instance prod_rel_refl `{Reflexive _ RR} `{Reflexive _ SS} : Reflexive (RR ⊗ SS).
    Proof.
      intros []. apply ReflexiveH_Reflexive in H. apply ReflexiveH_Reflexive in H0.
      cbn. split. apply H. apply H0.
    Qed.

    #[global]
    Instance prod_rel_sym `{Symmetric _ RR} `{Symmetric _ SS}  : Symmetric (RR ⊗ SS).
    Proof.
      intros ? ? ?. apply SymmetricH_Symmetric in H. apply SymmetricH_Symmetric in H0.
      destruct x; destruct y; cbn in *. destruct H1. split.
      - unfold SymmetricH in H. apply H. auto.
      - unfold SymmetricH in H0. apply H0. auto.
    Qed.

    #[global]
    Instance prod_rel_trans `{Transitive _ RR} `{Transitive _ SS}  : Transitive (RR ⊗ SS).
    Proof.
      intros!.
      apply TransitiveH_Transitive in H. apply TransitiveH_Transitive in H0.
      unfold TransitiveH in *.
      inversion H1; inversion H2; subst; eauto; inversion H9; subst.
    Qed.

    #[global]
    Instance prod_rel_eqv `{Equivalence _ RR} `{Equivalence _ SS} : Equivalence (RR ⊗ SS).
    Proof.
      constructor; typeclasses eauto.
    Qed.

    #[global]
    Instance prod_rel_PER `{PER _ RR} `{PER _ SS} : @PER _ (RR ⊗ SS).
    Proof.
      constructor.
      - destruct H, H0.
        eapply SymmetricH_Symmetric.
        eapply @prod_rel_sym; [ eapply SymmetricH_Symmetric; eauto .. | ].
        eapply SymmetricH_Symmetric; eauto.
      - eapply TransitiveH_Transitive.
        eapply @prod_rel_trans.
        + destruct H, H0.
          eapply TransitiveH_Transitive; eauto.
        + destruct H, H0.
          eapply TransitiveH_Transitive; eauto.
    Qed.

  End Equivalence.

  (* [prod_rel] is monotone in both parameters *)
  Lemma prod_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
  : R ⊗ S ⊑ R' ⊗ S'.
  Proof.
    intros!. destruct x, y. repeat red. repeat red in H1. destruct H1.
    split.
    - apply H. assumption.
    - apply H0. assumption.
  Qed.

  (* begin *)
(*    [prod_rel] is a bifunctor *)
(*    *)

  Lemma prod_rel_eq : forall (A B:Type),  (@eq A) ⊗ (@eq B) ≡ @eq (A * B).
  Proof.
    intros.
    unfold eq_rel; split; unfold subrelationH; intros.
    - destruct x, y. repeat red in H. destruct H. cbn in *; subst; reflexivity.
    - destruct x; destruct y. cbn in H. repeat red. inversion H. split; reflexivity.
  Qed.

  Definition prod_fst_rel {A B : Type} (R : relationH (A * B) (A * B)) :
    relationH A A :=
    fun x y => forall (b1 b2 : B), R  (x, b1) (y, b2).

  Definition prod_snd_rel {A B : Type} (R : relationH (A * B) (A * B)) :
    relationH B B :=
    fun x y => forall (a1 a2 : A), R  (a1, x) (a2, y).

  Lemma prod_inv (A B : Type) :
    forall (R : relationH (A * B) (A * B)) (x1 x2 : A) (y1 y2 : B),
        prod_fst_rel R x1 x2 /\ prod_snd_rel R y1 y2 ->
        R (x1, y1) (x2, y2).
  Proof.
    intros.
    destruct H. unfold prod_fst_rel, prod_snd_rel in *. cbn in *.
    apply H0.
  Qed.

  Lemma prod_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
    : (S ∘ R) ⊗ (U ∘ T) ≡ (S ⊗ U) ∘ (R ⊗ T).
  Proof.
    split; intros!.
    - destruct x, y. repeat red. repeat red in H. destruct H as [H1 H2].
      unfold fst, snd. cbn in H1, H2.
      edestruct H1 as (b & HR & HS).
      edestruct H2 as (e & HT & HU).
      exists (b, e). split; cbn; split; eauto.
    - destruct x, y. repeat red. repeat red in H. destruct H as [x [H1 H2]].
      split.
      + exists (fst x). cbn; split; [apply H1|apply H2].
      + exists (snd x). cbn; split; [apply H1|apply H2].
  Qed.

  #[global]
  Instance Proper_prod_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@prod_rel A B C D).
  Proof.
    intros!. split; intros!; destruct x1, y1; cbn in *; destruct H1; split;
    try apply H; try apply H0; eauto.
  Qed.

  (* end *)
(*    [prod_rel] is a bifunctor *)

(* Note: we also have associators and unitors, forming a monoidal category. *)
(*      See [CategoryRelation.v] if needed. *)

  (* Distributivity of [transpose] over [prod_rel] *)
  Lemma transpose_prod {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊗ R) ≡ (†S ⊗ †R).
  Proof.
    split; unfold transpose; cbn; intros!; destruct x, y; cbn in *;
    destruct H; split; eauto.
  Qed.
End ProdRelFacts.


Section SumRelFacts.

  (* [sum_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {A B : Type}.
    Context (R : relationH A A).
    Context (S : relationH B B).

    #[global]
    Instance sum_rel_refl {RR: Reflexive R} {SR: Reflexive S} : Reflexive (R ⊕ S).
    Proof.
      intros []. apply ReflexiveH_Reflexive in RR.
      apply ReflexiveH_Reflexive in SR.
      cbn.
      constructor. apply RR.
      constructor. apply SR.
    Qed.

    #[global]
    Instance sum_rel_sym {RS: Symmetric R} {SS: Symmetric S} : Symmetric (R ⊕ S).
    Proof.
      intros ? ? ?. apply SymmetricH_Symmetric in RS.
      apply SymmetricH_Symmetric in SS.
      destruct x, y.
      - constructor. inversion H. subst. apply RS. auto.
      - inversion H.
      - inversion H.
      - constructor. inversion H. subst. apply SS. auto.
    Qed.

    #[global]
    Instance sum_rel_trans {RT: Transitive R} {ST: Transitive S}  : Transitive (R ⊕ S).
    Proof.
      intros!.
      apply TransitiveH_Transitive in RT. apply TransitiveH_Transitive in ST.
      unfold TransitiveH in *.
      destruct x, y, z; try contradiction; inversion H; inversion H0; subst.
      cbn in *.
      constructor. eauto. constructor. eauto.
    Qed.

    #[global]
    Instance sum_rel_eqv {RE: Equivalence R} {SE: Equivalence S} : Equivalence (R ⊕ S).
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End Equivalence.

  (* [sum_rel] is monotone in both parameters *)
  Lemma sum_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
    : R ⊕ S ⊑ R' ⊕ S'.
  Proof.
    intros!; destruct x, y; repeat red; repeat red in H1;
    inversion H1; subst; constructor; eauto.
  Qed.

(*    [sum_rel] is a bifunctor *)

  Lemma sum_rel_eq : forall (A B: Type),  @eq A ⊕ @eq B ≡ @eq (A + B).
  Proof.
    intros. red.
    split; repeat intro; eauto.
    inversion H; subst; auto; try reflexivity.
    subst. destruct y; constructor; eauto.
  Qed.

  Lemma sum_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
  : (S ∘ R) ⊕ (U ∘ T) ≡ (S ⊕ U) ∘ (R ⊕ T).
  Proof.
    split; intros!.
    - destruct x, y; inv H.
      destruct H2 as (? & ? & ?); eexists; eauto.
      destruct H2 as (? & ? & ?); eexists; eauto.
    - destruct H as (? & H1 & H2); inv H1; inv H2.
      econstructor; eexists; eauto.
      econstructor; eexists; eauto.
  Qed.

  #[global]
  Instance Proper_sum_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@sum_rel A B C D).
  Proof.
    intros!.
    split; intros!; destruct x1, y1; cbn in *; try inversion H1;
      try apply H; try apply H0; eauto; subst; inversion H1; subst;
        try econstructor; try apply H; try apply H0; eauto.
  Qed.

(*    [sum_rel] is a bifunctor *)

(* Note: we also have associators and unitors, forming a monoidal category. *)
(*      See [CategoryRelation.v] if needed. *)
(*  *)

  (* Distributivity of [transpose] over [sum_rel] *)
  Lemma transpose_sum {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊕ R) ≡ (†S ⊕ †R).
  Proof.
    split; unfold transpose; cbn; intros!; destruct x, y; cbn in *;
      try inversion H; eauto; subst; inversion H; subst; try econstructor; eauto.
  Qed.

End SumRelFacts.

Lemma PER_reflexivityH1 : forall {A:Type} (R : relationH A A) (RS: SymmetricH R) (RT: TransitiveH R)
                            (a b : A), R  a b -> R a a.
Proof.
  intros.
  assert (R  b a). { specialize (RS a b). apply RS. assumption. }
  specialize (RT a b a). apply RT; auto.
Qed.

Lemma PER_reflexivityH2 : forall {A:Type} (R : relationH A A) (RS: SymmetricH R) (RT: TransitiveH R)
                            (a b : A), R  b a -> R a a.
Proof.
  intros.
  assert (R a b). { specialize (RS b a). apply RS. assumption. }
  specialize (RT a b a). apply RT; auto.
Qed.

Ltac PER_reflexivityH :=
  match goal with
  | [ H : ?R  ?X ?Y |- ?R  ?X ?X ] =>  eapply PER_reflexivityH1; eauto
  | [ H : ?R  ?Y ?X |- ?R  ?X ?X ] =>  eapply PER_reflexivityH2; eauto
  end; try apply per_symm ; try apply per_trans.


Definition diagonal_prop {A : Type} (P : A -> Prop) : relationH A A :=
  fun x y => (P  x /\ P y).

Lemma diagonal_prop_SymmetricH {A : Type} (P : A -> Prop) : SymmetricH (diagonal_prop P).
Proof.
  red. intros a1 a2 H.
  cbn in *. unfold diagonal_prop in *. tauto.
Qed.

Lemma diagonal_prop_TransitiveH {A : Type} (P : A -> Prop) : TransitiveH (diagonal_prop P).
Proof.
  red. intros.
  cbn in *. unfold diagonal_prop in *.
  tauto.
Qed.

Lemma diagonal_prop_PER {A : Type} (P : A -> Prop) : PER (diagonal_prop P).
Proof.
  constructor.
  red. intros.
  cbn in *. unfold diagonal_prop in *; tauto.
  red. intros.
  cbn in *. unfold diagonal_prop in *; tauto.
Qed.

(* With the current state of the monad theory, we cannot prove the laws generically.
   We specialize things to [failT (itree E)] until we generalize [Eq1] to be parameterized
   by the underlying relation on returned values.
 *)
Definition option_rel {X : Type} (R : relation X) : relation (option X) :=
  fun mx my => match mx,my with
            | Some x, Some y => R x y
            | None, None => True
            | _, _ => False
            end.
#[export] Hint Unfold option_rel : core.

Lemma option_rel_eq : forall {A : Type},
    eq_rel (@eq (option A)) (option_rel eq).
Proof.
  intros ?; split; intros [] [] EQ; subst; try inv EQ; cbn; auto.
Qed.

#[export] Hint Unfold option_rel : core.

Notation prerel E D := (forall (A B : Type), E A -> D B -> Prop ).
Notation postrel E D := (forall (A B : Type), E A -> A -> D B -> B -> Prop).

Variant sum_prerel {E1 E2 D1 D2 : Type -> Type} (PR1 : prerel E1 D1 ) (PR2 : prerel E2 D2) 
  : prerel (E1 +' E2) (D1 +' D2) := 
  | sum_prerel_inl (A B : Type) e1 d1 : PR1 A B e1 d1 -> sum_prerel PR1 PR2 A B (inl1 e1) (inl1 d1)
  | sum_prerel_inr (A B : Type) e2 d2 : PR2 A B e2 d2 -> sum_prerel PR1 PR2 A B (inr1 e2) (inr1 d2)
.

Variant sum_postrel  {E1 E2 D1 D2 : Type -> Type} (PR1 : postrel E1 D1 ) (PR2 : postrel E2 D2) 
  : postrel (E1 +' E2) (D1 +' D2) :=
  | sum_postrel_inl A B e1 d1 a b : PR1 A B e1 a d1 b -> sum_postrel PR1 PR2 A B (inl1 e1) a (inl1 d1) b
  | sum_postrel_inr A B e2 d2 a b : PR2 A B e2 a d2 b -> sum_postrel PR1 PR2 A B (inr1 e2) a (inr1 d2) b
.
