From Coq Require Import
     Morphisms
     Relation_Definitions
     RelationClasses.

From ITree Require Import
     Basics.Tacs
     Basics.Basics
     Basics.Function
     Basics.Typ
     (* Basics.CategoryTheory *)
     (* Basics.CategoryOps *)
.

(* Heterogeneous relation definition, modified from https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html. *)
(* A categorical account of this file is given in [CategoryRelation.v] *)

(* SAZ:
    Note that, morally, we need to work with only relationH functions such that
    A -=-> B -=-> prop_typ
    (A × B -=-> prop_typ)
*)

Open Scope typ_scope.

Definition relationH (A B : typ) := (A × B) -=-> prop_typ.

Section RelationH_Operations.

  Program Definition compose {A B C} (S : relationH B C) (R : relationH A B): relationH A C :=
    fun (p : A × C) => exists b, (R @ (fst p, b)) /\ (S @ (b, (snd p))).
  Next Obligation.
    do 2 red. intros (x1 & y1) (x2 & y2) (HA & HC).
    cbn in *.
    split; intros (b & Rb & Sb).
    - exists b. split.
      rewrite <- HA. assumption.
      rewrite <- HC. assumption.
    - exists b. split.
      rewrite HA. assumption.
      rewrite HC. assumption.
  Qed.
    

  (* Heterogeneous notion of [subrelation] *)
  Class subrelationH {A B} (R S : relationH A B) : Prop :=
    is_subrelationH: forall (x : A) (y : B), R @ (x, y) -> S @ (x, y).

  Definition superrelationH {A B} (R S : relationH A B) : Prop := subrelationH S R.
  
  Definition eq_rel {A B} (R S : relationH A B) :=
    subrelationH R S /\ subrelationH S R.

  Program Definition transpose {A B: typ} (R: relationH A B): relationH B A :=
    fun p => R @ (snd p, fst p).
  Next Obligation.
    do 2 red.
    intros (x1 & y1) (x2 & y2) (HA & HC).
    split; intros.
    - rewrite <- HA. rewrite <- HC.  assumption.
    - rewrite HA. rewrite HC. assumption.
  Qed.

  (* The graph of a function forms a relation *)
  Program Definition fun_rel {A B: typ} (f: A -=-> B): relationH A B :=
    fun p => (snd p) == f @ (fst p).
  Next Obligation.
    do 2 red.
    intros (x1 & y1) (x2 & y2) (HA & HC).
    split; intros.
    - rewrite <- HA. rewrite <- HC.  assumption.
    - rewrite HA. rewrite HC. assumption.
  Qed.

  (** ** Relations for morphisms/parametricity *)

  (** Logical relation for the [sum] type. *)
  Program Definition sum_rel {A1 A2 B1 B2 : typ}
          (RA : relationH A1 A2) (RB : relationH B1 B2)
    : relationH (A1 ⨥ B1) (A2 ⨥ B2) :=
    fun p =>
      match pair (fst p) (snd p) with
      | pair (inl x) (inl y) => RA (x, y)
      | pair (inr x) (inr y) => RB (x, y)
      | pair _ _ => False
      end.
  Next Obligation.
    split; intros.
    - intro. inversion H1.
    - intro. inversion H1.
  Qed.
  Next Obligation.
    split; intros.
    - intro. inversion H1.
    - intro. inversion H1.
  Qed.
  Next Obligation.
    do 2 red.
    intros (x1 & x2) (y1 & y2); destruct x1; destruct x2; destruct y1; destruct y2; cbn in *; intros; try tauto.
    - destruct H. destruct RA. cbn. rewrite H. rewrite H0. reflexivity.
    - destruct H. destruct RB. cbn. rewrite H. rewrite H0. reflexivity.
  Qed.      
    

  (** Logical relation for the [prod] type. *)
  Program Definition prod_rel {A1 A2 B1 B2 : typ}
          (RA : relationH A1 A2) (RB : relationH B1 B2)
    : relationH (A1 × B1) (A2 × B2) :=
    fun p => match pair (fst p) (snd p) with
          | pair (pair x1 y1) (pair x2 y2) => RA @ (x1, x2) /\ RB @ (y1, y2)
          end.
  Next Obligation.
    do 2 red.
    intros ((a11 & b11) & (a12 & b12))  ((a21 & b21) & (a22 & b22)).
    cbn. intros ((HA1 & HB1) & (HA2 & HB2)).
    split; intros.
    - rewrite <- HA1. rewrite <- HA2. rewrite <- HB1. rewrite <- HB2. assumption.
    - rewrite HA1. rewrite HA2. rewrite HB1. rewrite  HB2. assumption.
  Qed.
    

End RelationH_Operations.

Arguments compose [A B C] S R.
Arguments subrelationH [A B] R S.
Arguments transpose [A B] R.
Arguments sum_rel [A1 A2 B1 B2] RA RB.
Arguments prod_rel [A1 A2 B1 B2] RA RB.

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


(* Given any typ we can project out a relation: *)

Program Definition relationH_of_typ (A : typ) : relationH A A :=
  fun p => equalE A (fst p) (snd p).
Next Obligation.
  do 2 red. intros (x1 & y1) (x2 & y2) (HA & HB).
  cbn in *. split; intros.
  - rewrite <- HA; rewrite <- HB; assumption.
  - rewrite HA; rewrite HB; assumption.
Qed.

Coercion relationH_of_typ : typ >-> relationH.

Definition relationH_to_relation {A: typ} (R : relationH A A) : relation A :=
  fun (x : @Ty A) (y : @Ty A) => R @ (x, y).

Notation "↓ R" := (relationH_to_relation R) (at level 5).

Instance Proper_relation {A: typ} (R : relationH A A) :
  Proper (equalE A ==> equalE A ==> iff) (↓ R).
Proof.
  destruct R.
  repeat red. intros. cbn.
  split; intros.
  - specialize (p (x0, x1) (y, y0)).  apply p.
    rewrite H. rewrite H0. reflexivity. assumption.
  - specialize (p (x0, x1) (y, y0)).  apply p.
    rewrite H. rewrite H0. reflexivity. assumption.
Qed.


Coercion relationH_to_relation : relationH >-> relation.

Definition ReflexiveH {A: typ} (R : relationH A A) : Prop :=
  forall (a:A), R @ (a, a).

Definition SymmetricH {A: typ} (R : relationH A A) : Prop :=
  forall (p: A × A), R @ p -> R @ (snd p, fst p).

Definition TransitiveH {A: typ} (R : relationH A A) : Prop :=
  forall (p q: A × A), R @ p -> R @ q -> equalE A (snd p) (fst q) -> R @ (fst p, snd q).

Lemma relationH_reflexive : forall (A:typ), ReflexiveH A.
Proof.
  intros A.
  destruct A; cbn. 
  repeat red. intros. cbn. reflexivity.
Qed.

Lemma relationH_symmetric : forall (A:typ), SymmetricH A.
Proof.
  intros A.
  destruct A; cbn. 
  repeat red. intros. cbn in *. symmetry; assumption.
Qed.

Lemma relationH_transitive : forall (A:typ), TransitiveH A.
Proof.
  intros A.
  destruct A; cbn. 
  repeat red. intros. cbn in *.
  destruct p, q. cbn in *.
  eapply transitivity. apply H. eapply transitivity. apply H1. assumption.
Qed.

Lemma ReflexiveH_Reflexive {A: typ} (R : relationH A A) :
  ReflexiveH R <-> Reflexive ↓R.
Proof.
  split; intros.
  - red. apply H.
  - apply H.
Qed.    

Lemma SymmetricH_Symmetric {A: typ} (R : relationH A A) :
  SymmetricH R <-> Symmetric ↓R.
Proof.
  split; intros.
  - red. unfold SymmetricH in H. intros. specialize (H (x ,y)). cbn in H.
    apply H. assumption.
  - red. intros p HP. destruct p. cbn in *. apply H. assumption.
Qed.    

Lemma TransitiveH_Transitive {A: typ} (R : relationH A A) :
  TransitiveH R <-> Transitive ↓R.
Proof.
  split; intros.
  - red. intros x y z H0 H1. unfold TransitiveH in H.
    specialize (H (x, y) (y, z) H0 H1). apply H. cbn. reflexivity.
  - red. intros p q HP HQ EQ. destruct p; destruct q; cbn.
    unfold Transitive in H. cbn in EQ.
    eapply H. apply HP.  rewrite EQ. apply HQ.
Qed.    


(** ** subrelationH *)
Section SubRelationH.

  (* YZ TODO: Study how [subrelation] is manipulated. Notably:
     * Relevance of using [flip] exactly, and how it relates to us using [transpose]
     * Definition of [relation_equivalence] in terms of [predicate_equivalence]
   *)
  (* TODO: Instances for directed rewriting by [subrelationH] *)

  Global Instance subrelationH_Reflexive {A B: typ} (R: relationH A B): R ⊑ R.
  Proof.
    intros!; auto.
  Qed.

  (* TODO: Figure out how all of this should be organized w.r.t. typeclasses.
     Should be an instance of [Preorder eq_rel subrelationH] most likely?
   *)
  Definition subrelationH_antisym {A B: typ} (R S: relationH A B) `{R ⊑ S} `{S ⊑ R}: R ≡ S.
  Proof.
    split; auto.
  Qed.

  Global Instance subrelationH_trans {A B: typ} (R S T: relationH A B)
         `{R ⊑ S} `{S ⊑ T} : R ⊑ T.
  Proof.
    intros!; auto.
  Qed.

  Global Instance subrelationH_refl_eq {A: typ} (R: relationH A A) (H : Reflexive ↓R) : A ⊑ R.
  Proof.
    intros!. 
    destruct R. cbn in *.
    rewrite H0.
    apply H.
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
  (* SAZ: BROKE THIS *)
  (*
  Global Instance eq_rel_rewrite {A B}: subrelationH eq_rel (pointwise_relation A (pointwise_relation B iff)).
  Proof.
    intros!; destructn @eq_rel; split; intro; appn subrelationH; auto.
  Qed.
   *)
End RelationEqRel.

Section RelationCompose.

  (* [eq] define identities *)
  Lemma eq_id_r: forall {A B : typ} (R : relationH A B),
    (B ∘ R) ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & HR & EQ).
      rewrite <- EQ. assumption.
    - cbn. exists y. split; auto. reflexivity.
  Qed.

  Lemma eq_id_l: forall {A B} (R : relationH A B),
      R ∘ A ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & EQ & HR).
      rewrite EQ. assumption.
    - cbn. exists x. split; auto. reflexivity.
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
  Global Instance transpose_Reflexive {A} (R : relationH A A) {RR: Reflexive ↓R} : Reflexive ↓† R | 100.
  Proof.
    red. intros x. apply RR.
  Qed.

  Global Instance transpose_Symmetric {A} (R : relationH A A) {RS: Symmetric ↓R} : Symmetric ↓† R | 100.
  Proof.
    red; intros x; unfold transpose; intros. apply SymmetricH_Symmetric in RS.
    apply RS. assumption.
  Qed.

  Global Instance transpose_Transitive {A} (R : relationH A A) {RT : Transitive ↓R} : Transitive ↓† R | 100.
  Proof.
    red; intros x; unfold transpose; intros.
    apply TransitiveH_Transitive in RT.
    unfold TransitiveH in RT.
    destruct A. cbn in *. destruct R. cbn in *.
    specialize (RT (pair z y) (pair y x)). cbn in RT. apply RT; auto. reflexivity.
  Qed.
  (* end
     [transpose] is closed on equivalence relations
   *)

  (* begin
     [transpose] is a functor (from the opposite category into itself)
   *)
  Lemma transpose_eq {A: typ}
    : † A ≡ A.
  Proof.
    split; unfold transpose; intros!; subst; auto. cbn in H. rewrite H. destruct A. cbn. reflexivity.
    cbn in H. rewrite H. destruct A. cbn. reflexivity.
  Qed.

  Lemma transpose_sym {A : typ} (R : relationH A A) {RS: Symmetric ↓R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; cbn in *.
    apply SymmetricH_Symmetric in RS. red in RS. apply (RS (y, x)). assumption.
    apply SymmetricH_Symmetric in RS. red in RS. apply (RS (x, y)). assumption.
  Qed.

  Lemma transpose_compose {A B C : typ}
        (R : relationH A B) (S : relationH B C)
    : † (S ∘ R) ≡ (†R ∘ †S).
  Proof.
    split; unfold transpose; cbn; intros!; cbn in *.
    - destruct H as (b & HR & HS). exists b. tauto.
    - destruct H as (b & HR & HS). exists b. tauto.
  Qed.

  Global Instance Proper_transpose {A B : typ}
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
      cbn in *. intros. apply HS. assumption.
  Qed.

  Global Instance transpose_Proper :forall A B, Proper (@eq_rel A B ==> eq_rel) (@transpose A B).
  Proof.
    intros A B R1 R2 (Hab & Hba).
    split.
    - apply transpose_inclusion in Hab. assumption.
    - apply transpose_inclusion in Hba. assumption.
  Qed.

  (* [transpose] is the identity over symmetric relations *)
  Lemma transpose_sym_eq_rel {A} (R : relationH A A) {RS: Symmetric ↓R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; cbn in *.
    - apply SymmetricH_Symmetric in RS. unfold SymmetricH in RS. apply (RS (pair y x)). assumption.
    - apply SymmetricH_Symmetric in RS. unfold SymmetricH in RS. apply (RS (pair x y)). assumption.      
  Qed.

  (* [transpose] is monotone *)
  Global Instance transpose_monotone
         {A B} (R S: relationH A B) `{R ⊑ S}
    : †R ⊑ †S.
  Proof.
    unfold transpose; intros!; appn subrelationH; auto.
  Qed.

End TransposeFacts.

Section ProdRelFacts.

  (* [prod_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {R S : typ}.
    Context (RR : relationH R R).
    Context (SS : relationH S S).

    Global Instance prod_rel_refl `{Reflexive _ ↓RR} `{Reflexive _ ↓SS} : Reflexive ↓(RR ⊗ SS).
    Proof.
      intros []. apply ReflexiveH_Reflexive in H. apply ReflexiveH_Reflexive in H0.
      cbn. split. apply H. apply H0.
    Qed.

    Global Instance prod_rel_sym `{Symmetric _ ↓RR} `{Symmetric _ ↓SS}  : Symmetric ↓(RR ⊗ SS).
    Proof.
      intros ? ? ?. apply SymmetricH_Symmetric in H. apply SymmetricH_Symmetric in H0.
      red. red in H1. 
      destruct x; destruct y; cbn in *. destruct H1. split.
      - unfold SymmetricH in H. specialize (H (t, t1)). apply H. assumption.
      - unfold SymmetricH in H0. specialize (H0 (t0, t2)). apply H0. assumption.      
    Qed.

    Global Instance prod_rel_trans `{Transitive _ ↓RR} `{Transitive _ ↓SS}  : Transitive ↓(RR ⊗ SS).
    Proof.
      intros!.
      apply TransitiveH_Transitive in H. apply TransitiveH_Transitive in H0.
      unfold TransitiveH in *.
      destruct x, y, z.
      repeat red in H1. repeat red in H2.
      destruct H1, H2.
      specialize (H (t, t1) (t1, t3) H1 H2).
      specialize (H0 (t0, t2) (t2, t4) H3 H4).
      cbn in *. split. apply H. reflexivity. apply H0. reflexivity.
    Qed.

    Global Instance prod_rel_eqv `{Equivalence _ ↓RR} `{Equivalence _ ↓SS} : Equivalence ↓(RR ⊗ SS).
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End Equivalence.

  (* [prod_rel] is monotone in both parameters *)
  Global Instance prod_rel_monotone
         {A B C D: typ} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
  : R ⊗ S ⊑ R' ⊗ S'.
  Proof.
    intros!. destruct x, y. repeat red. repeat red in H1. destruct H1.
    split.
    - apply H. assumption.
    - apply H0. assumption.
  Qed.

  (* begin
   [prod_rel] is a bifunctor
   *)

  Lemma prod_rel_eq : forall (A B:typ),  A ⊗ B ≡ (A × B).
  Proof.
    intros.
    unfold eq_rel; split; unfold subrelationH; intros.
    - destruct x, y. repeat red in H. destruct H. cbn.   split; assumption.
    - destruct x; destruct y. cbn in H. repeat red. split; tauto.
  Qed.

(* SAZ: Got to here 
    - add tactics invn_prod_rel and invn_compose? 
*)
  (*
  Lemma prod_compose {A B C D E F: typ}
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
*)
End ProdRelFacts.

(*
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

*)
