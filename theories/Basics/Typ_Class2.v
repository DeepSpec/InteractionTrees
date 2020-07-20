From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From ITree Require Import
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor
     Basics.Function
.

Import CatNotations.
Open Scope cat_scope.
Import ProperNotations.

Definition rel (A : Type) := A -> A -> Prop.

(**
   Definition of [typ] as a class whose carrier is internal to the class.
   In contrast to [Typ_Class1], we often need to use the constructor explicitly to build values
   of the class since although we can define a coercion via [typ], the coercion requires the
   type checker to see the relation considered explicitly as a [rel A] and not a [A -> A -> Prop].

   _Warning_: you want to be a bit careful with what goes on behind the scene with this version.
   Jumping ahead to the definition of the product, you can readily write the following:
   Instance prod_typ (TA TB: typ) : typ :=
     Typ (fun '(pa,pb) '(qa,qb) => equal pa qa /\ equal (pb: TB) qb).
   But you won't get what you're looking for!
 *)
Class typ : Type :=
  Typ {
      Ty : Type;
      equal : rel Ty;
      equal_PER :> PER equal
    }.
Arguments equal {T}: rename.
Arguments Typ {Ty} _ {equal_PER}.
Notation "'equalE' T" := (@equal T) (at level 5).
Notation "A '==' B" := (equalE _ A B) (at level 50).
(* This coercion allows us to write [(a: T)] to mean [(a : Ty T)] *)
Coercion Ty  : typ >-> Sortclass.
(* Coercion Typ : rel >-> typ. *)

(* Our usual [Type]s are recovered by setting the relation to [eq] *)
Instance typ_eq (A: Type) : typ := Typ (@eq A).
(* Note that we could have used the coercion instead of the constructor as follows:
Instance typ_eq (A: Type) : typ := (@eq A): rel A.
But that the simplest version cannot be inferred:
Instance typ_eq (A: Type) : typ := @eq A.
*)

(* A [typ A] can be thought as the sub-type of elements of [A] over which [equal] is reflexive *)
Definition contains (T : typ) (a:T) : Prop := equal a a.
Notation "a ∈ T" := (contains T a) (at level 75).

Record elt (T:typ) :=
  mk_elt {
      it :> T;
      IN : it ∈ T
    }.

Lemma elt_in : forall (T : typ) (x : elt T), x == x.
Proof. intros T (x & I). cbn. assumption.
Qed.      

(* In particular, all elements are in their [typ_eq] *)
Fact type_eq_full : forall A (a: A), a ∈ (typ_eq A).
Proof.
  reflexivity.
Qed.

(** ** top, bot
    Given a carrier [A], two particular [typ A] can be defined: [top] where no elements are distinguished,
    and [bot] which is basically the empty type seen as a subtype of [A]
    (no reflexive elements for the relation, so no elements in [bot A])
 *)
Instance top_PER {A} : PER (fun a b : A => True).
Proof.
  split; eauto.
Qed.

Instance bot_PER {A} : PER (fun a b : A => False).
Proof.
  split; eauto.
Qed.

Definition top_typ A : typ := Typ (fun a b : A => True).
Definition bot_typ A : typ := Typ (fun a b : A => False).

(* All elements are also in [top_typ] *)
Fact top_typ_full : forall A (a: A), a ∈ (top_typ A).
Proof.
  reflexivity.
Qed.

(* But none are in [bot_typ] *)
Fact bot_typ_empty : forall A (a: A), ~a ∈ (bot_typ A).
Proof.
  intros ? ? abs; inversion abs.
Qed.

(** ** prod
    Cartesian product of two [typ].
    In this approach, we have a lot of type annotations, but the term is straightforward to write.
 *)

Instance pair_PER (A B:Type) (RA : rel A) `{PER A RA} (RB : rel B) `{PER B RB}:
  PER (fun (p q: A * B) => RA (fst p) (fst q) /\ RB (snd p) (snd q)).
Proof.
  split.
  repeat red. intros x y (H1 & H2). split; symmetry; assumption.
  repeat red. intros x y z (H1 & H2) (H3 & H4). split; eapply transitivity; eauto.
Qed.

Instance prod_typ (TA TB: typ) : typ :=
  Typ (fun (p q: TA * TB) => equal (fst p) (fst q) /\ equal (snd p) (snd q)).
Notation "e × f" := (prod_typ e f) (at level 70).

(* We indeed picked the most general product of typs in that all pairs of elements _belonging_ to the crossed typs are in: *)
Fact prod_typ_gen : forall (TA TB: typ) (a: TA) (b : TB),
    (a ∈ TA /\ b ∈ TB) <-> (a,b) ∈ TA × TB.
Proof.
  intros *; split; (intros [INA INB]; split; [apply INA | apply INB]).
Qed.


Global Instance Proper_pair {TA TB : typ} :
  Proper (equalE TA ==> equalE TB ==> equalE (TA × TB)) (fun x y => (x, y)).
Proof.
  repeat red; intros.
  split; cbn; assumption.
Qed.

Global Instance Proper_fst {TA TB : typ} :
  Proper (equalE (TA × TB) ==> equalE TA) fst.
Proof.
  repeat red; intros; cbn.
  destruct TA. cbn. destruct x. destruct y. cbn. destruct H. assumption.
Qed.

Global Instance Proper_snd {TA TB : typ} :
  Proper (equalE (TA × TB) ==> equalE TB) snd.
Proof.
  repeat red; intros; cbn.
  destruct TA. cbn. destruct x. destruct y. cbn. destruct H. assumption.
Qed.


(** ** sum 
  Coproduct of two [typ].
 *)

Instance sum_PER (A B:Type) (RA : rel A) `{PER A RA} (RB : rel B) `{PER B RB} :
  PER (fun (p q : A + B) =>
          match (p, q) with
          | (inl x, inl y) => RA x y
          | (inr x, inr y) => RB x y
          | (_, _) => False
          end).
Proof.
  split; repeat red; intros.
  - destruct x; destruct y; try tauto; symmetry; auto.
  - destruct x; destruct y; destruct z; try tauto; etransitivity; eauto.
Qed.

Instance sum_typ (TA TB : typ) : typ :=
  Typ (fun (p q : TA + TB) =>
          match (p, q) with
          | (inl x, inl y) => equal x y
          | (inr x, inr y) => equal x y
          | (_, _) => False
          end).
Notation "e ⨥ f" := (sum_typ e f) (at level 80).


Global Instance Proper_inl {TA TB : typ} :
  Proper (equalE TA ==> equalE (TA ⨥ TB)) inl.
Proof.
  repeat red; intros; cbn.
  destruct TA. cbn. assumption.
Qed.

Global Instance Proper_inr {TA TB : typ} :
  Proper (equalE TB ==> equalE (TA ⨥ TB)) inr.
Proof.
  repeat red; intros; cbn.
  destruct TA. cbn. assumption.
Qed.

Fact sum_typ_gen1 : forall (TA TB : typ) (a : TA),
    (a ∈ TA) <-> (inl a) ∈ (TA ⨥ TB).
Proof.
  intros TA TB a.
  split.
  - intros IN. apply Proper_inl. assumption.
  - intros. red in H. red. destruct TA. cbn in *. assumption.
Qed.  

Fact sum_typ_gen2 : forall (TA TB : typ) (b : TB),
    (b ∈ TB) <-> (inr b) ∈ (TA ⨥ TB).
Proof.
  intros TA TB b.
  split.
  - intros IN. apply Proper_inr. assumption.
  - intros. red in H. red. destruct TB. cbn in *. assumption.
Qed.

Class typ2 : Type :=
  Typ2 {
      Ty2 : Type;
      equal2 : rel Ty2;
      equal_PER2 :> Equivalence equal2
    }.


Instance fun_PER (A B:Type) (RA : rel A) `{Equivalence A RA} (RB : rel B) `{Equivalence B RB}
  : typ2.
Proof.
  eapply (Typ2 ({f | Proper (RA ==> RB) f})
               (fun f g => forall a1 a2, RA a1 a2 -> RB (` f a1) (` g a2))).
  split.
  - repeat red. intros.  destruct x. cbn. apply p. assumption.
  - repeat red. intros x y H1 a1 a2 H2.

    symmetry. apply H1. symmetry. apply H2.
  - repeat red. intros x y z H1 H2 a1 a2 H3.
    eapply transitivity. apply H1. apply H3. apply H2. eapply transitivity. symmetry. apply H3. apply H3.
Qed.




Instance fun_PER (A B:Type) (RA : rel A) `{PER A RA} (RB : rel B) `{PER B RB}
  : PER (fun (f g: A -> B) => forall a1 a2, RA a1 a2 -> RB (f a1) (g a2)).
Proof.
  split.
  - repeat red. intros x y H1 a1 a2 H2.  symmetry. apply H1. symmetry. apply H2.
  - repeat red. intros x y z H1 H2 a1 a2 H3.
    eapply transitivity. apply H1. apply H3. apply H2. eapply transitivity. symmetry. apply H3. apply H3.
Qed.

(** ** arr
    Exponential of two [typ].
 *)
Definition arr_typ (TA TB: typ) : typ :=
  Typ (fun (f g: TA -> TB) => forall a1 a2, equal a1 a2 -> equal (f a1) (g a2)).

Notation "e ~~> f" := (arr_typ e f) (at level 60).

(* Elements in the arrow [typ] are exactly the functions respecting the equivalences *)
Fact arr_typ_gen : forall (TA TB: typ) (f: TA -> TB),
     f ∈ TA ~~> TB <-> Proper (equalE TA ==> equalE TB) f.
Proof.
  intros *; split; intros H; apply H.
Qed.

Goal ((Typ (@eq nat)) ~~> (bot_typ nat)).
Proof.
  Fail typeclasses eauto. (* Still no instance with new Typ definition. *)
Abort.


(** ** Prop
    We can define a typ for Prop using `iff` as equality. 

    SAZ: TODO - better notations?
*)
Definition prop_typ : typ := Typ (iff).


(*
    Typ forms a Category. We are working in a category C, where:

    Objects:    Typ
    Hom (Typ eqA) (Typ eqB) := { f | Proper (eqA ==> eqB) f }
    ID in Hom (Typ eqA) (Typ eqA) := fun (x:A) => x
*)
Section TypCat.

  Definition typ_proper (a b : typ) := (elt (a ~~> b)).
  Notation "TA -=-> TB" := (typ_proper TA TB) (at level 40).

  Definition typ_proper_app {a b : typ} (f : a -=-> b) (x : elt a) : b :=
    (it f) (it x).

  Notation "f @ x" := (typ_proper_app f x) (at level 40).

  Instance eq2_typ_proper : Eq2 typ_proper :=
    (fun a b f g => forall (x : elt a) (y : elt a), equalE a x y -> equalE b (f @ x) (g @ y)).

  Lemma id_ok: forall (TA : typ),
      Proper (equalE TA ==> equalE TA) (fun x => x).
  Proof.
    intros.
    repeat red. tauto.
  Defined.

  Lemma compose_ : forall (TA TB TC : typ)
                   (f : elt (TA ~~> TB))
                   (g : elt (TB ~~> TC))
      (it f >>> it g) ∈ (TA ~~> TC).
  Proof.
    intros TA TB TC f g P1 P2.
    repeat red.
    intros.
    apply P2. apply P1. assumption.
  Defined.

  Global Instance id_typ_proper : Id_ typ_proper :=
    fun TA : typ =>
    exist (fun f : TA -> TA => Proper (equalE TA ==> equalE TA) f)
      (fun x : TA => x) (id_ok TA).

  Global Instance cat_typ_proper : Cat typ_proper :=
    fun (a b c : typ) (TA : a -=-> b) (TB : b -=-> c) =>
    exist (fun f : a -> c => Proper (equalE a ==> equalE c) f)
      (fun x : a => TB @ (TA @ x)) (compose a b c _ _ (proj2_sig TA) (proj2_sig TB)).

  Global Instance cat_IdL_typ_proper : CatIdL typ_proper.
    repeat intro. destruct f. cbn. apply p. assumption.
  Defined.

  Global Instance cat_IdR_typ_proper : CatIdR typ_proper.
    repeat intro. destruct f. cbn. apply p. assumption.
  Defined.

  Global Instance cat_assoc_typ_proper : CatAssoc typ_proper.
    refine (fun a b c d TA TB TC => _). repeat intro.
    destruct TA, TB, TC. eapply p1. eapply p0. eapply p. assumption.
  Defined.

  Global Instance proper_typ_proper (a b c : typ) : Proper ((@eq2 typ _ _ a b) ==> (@eq2 typ _ _ b c) ==> (@eq2 typ _ _ a c)) (cat).
    repeat intro.
    destruct x, y, x0, y0. unfold eq2, eq2_typ_proper in H0.
    cbn in H0. unfold eq2, eq2_typ_proper in H. cbn in H. cbn.
    specialize (H x1 y1 H1).
    specialize (H0 (x x1) (x2 y1)).
    apply H0. apply H.
  Defined.

  Global Instance category_typ_proper : Category typ_proper.
    constructor; try typeclasses eauto.
  Defined.

  
End TypCat.


Notation "A '-=->' B" := (typ_proper A B) (right associativity, at level 70).
Notation "f @ x" := (typ_proper_app f x) (at level 40).


Section TypCatCoproducts.

(** *** Coproducts *)

Program Definition case_typ_proper
  {A B C : typ} (f : A -=-> C) (g : B -=-> C) : (A ⨥ B) -=-> C :=
    (fun (x : A ⨥ B) =>
      match x with
      | inl a => f @ a
      | inr b => g @ b
      end).
Next Obligation.
  repeat red.
  intros x y.
  destruct C; destruct x; destruct y; cbn in *; try tauto.
  - intros. destruct f. cbn. apply p. assumption. 
  - intros. destruct g. cbn. apply p. assumption. 
Qed.


(** Coproduct elimination *)
Instance case_sum : Case typ_proper sum_typ := @case_typ_proper.

Program Definition prod_typ_proper
        {A B C : typ} (f : C -=-> A) (g : C -=-> B) : C -=-> (A × B) :=
  fun (c: C) => (f c, g c).
Next Obligation.
  repeat red.
  intros x y H.
  destruct f; destruct g; cbn in *.
  split.
  - apply p. assumption.
  - apply p0. assumption.
Qed.

Instance pair_prod: Pair typ_proper prod_typ := @ prod_typ_proper.

(** Injections *)

Program Definition inl_typ_proper {A B : typ} : A -=-> (A ⨥ B) :=
  inl.
Next Obligation.
  repeat red. intros x y EQ. destruct A. assumption.
Qed.  

Program Definition inr_typ_proper {A B : typ} : B -=-> (A ⨥ B) :=
  inr.
Next Obligation.
  repeat red. intros x y EQ. destruct B. assumption.
Qed.  


Instance sum_inl : Inl typ_proper sum_typ := @inl_typ_proper.
Instance sum_inr : Inr typ_proper sum_typ := @inr_typ_proper.

End TypCatCoproducts.  

(* Add proper instances to hint database. *)
Existing Instance eq2_typ_proper.
Existing Instance cat_typ_proper.
Existing Instance id_typ_proper.


(* Proper instances for typ and typ_proper. ********************************* *)

Lemma Proper_typ_proper_app : forall {a b : typ},
    Proper (eq2 ==> equalE a ==> equalE b)
            (@typ_proper_app a b).
Proof.
  repeat intro.
  destruct x, y.
  cbn in *.
  specialize (H x0 y0).
  cbn in H.
  apply H. unfold contains. etransitivity. apply H0. symmetry.
  unfold contains. etransitivity. symmetry. apply H0. apply H0.
Qed.

(* Lemma Proper_typ_proper_app_partial : forall {a b : typ}  *)
(*     Proper (equalE a ==> equalE b) *)
(*             (@typ_proper_app a b x). *)
(* Proof. *)
(*   repeat intro. *)
(*   destruct x, y. *)
(*   cbn in *. *)
(*   specialize (H x0 y0). *)
(*   cbn in H. *)
(*   apply H. unfold contains. etransitivity. apply H0. symmetry. apply H0. *)
(*   unfold contains. etransitivity. symmetry. apply H0. apply H0. *)
(*   assumption. *)
(* Qed. *)

(* Instance Proper_equal_equal (A : typ) : *)
(*   Proper (equalE A --> equalE A ==> Basics.impl) (equalE A). *)
(* Proof. *)
(*   repeat intro. red in H0. *)
(*   transitivity x0; [ | assumption]. transitivity x; assumption. *)
(* Qed. *)

Instance Proper_equal (A : typ) :
  Proper (equalE A ==> equalE A ==> iff) (equalE A).
Proof.
  repeat intro. split.
  - intro. symmetry. etransitivity.
    symmetry. apply H0. transitivity x; [ symmetry | ]; assumption.
  - intro. etransitivity. apply H. transitivity y0; [ | symmetry ]; assumption.
Qed.

(* Instance Proper_equal_partial (A : typ) (a : A) : *)
(*   Proper (equalE A --> Basics.flip Basics.impl) (equalE A a). *)
(* Proof. *)
(*   repeat intro. red in H. transitivity y ; assumption. *)
(* Qed. *)

Instance Proper_equal_partial (A : typ) (a : A) :
  Proper (equalE A ==> iff) (equalE A a).
Proof.
  repeat intro. split. intro;
  etransitivity; eassumption.
  intro; etransitivity; [ | symmetry ]; eassumption.
Qed.

(* Add proper instances to hint database. *)
Existing Instance Proper_typ_proper_app.
Existing Instance Proper_equal.
Existing Instance Proper_equal_partial.


(* Interesting properties about typ_proper *********************************** *)

Instance eq2_PER : forall a b, PER (eq2 (a := a) (b := b)).
Proof.
  pose proof fun_PER.
  unfold eq2, eq2_typ_proper. intros.
  specialize (H a b (equalE a) _ (equalE b) _).
  econstructor.
  - red. repeat intro. destruct x, y. cbn in *. apply H. apply H0. apply H1.
  - red. repeat intro. destruct x, y. cbn in *. destruct H. eapply PER_Transitive.
    eassumption. eassumption. assumption.
Qed.

Global Instance eq2_Reflexive : forall a b, Reflexive (eq2 (a := a) (b := b)).
Proof.
  epose proof cat_IdL_typ_proper. unfold CatIdL in H.
  repeat intro.
  specialize (H a b x).
  unfold eq2, eq2_typ_proper in H.
  rewrite <- H. 2 : symmetry; apply H0. apply H. etransitivity.
  symmetry. apply H0. apply H0.
Defined.

Global Instance eq2_Equivalence : forall a b, Equivalence (eq2 (a := a) (b := b)).
Proof.
  intros; constructor; typeclasses eauto.
Defined.

(* Typ_proper also happens to be a typ. *)
Definition typ_proper_typ a b : typ :=
  Typ (eq2 (a := a) (b := b)).

Notation "A ~=~> B" := (typ_proper_typ A B) (at level 80).

(* (* Properness property about exponentials *********************************** *) *)

Global Instance arr_PER: forall a b, PER (equalE (a ~~> b)).
Proof.
  pose proof fun_PER.
  cbn. intros. specialize (H a b (equalE a) _ (equalE b) _). eapply H.
Defined.



(* Non-empty typ ------------------------------------------------------------ *)

Class NonEmpty (T:typ) : Prop:=
  {
   nonempty: exists (t:T), t == t
  }.

(* Misc. Utilities ********************************************************** *)


Notation "-=->!" := (exist _) (right associativity, at level 50).

(* IY: Is there a better generalized Ltac for this? *)
Ltac unfold_cat :=
    unfold cat, cat_typ_proper, eq2, eq2_typ_proper; cbn.

Tactic Notation "unfold_cat" "in" hyp(H) :=
  unfold cat, cat_typ_proper, eq2, eq2_typ_proper in H; cbn in H.

(* TODO : Automate properness proofs. *)
Ltac find_proper :=
  match goal with
  | |- Proper (equalE ?A ==> iff) _ => apply Proper_equal_partial
  end.

Local Obligation Tactic := program_simpl; try find_proper.


Ltac PER_reflexivity :=
  match goal with
  | [ H : ?eq ?X ?Y |- ?eq ?X ?X ] =>  eapply transitivity; [apply H | symmetry; apply H]
  | [ H : ?eq ?Y ?X |- ?eq ?X ?X ] =>  eapply transitivity; [symmetry; apply H | apply H]
  | [H : ?x == _ |- ?x == _] => etransitivity; [ | symmetry ]; eassumption
  | [H : _ == ?y |- ?x == _] => symmetry in H; etransitivity; [ | symmetry ]; eassumption
  end.


