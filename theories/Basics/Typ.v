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

Declare Scope typ_scope.
Open Scope typ_scope.

(* SAZ: Yet another try at Typ but this time with equivalence relations and an "elt" predicate. *)

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
      equal : relation Ty;
      equal_Equivalence :> Equivalence equal
    }.
Arguments equal {T}: rename.
Arguments Typ {Ty} _ {equal_Equivalence}.
Notation "'equalE' T" := (@equal T) (at level 5) : typ_scope.
Notation "A '==' B" := (equalE _ A B) (at level 50) : typ_scope.
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

Lemma elt_in : forall (T : typ) (x : T), x == x.
Proof. intros T x. reflexivity.
Qed.      


(** ** top
    Given a carrier [A], the [top] relation has no elements distinguished.
 *)
Instance top_Equivalence {A} : Equivalence (fun a b : A => True).
Proof.
  split; eauto.
Qed.

(* The (any) top typ is the (a) terminal object of the category. *)
Definition top_typ A : typ := Typ (fun a b : A => True).

(** ** Prop
    We can define a typ for Prop using `iff` as equality. 

    SAZ: TODO - better notations?
 *)
Definition prop_typ : typ := Typ (iff).


(** ** Hom Set *)

(* typ_proper forms the morphisms of the category *)

Definition typ_proper (a b : typ) := {f | Proper (equalE a ==> equalE b) f}. 
Notation "TA -=-> TB" := (typ_proper TA TB) (at level 40).

Definition typ_proper_app {a b : typ} (f : a -=-> b) (x : a) : b := (` f) x.

Notation "f @ x" := (typ_proper_app f x) (at level 40).

Instance eq2_typ_proper : Eq2 typ_proper :=
    (fun a b f g => forall (x : a) (y : a), equalE a x y -> equalE b (f @ x) (g @ y)).

Global Instance Proper_typ_proper_app : forall {a b : typ},
    Proper (eq2 ==> equalE a ==> equalE b)
            (@typ_proper_app a b).
Proof.
  repeat intro.
  destruct x, y.
  cbn in *.
  specialize (H x0 y0).
  cbn in H.
  apply H. assumption.
Qed.

 
(* arrow_typ internalizes the hom set as an object in the category *)
Program Instance arrow_typ (TA TB : typ) : typ :=
  @Typ (TA -=-> TB) (fun (f g : TA -=-> TB) => forall a1 a2, (equalE TA a1 a2) -> (equalE TB (` f a1) (` g a2))) _.
Next Obligation.
  destruct TA; destruct TB; split.
  - repeat red. intros. destruct x; cbn in *. apply p. assumption.
  - repeat red. intros x y H1 a1 a2 H2. destruct y. cbn in *.
    symmetry. apply H1. symmetry. apply H2.
  - repeat red. intros x y z H1 H2 a1 a2 H3. destruct x; destruct z; destruct y; cbn in *.
    eapply transitivity. apply H1. apply H3. apply H2. eapply transitivity. symmetry. apply H3. apply H3.
Qed.  

Notation "TA ~~> TB" := (arrow_typ TA TB) (at level 40) : typ_scope.

Program Definition internalize_arrow {TA TB : typ} (f : TA -=-> TB) : TA ~~> TB := f.
Program Definition externalize_arrow {TA TB : typ} (f : TA ~~> TB) : TA -=-> TB := f.

(** ** prod
    Cartesian product of two [typ].
    In this approach, we have a lot of type annotations, but the term is straightforward to write.
 *)

Instance pair_Equivalence (A B:Type) (RA : relation A)
         `{Equivalence A RA} (RB : relation B) `{Equivalence B RB}:
  Equivalence (fun (p q: A * B) => RA (fst p) (fst q) /\ RB (snd p) (snd q)).
Proof.
  split.
  repeat red. intros; split; reflexivity.
  repeat red. intros x y (H1 & H2). split; symmetry; assumption.
  repeat red. intros x y z (H1 & H2) (H3 & H4). split; eapply transitivity; eauto.
Qed.


Instance prod_typ (TA TB: typ) : typ :=
  Typ (fun (p q: TA * TB) => equal (fst p) (fst q) /\ equal (snd p) (snd q)).
Notation "e × f" := (prod_typ e f) (at level 70).


Definition pair_typ {a b : typ} (x : a) (y : b) : a × b := pair x y.
Definition fst_typ {a b : typ} (x : a × b) : a := fst x.
Definition snd_typ {a b : typ} (x : a × b) : b := snd x.

Notation "( x , y )" := (pair_typ x y) : typ_scope.

Program Definition curry_ {a b c : typ} (f : (a × b) -=-> c) : a -> (b ~~> c) :=
  fun (x:a) => _.
Next Obligation.
  exists (fun b => f @ (x, b)).
  do 2 red. intros b1 b2 EQB. destruct f; cbn in *. apply p. cbn.
  split; [ reflexivity | assumption].
Defined.  
  
Program Definition curry {a b c : typ} (f : (a × b) -=-> c) : a -=-> (b ~~> c) :=
  exist _ (fun x => curry_ f x) _.
Next Obligation.
  do 2 red.
  intros x y H a1 a2 H0.
  destruct f; cbn in *. apply p. cbn. tauto.
Defined.  

Goal ((3 : top_typ nat) == (4 : top_typ nat)) .
Proof.
  repeat red; auto.
Qed.

Fact prod_typ_gen : forall (TA TB : typ) (x : TA × TB), x == (fst x, snd x).
Proof.
  intros TA TB x.
  destruct x; reflexivity.
Qed.  

Goal ((3 : top_typ nat), (4 : top_typ nat)) == ((4 : top_typ nat), (4 : top_typ nat)).
Proof.
  repeat red. split; reflexivity. 
Qed.


Global Instance Proper_pair {TA TB : typ} :
  Proper (equalE TA ==> equalE TB ==> equalE (TA × TB)) (fun x y => (x, y)).
Proof.
  repeat red; intros.
  split; cbn; assumption.
Qed.

Goal forall (x: top_typ nat), (x == 4) -> ((x, x)  == ((3 : top_typ nat), (3 : top_typ nat))).
  intros.
  rewrite H.
  apply Proper_pair; reflexivity.
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

Instance sum_PER (A B:Type)
         (RA : relation A) `{Equivalence A RA}
         (RB : relation B) `{Equivalence B RB} :
  Equivalence (fun (p q : A + B) =>
          match pair p q with
          | pair (inl x) (inl y) => RA x y
          | pair (inr x) (inr y) => RB x y
          | pair _ _ => False
          end).
Proof.
  split; repeat red; intros.
  - destruct x; try reflexivity.
  - destruct x; destruct y; try tauto; symmetry; auto.
  - destruct x; destruct y; destruct z; try tauto; etransitivity; eauto.
Qed.

Instance sum_typ (TA TB : typ) : typ :=
  Typ (fun (p q : TA + TB) =>
          match pair p q with
          | pair (inl x) (inl y) => equalE TA x y
          | pair (inr x) (inr y) => equalE TB x y
          | pair _ _ => False
          end).
Notation "e ⨥ f" := (sum_typ e f) (at level 80) : typ_scope.

Definition inl_typ {a b : typ} (x : a) : a ⨥ b := inl x.
Definition inr_typ {a b : typ} (x : b) : a ⨥ b := inr x.


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


(*
    Typ forms a Category. We are working in a category C, where:

    Objects:    Typ
    Hom (Typ eqA) (Typ eqB) := { f | Proper (eqA ==> eqB) f }
    ID in Hom (Typ eqA) (Typ eqA) := fun (x:A) => x
*)
Section TypCat.


  Lemma id_ok: forall (TA : typ),
      Proper (equalE TA ==> equalE TA) (fun x => x).
  Proof.
    intros.
    repeat red. tauto.
  Defined.

  Instance compose_Proper:
    forall (TA TB TC : typ)
      (f : TA -=-> TB)
      (g : TB -=-> TC),
      Proper (equalE TA ==> equalE TC) ((` f) >>> (` g)).
  Proof.
    intros TA TB TC f g a1 a2 EQ.
    repeat red.
    destruct TC; cbn. destruct g; destruct f; cbn in *.
    apply p. apply p0. assumption.
  Defined.

  Global Instance id_typ_proper : Id_ typ_proper :=
    fun TA : typ =>
    exist (fun f : TA -> TA => Proper (equalE TA ==> equalE TA) f)
      (fun x : TA => x) (id_ok TA).

  Global Instance cat_typ_proper : Cat typ_proper :=
    fun (a b c : typ) (f : a -=-> b) (g : b -=-> c) =>
    exist (fun x : a -> c => Proper (equalE a ==> equalE c) x)
      ((` f) >>> (` g)) (compose_Proper a b c f g).

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

Global Instance Proper_equal (A : typ) :
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
  unfold eq2, eq2_typ_proper. intros.
  econstructor.
  - red. repeat intro. destruct x, y. cbn in *. symmetry. apply H. symmetry. assumption.
  - red. repeat intro. destruct x, y. cbn in *.  eapply PER_Transitive.
    apply H. eassumption. apply H0. reflexivity.
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



(* (* Properness property about exponentials *********************************** *) *)

Global Instance arr_PER: forall a b, PER (equalE (a ~~> b)).
Proof.
  destruct a, b; cbn.
  split.
  - repeat red. intros. destruct x,y; cbn in *. symmetry. apply H. symmetry. assumption.
  - repeat red. intros. destruct x,y,z; cbn in *. etransitivity. apply H. eassumption. apply H0. reflexivity.
Defined.



(* Misc. Utilities ********************************************************** *)


Notation "-=->!" := (exist _) (right associativity, at level 50) : typ_scope.

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


