(** * Category operations *)

(** Interfaces for programming with categories. *)

(** A category is represented by a type of objects [obj], and a type
    of morphisms [C : obj -> obj -> Type].

    The interface gives the signatures for the following operations
    (which may be defined independently).
    For any [a], [b], [c]):

    - [eq2 : C a b -> C a b -> Prop], equivalence of morphisms;

    - [id_ a : C a a], the identity morphism;
    - [cat : C a b -> C b c -> C a c], composition of morphisms;

    - [empty : C i a], the initial morphism (where [i] is the initial
      object);

    - [bimap : C a b -> C c d -> C (bif a b) (bif c d)], "vertical
      composition" of morphisms, where [bif] is a bifunctor
      (in our case it is the coproduct bifunctor);
    - [assoc_l], [assoc_r], [unit_l], [unit_l'], [unit_r], [unit_r']:
      natural isomorphisms of a tensor product [bif], making [C] a
      monoidal category;

    - [case_ : C a c -> C b c -> C (bif a b) c], "case analysis"
      of a coproduct [bif];
    - [inl_ : C a (bif a b)], left injection in a coproduct [bif];
    - [inr_ : C b (bif a b)], right injection;

    - [iter : C a (bif a b) -> C a b], loop operator.
 *)

(** We use typeclasses to give such "canonical names" to these
    operations, allowing us to define common notations and equations
    once and for all. This is the approach described in
    "Type Classes for Mathematics in Type Theory",
    by Bas Spitters and Eelis van der Weegen
    (https://arxiv.org/abs/1102.1323).

    The properties of these operations are given in
    [Basics.CategoryTheory].
 *)

(** Notations [>>>] and [⩯] are in the module [CatNotations], under the scope
    [cat]. The common way to use them is:
[[
  Import CatNotations.
  Local Open Scope cat.
]]
 *)

(** ** Low-level infrastructure *)

(** Categories are parameterized by a type of objects [obj]. *)

Module Import Carrier.

(** A category will be designated by the type of its morphisms (Hom-sets),
    which is indexed by two objects. *)
Notation Hom obj := (obj -> obj -> Type) (only parsing).

(** Examples found in this library:

    - The category of functions: [obj := Type], [Fun a b := a -> b].
    - The category of indexed functions: [obj := Type -> Type], [IFun E F := E ~> F]
      (where [~>] is defined in [Basics.Basics]).
    - The category of [itree] continuations (one category for every [E : Type -> Type]):
      [obj := Type], [ktree E a b := a -> itree E a b].
    - The category of [itree] handlers: [obj := Type -> Type],
      [Handler E F := E ~> itree F].

    The latter two are Kleisli categories of the former two respectively.
*)

(** Bifunctors from a category to itself are designated by their object maps.
    They are associated to morphism maps via the [Bimap] class. *)
Notation binop obj := (obj -> obj -> obj) (only parsing).

End Carrier.

(** Scope for category notations. *)
(*
  The following line removes the warning on >=8.10, but is incompatible for <8.10
*)
(* Declare Scope cat_scope. *)
Delimit Scope cat_scope with cat.

(** ** Categories *)

(* [/ᐠ｡‸｡ᐟ\] *)
Section CatOps.

Context {obj : Type} (C : Hom obj).

(** The equivalence between two morphisms [f] and [g] is written
    [eq2 f g] or [f ⩯ g] ([\hatapprox] in LaTeX). *)
Class Eq2 : Type :=
  eq2 : forall a b (f g : C a b), Prop.

(** The identity morphism for the object [a : obj] is written [id_ a]. *)
Class Id_ : Type :=
  id_ : forall a, C a a.
(* We add an underscore [id_] to avoid clashing with the standard
   library [id]. *)

(** Given two morphisms [f] and [g] with a common endpoint, their
    composition (or con(cat)enation) is written [cat f g] or [f >>> g]. *)
Class Cat : Type :=
  cat : forall a b c, C a b -> C b c -> C a c.

(** If there is an initial object [i], its initial morphisms are written
    [empty : C i a]. *)
Class Initial (i : obj) :=
  empty : forall a, C i a.

(** If there is a terminal object [t], its terminal morphisms are written
    [one : C a i]. *)
Class Terminal (t : obj) :=
  one : forall a, C a t.

Definition op: Hom obj := fun (A B: obj) => C B A.

End CatOps.

Arguments eq2 {obj C Eq2 a b}.
Arguments id_ {obj C Id_}.
Arguments cat {obj C Cat a b c}.
Arguments empty {obj C i Initial a}.
Arguments one {obj C t Terminal a}.
Arguments op {obj} C.

(** ** Bifunctors *)

Section CocartesianOps.

Context {obj : Type} (C : Hom obj) (bif : binop obj).

(** Bifunctors map pairs of objects to objects ([bif])
    and pairs of morphisms to morphisms ([bimap]).

    The composition [bimap f g] is also called _tensor product_ of [f] and [g].

    Many of the following typeclases are _derived_ from just three basic
    Coproduct constructions:
       - [Case]  (case analysis)
       - [Inl]   (left injection)
       - [Inr]   (right injection)

 *)
Class Bimap :=
  bimap : forall a b c d, C a c -> C b d -> C (bif a b) (bif c d).

(** *** Coproducts *)

(** Coproducts are a generalization of sum types and case analysis. *)

(** Case analysis on a sum. *)
Class Case :=
  case_ : forall a b c, C a c -> C b c -> C (bif a b) c.

(** Injection into the left component. *)
Class Inl :=
  inl_ : forall a b, C a (bif a b).

(** Injection into the right component. *)
Class Inr :=
  inr_ : forall a b, C b (bif a b).

(* Like [id_], the underscores avoid confusion with the names
   from the stdlib ([inl] and [inr] are constructors of [sum],
   and [case] is a tactic.) *)

(** *** Tensor products (monoidal categories) *)

(** [cat] can be seen as "horizontal composition", while
    [bimap] as "vertical composition".
    When this vertical composition is associative and has units
    (similarly to [cat]), we have a monoidal category. To be
    more precise, this associativity and unity of vertical
    composition is generally allowed to be witnessed up to some
    isomorphisms, called associators and unitors.
    These properties are defined formally in [Basics.CategoryTheory].
 *)

(** **** Associators *)

Class AssocR :=
  assoc_r : forall a b c, C (bif (bif a b) c) (bif a (bif b c)).

Class AssocL :=
  assoc_l : forall a b c, C (bif a (bif b c)) (bif (bif a b) c).

(** **** Unitors *)

Class UnitL (i : obj) :=
  unit_l : forall a, C (bif i a) a.

Class UnitL' (i : obj) :=
  unit_l' : forall a, C a (bif i a).

Class UnitR (i : obj) :=
  unit_r : forall a, C (bif a i) a.

Class UnitR' (i : obj) :=
  unit_r' : forall a, C a (bif a i).

(** *** Products *)

(** Products are a generalization of product types *)

(** Pairing. *)
Class Pair :=
  pair_ : forall a b c, C c a -> C c b -> C c (bif a b).

(** Projection onto the left component. *)
Class Fst :=
  fst_ : forall a b, C (bif a b) a.

(** Projection onto the right component. *)
Class Snd :=
  snd_ : forall a b, C (bif a b) b.

(** **** Symmetry *)

Class Swap :=
  swap : forall a b, C (bif a b) (bif b a).

End CocartesianOps.

Arguments bimap {obj C bif Bimap a b c d}.
Arguments case_ {obj C bif Case a b c}.
Arguments inl_ {obj C bif Inl a b}.
Arguments inr_ {obj C bif Inr a b}.
Arguments pair_ {obj C bif Pair a b c}.
Arguments fst_ {obj C bif Fst a b}.
Arguments snd_ {obj C bif Snd a b}.
Arguments assoc_r {obj C bif AssocR a b c}.
Arguments assoc_l {obj C bif AssocL a b c}.
Arguments unit_l  {obj C bif i UnitL a}.
Arguments unit_l' {obj C bif i UnitL' a}.
Arguments unit_r  {obj C bif i UnitR a}.
Arguments unit_r' {obj C bif i UnitR' a}.
Arguments swap {obj C bif Swap a b}.

(** ** Notations with explicit objects *)

(** Useful to annotate the above isomorphisms in cases where their
    types would be ambiguous. *)

Notation assoc_r_ a b c := (@assoc_r _ _ _ _ a b c) (only parsing).
Notation assoc_l_ a b c := (@assoc_l _ _ _ _ a b c) (only parsing).
Notation unit_l_  i a := (@unit_l  _ _ _ i _ a) (only parsing).
Notation unit_l'_ i a := (@unit_l' _ _ _ i _ a) (only parsing).
Notation unit_r_  i a := (@unit_r  _ _ _ i _ a) (only parsing).
Notation unit_r'_ i a := (@unit_r' _ _ _ i _ a) (only parsing).
Notation swap_ a b := (@swap _ _ _ _ a b) (only parsing).

(** With explicit category. *)
Notation case__ C := (@case_ _ C _ _ _ _ _)
  (only parsing).
Notation pair__ C := (@pair_ _ C _ _ _ _ _)
  (only parsing).

(** ** Core notations *)
Module Import CatNotations.

Infix "⩯" := eq2 (at level 70) : cat_scope.
Infix ">>>" := cat (at level 50, left associativity) : cat_scope.

End CatNotations.

Local Open Scope cat.

(** ** Derived constructions *)

(** *** Coproduct operations *)

(** Generalization of [a + a -> a]. *)
Definition merge {obj : Type} {C : Hom obj} {bif : binop obj}
           {Id_C : Id_ C} {Coproduct_C : Case C bif}
  : forall {a : obj}, C (bif a a) a :=
  fun a => case_ (id_ a) (id_ a).

(** **** Cocartesian category *)

(** The coproduct defines a symmetric monoidal category,
    called a _cocartesian category_. *)

Section CocartesianConstruct.

Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).
Variables (SUM : binop obj) (Coprod_SUM : Case C SUM)
          (Inl_SUM : Inl C SUM)
          (Inr_SUM : Inr C SUM).

(** Coproducts are bifunctors. *)
Global Instance Bimap_Coproduct : Bimap C SUM :=
  fun a b c d (f : C a c) (g : C b d) =>
    case_ (f >>> inl_) (g >>> inr_).

(** Coproducts are symmetric. *)

Global Instance Swap_Coproduct : Swap C SUM :=
  fun a b => case_ inr_ inl_.

(** Coproducts are associative. *)

Global Instance AssocR_Coproduct : AssocR C SUM :=
  fun a b c => case_ (case_ inl_ (inl_ >>> inr_))
                    (inr_ >>> inr_).

Global Instance AssocL_Coproduct : AssocL C SUM :=
  fun a b c => case_ (inl_ >>> inl_)
                    (case_ (inr_ >>> inl_) inr_).

Variables (Id_C : Id_ C) (I : obj) (Initial_I : Initial C I).

(** The initial object is a unit for the coproduct. *)

Global Instance UnitL_Coproduct : UnitL C SUM I :=
  fun a => case_ empty (id_ a).

Global Instance UnitL'_Coproduct : UnitL' C SUM I :=
  fun a => inr_.

Global Instance UnitR_Coproduct : UnitR C SUM I :=
  fun a => case_ (id_ a) empty.

Global Instance UnitR'_Coproduct : UnitR' C SUM I :=
  fun a => inl_.

End CocartesianConstruct.
(** **** Cartesian category *)

(** The product defines a symmetric monoidal category,
    called a _cartesian category_. *)

Section CartesianConstruct.

  (* These Instances are kept local and should be made explicit locally using
     [Existing Instance] to avoid clashes with the cocartesian instances
   *)

Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).
Variables (PROD : binop obj) (Prod_PROD : Pair C PROD)
          (Fst_PROD : Fst C PROD)
          (Snd_PROD : Snd C PROD).

(** Products are bifunctors. *)
Instance Bimap_Product : Bimap C PROD :=
  fun a b c d (f : C a c) (g : C b d) =>
    pair_ (fst_ >>> f) (snd_ >>> g).

(** Products are symmetric. *)

Instance Swap_Product : Swap C PROD :=
  fun a b => pair_ snd_ fst_.

(** Products are associative. *)

Instance AssocR_Product : AssocR C PROD :=
  fun a b c => pair_ (fst_ >>> fst_) (pair_ (fst_ >>> snd_) snd_).

Instance AssocL_Product : AssocL C PROD :=
  fun a b c => pair_ (pair_ fst_ (snd_ >>> fst_)) (snd_ >>> snd_).

Variables (Id_C : Id_ C) (T : obj) (Terminal_T : Terminal C T).

(** The initial object is a unit for the product. *)

Instance UnitL_Product : UnitL C PROD T :=
  fun a => snd_.

Instance UnitL'_Product : UnitL' C PROD T :=
  fun a => pair_ one (id_ a).

Instance UnitR_Product : UnitR C PROD T :=
  fun a => fst_.

Instance UnitR'_Product : UnitR' C PROD T :=
  fun a => pair_ (id_ a) one.

End CartesianConstruct.

Section Dagger.
  Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).

  Class Dagger : Type :=
    dagger : forall a b, op C a b -> C a b.

End Dagger.

Arguments dagger {obj C _ a b}.

(** ** Iteration, fixed points *)

Section Iteration.

Context {obj : Type} (C : Hom obj).
Variables (bif : binop obj).

(** Categories with a loop operator (_pre-iterative categories_).
  Abstract generalization of [ITree.Basics.Basics.ALoop] and
  [ITree.Core.KTree.loop]. [iter] is often denoted as a dagger in the
  relevant literature. *)
Class Iter : Type :=
  iter : forall a b, C a (bif a b) -> C a b.

Context
  {Id_C : Id_ C}
  {Cat_C : Cat C}
  {Case_bif : Case C bif}
  {Inl_bif : Inl C bif}
  {Inr_bif : Inr C bif}
  {Iter_bif : Iter}.

(** Trace operator (generalization of [KTree.loop]). *)
Definition loop (a b c : obj)
  : C (bif c a) (bif c b) -> C a b :=
  fun f => inr_ >>> iter _ _ (f >>> bimap inl_ (id_ b)).

(**  For our purposes, [loop] and [iter] are mutually derivable.
  [loop] is a definition instead of another class to prevent the interface
  from growing too much. We originally started with traced categories but
  iterative categories seem to provide more of the theory we need. *)

End Iteration.

Arguments iter {obj C bif _ a b}.
Arguments loop {obj C bif _ _ _ _ _ _ a b c}.

(** ** Automatic solver of reassociating sums *)

Section RESUM.

Context {obj : Type} (C : Hom obj) (bif : binop obj).
Context `{Id_ _ C} `{Cat _ C}.
Context `{Case _ C bif} `{Inl _ C bif} `{Inr _ C bif}.

Class ReSum (a b : obj) :=
  resum : C a b.

(** The instance weights on [ReSum_inl] (8) and [ReSum_inr] (9) are so that,
    if you have a list [E +' E +' F] (associated to the right:
    [E +' (E +' F)]), then the first one will be picked for the inclusion
    [E -< E +' E +' F]. *)

Global Instance ReSum_id `{Id_ _ C} a : ReSum a a := { resum := id_ a }.
Global Instance ReSum_sum a b c
         `{ReSum a c} `{ReSum b c} : ReSum (bif a b) c :=
  { resum := case_ resum resum }.
Global Instance ReSum_inl a b c `{ReSum a b} : ReSum a (bif b c) | 8 :=
  { resum := resum >>> inl_ }.
Global Instance ReSum_inr a b c `{ReSum a b} : ReSum a (bif c b) | 9 :=
  { resum := resum >>> inr_ }.
Global Instance ReSum_empty {i : obj} `{Initial _ _ i} a : ReSum i a :=
  { resum := empty }.

(* Usage template:

[[
Opaque cat.
Opaque id.
Opaque case_.
Opaque inl_.
Opaque inr_.

    (* where the category is (->)  vv *)
Definition f {X Y Z} : complex_sum -> another_complex_sum :=
  Eval compute in resum.

Transparent cat.
Transparent id.
Transparent case_.
Transparent inl_.
Transparent inr_.
]]
*)

End RESUM.
