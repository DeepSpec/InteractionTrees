(** * Category operations *)

(** Interfaces for programming with categories.

    We use typeclasses to give "canonical names" to these operations,
    allowing us to define common notations and equations once and for
    all. This is the approach described in
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

End CatOps.

Arguments eq2 {obj C Eq2 a b}.
Arguments id_ {obj C Id_}.
Arguments cat {obj C Cat a b c}.
Arguments empty {obj C i Initial a}.

(** ** Bifunctors *)

Section CocartesianOps.

Context {obj : Type} (C : Hom obj) (bif : binop obj).

(** Bifunctors map pairs of objects to objects ([bif])
    and pairs of morphisms to morphisms ([bimap]).

    The composition [bimap f g] is also called _tensor product_ of [f] and [g].

    Many of the following typeclases are _derived_ from just three basic 
    Coproduc constructions:
       - [CoprodCase]  (case analysis)
       - [CoprodInl]   (left injection)
       - [CoprodInr]   (right injection)

 *)
Class Bimap :=
  bimap : forall a b c d, C a c -> C b d -> C (bif a b) (bif c d).

(** *** Coproducts *)

(** Coproducts are a generalization of sum types and case analysis. *)

(** Case analysis on a sum. *)
Class CoprodCase :=
  case_ : forall a b c, C a c -> C b c -> C (bif a b) c.

(** Injection into the left component. *)
Class CoprodInl :=
  inl_ : forall a b, C a (bif a b).

(** Injection into the right component. *)
Class CoprodInr :=
  inr_ : forall a b, C b (bif a b).

(* Like [id_], the underscores avoid confusion with the names
   from the stdlib (where [case] is a tactic.) *)

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

(** **** Symmetry *)

Class Swap :=
  swap : forall a b, C (bif a b) (bif b a).

End CocartesianOps.

Arguments bimap {obj C bif Bimap a b c d}.
Arguments case_ {obj C bif CoprodCase a b c}.
Arguments inl_ {obj C bif CoprodInl a b}.
Arguments inr_ {obj C bif CoprodInr a b}.
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
           {Id_C : Id_ C} {Coproduct_C : CoprodCase C bif}
  : forall {a : obj}, C (bif a a) a :=
  fun a => case_ (id_ a) (id_ a).

(** **** Cocartesian category *)

(** The coproduct defines a symmetric monoidal category,
    called a _cocartesian category_. *)

Section CocartesianConstruct.

Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).
Variables (SUM : binop obj) (Coprod_SUM : CoprodCase C SUM)
          (CoprodInl_SUM : CoprodInl C SUM)
          (CoprodInr_SUM : CoprodInr C SUM).

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
  {CoprodCase_bif : CoprodCase C bif}
  {CoprodInl_bif : CoprodInl C bif}
  {CoprodInr_bif : CoprodInr C bif}
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
Context `{CoprodCase _ C bif} `{CoprodInl _ C bif} `{CoprodInr _ C bif}.

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
