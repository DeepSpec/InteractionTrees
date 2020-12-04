(** * Extensible effects *)

(** Notations to handle large sums and classes for extensible effects. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Indexed.Function.
(* end hide *)

(** Automatic application of commutativity and associativity for
    sums types constructed with [sum1].

    N.B. This is prone to infinite instance resolution loops.
    Put the following option at the top of your [.v] files to
    bound the instance search depth:

[[
  Typeclasses eauto := 5.
]]

    Higher numbers allow bigger instances but grow the search
    space exponentially.
 *)

Notation Subevent E F := (@ReSum (Type -> Type) IFun E F)
  (only parsing).
Notation "E -< F" := (Subevent E F)
  (at level 92, left associativity) : type_scope.

Definition subevent {E F : Type -> Type} `{E -< F} : E ~> F := resum _.

(** Notations to construct and pattern-match on nested sums. *)
Module Import SumNotations.

(*
  The following line removes the warning on >=8.10, but is incompatible for <8.10
 *)
(* Declare Scope sum_scope. *)
Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inr1 x) : sum_scope.
Notation "( x |)" := (inl1 x) : sum_scope.
Notation "(| x |)" := (inr1 (inl1 x)) : sum_scope.
Notation "(|| x )" := (inr1 (inr1 x)) : sum_scope.
Notation "(|| x |)" := (inr1 (inr1 (inl1 x))) : sum_scope.
Notation "(||| x )" := (inr1 (inr1 (inr1 x))) : sum_scope.
Notation "(||| x |)" := (inr1 (inr1 (inr1 (inl1 x)))) : sum_scope.
Notation "(|||| x )" := (inr1 (inr1 (inr1 (inr1 x)))) : sum_scope.
Notation "(|||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inl1 x))))) : sum_scope.
Notation "(||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 x))))) : sum_scope.
Notation "(||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))) : sum_scope.
Notation "(|||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x)))))) : sum_scope.
Notation "(|||||| x |)" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x))))))) : sum_scope.
Notation "(||||||| x )" :=
  (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x))))))) : sum_scope.

End SumNotations.

Local Open Scope sum_scope.

(** A polymorphic version of [Vis]. *)
Notation vis e k := (Vis (subevent _ e) k).

(* Called [send] in Haskell implementations of Freer monads. *)
Notation trigger e := (ITree.trigger (subevent _ e)).

(* Embedding events into trees.

   For example:
[[
   embed :
     (forall x y z,       E (f x y z)) ->
     (forall x y z, itree E (f x y z))
]]
 *)
Class Embeddable U V :=
  embed : U -> V.

Instance Embeddable_forall {A : Type} {U : A -> Type} {V : A -> Type}
         `(forall a, Embeddable (U a) (V a)) :
  Embeddable (forall a, U a) (forall a, V a) :=
  fun u a => embed (u a).

Instance Embeddable_itree {E F : Type -> Type} {R : Type}
         `(E -< F) :
  Embeddable (E R) (itree F R) :=
  fun e => trigger e.

(* Some rewriting lemmas sometimes expose [resum]. The following lemmas help reshape the goal properly *)
Lemma resum_to_subevent : forall (E F : Type -> Type) H T e,
    @resum _ IFun E F H T e = subevent _ e.
Proof.
  intros; reflexivity.
Qed.

Lemma subevent_subevent' : forall {E F} `{E -< F} {X} (e : E X),
    @subevent F F _ X (@subevent E F _ X e) = subevent X e.
Proof.
  reflexivity.
Qed.

Lemma subevent_subevent : forall {E F G :Type -> Type} (SEF: E -< F) (SFG: F -< G) T (e : E T),
    @subevent F G SFG T (@subevent E F SEF T e) =
    @subevent E G (fun x f => SFG _ (SEF _ f)) T e.
Proof.
  reflexivity.
Qed.
