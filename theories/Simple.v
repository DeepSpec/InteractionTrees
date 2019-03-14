(** * Simplified interface *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Basics.Category
     Basics.Basics
     Eq.Shallow.
(* end hide *)

(** ** Core definitions *)

(** Reexported from the library. *)

Require Export ITree.Core.ITree.
Import ITreeNotations.
Open Scope itree_scope.
(**
   - [itree : (Type -> Type) -> Type -> Type] type
   - [Ret], [Tau], [Vis] notations
   - [ITree.bind : itree E R -> (R -> itree E S) -> itree E S]
   - [ITree.map : (R -> S) -> itree E R -> itree E S]
   - [ITree.lift : E R -> itree E R]
   - Notations for [bind t k]: ["t >>= k"], ["x <- t ;; k x"]
 *)

(** Indexed types *)
Require Export ITree.Basics.Basics.
(**
   - Notation ["E ~> F" := (forall T, E T -> F T)]
 *)

Require Export ITree.Indexed.Sum.
(**
   - [sum1] ([_ +' _]), [inl1 : E ~> E +' F], [inr1 : F ~> E +' F]
   - [void1] (empty type)
 *)

(** ** Interpreters, handlers *)

Require Export ITree.Interp.Interp.
(**
   - [interp : (E ~> itree F) -> (itree E ~> itree F)]
 *)

Require Export ITree.Interp.Recursion.
(**
   - [mrec : (D ~> itree (D +' E)) -> (D ~> itree E)]
     and the notation [mrec-fix]
   - [lift_inl1 : D ~> itree (D +' E)]
   - [rec : (A -> itree (callE A B +' E) B -> A -> itree E B]
     and the notation [rec-fix]
   - [call : A -> itree (callE A B +' E) B]
 *)

(** We compose _effect handlers_ [E ~> itree F] using a set of
    general-purpose combinators from this little category theory
    library. *)

Require Export ITree.Basics.Category.
(** Types specialized to effect handlers:

   - [case_ : (E ~> itree G) -> (F ~> itree G) -> (E +' F ~> itree G)]
   - [bimap : (E ~> itree G) -> (F ~> itree H) -> (E +' F ~> itree (G +' H))]
   - [inl1_ : E ~> itree (E +' F)]
   - [inr1_ : F ~> itree (E +' F)]
   - [cat : (E ~> itree F) -> (F ~> itree G) -> (E ~> itree G)]
     (also denoted [>=>])
 *)

(** ** Equational theory *)

Module Type SimpleInterface.
(** This interface is implemented by the module
    [ITree.Simple.Simple] below. *)

Section EquivalenceUpToTaus.

Context {E : Type -> Type} {R : Type}.

(** The standard [itree] equivalence: "Equivalence Up To Taus",
    or _weak bisimulation_. *)
Parameter eutt : itree E R -> itree E R -> Prop.

Infix "≈" := eutt (at level 40).

(** [eutt] is an equivalence relation. *)
Global Declare Instance Equivalence_eutt :
    Equivalence eutt.

(** We can erase taus unter [eutt]. *)
Parameter eutt_tau : forall (t : itree E R),
    Tau t ≈ t.

Parameter itree_eta : forall (t : itree E R),
    t ≈ go (observe t).

Parameter eutt_ret : forall (r1 r2 : R),
    r1 = r2 <-> Ret r1 ≈ Ret r2.

Parameter eutt_vis : forall {U : Type} (e : E U) (k1 k2 : U -> itree E R),
    (forall u, k1 u ≈ k2 u) <-> Vis e k1 ≈ Vis e k2.

End EquivalenceUpToTaus.

Infix "≈" := eutt (at level 40).

(** *** Rewriting lemmas *)

Parameter unfold_bind
  : forall {E R S} (t : itree E R) (k : R -> itree E S),
    ITree.bind t k
  ≈ ITree._bind k (fun t => ITree.bind t k) (observe t).

(** The next two are immediate corollaries of [unfold_bind]. *)
Parameter ret_bind : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.

Parameter vis_bind
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).

Parameter bind_ret : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.

Parameter bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).

Hint Rewrite @eutt_tau : itree.
Hint Rewrite @ret_bind : itree.
Hint Rewrite @tau_bind : itree.
Hint Rewrite @vis_bind : itree.
Hint Rewrite @bind_ret : itree.
Hint Rewrite @bind_bind : itree.

(** **** Monadic interpretation: [interp] *)

Definition _interp {E F} (f : E ~> itree F) R (ot : itreeF E R _)
  : itree F R
  := match ot with
     | RetF r => Ret r
     | TauF t => Tau (interp f _ t)
     | VisF e k => Tau (f _ e >>= (fun x => interp f _ (k x)))
     end.

Parameter unfold_interp
  : forall {E F R} {f : E ~> itree F} (t : itree E R),
    interp f _ t ≈ (_interp f _ (observe t)).

(** The next three are immediate corollaries of [unfold_interp]. *)
Parameter ret_interp
  : forall {E F R} {f : E ~> itree F} (x: R),
    interp f _ (Ret x) ≈ Ret x.

Parameter vis_interp
  : forall {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R),
    interp f _ (Vis e k)
  ≈ Tau (ITree.bind (f _ e) (fun x => interp f _ (k x))).

Parameter interp_lift : forall {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F)) (e : E R),
    interp f _ (ITree.lift e) ≈ f _ e.

Parameter interp_bind : forall {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S),
    interp f _ (ITree.bind t k)
  ≈ ITree.bind (interp f _ t) (fun r => interp f _ (k r)).

(** **** Simple recursion: [rec] *)

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B)
  : (callE A B +' E) ~> itree E
  := case_ (calling' (rec f)) ITree.lift.

Parameter rec_as_interp
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (a : A),
    rec f a
  ≈ interp (recursive f) _ (f a).

Parameter interp_recursive_call
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (x : A),
    interp (recursive f) _ (call x)
  ≈ rec f x.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive {D E} (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.lift.

Parameter mrec_as_interp
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    mrec ctx _ d
  ≈ interp (mrecursive ctx) _ (ctx _ d).

Parameter interp_mrecursive
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    interp (mrecursive ctx) _ (lift_inl1 _ d)
  ≈ mrec ctx _ d.

(** *** [Proper] lemmas *)

Declare Instance eutt_go {E R} :
  Proper (going eutt ==> eutt) (@go E R).

Declare Instance eutt_observe {E R} :
  Proper (eutt ==> going eutt) (@observe E R).

Declare Instance eutt_TauF {E R} :
  Proper (eutt ==> going eutt) (@TauF E R _).

Declare Instance eutt_VisF {E R X} (e: E X) :
  Proper (pointwise_relation _ (@eutt E R) ==> going eutt) (VisF e).

Declare Instance eutt_bind {E R S} :
  Proper (pointwise_relation _ eutt ==> eutt ==> eutt)
         (@ITree.bind' E R S).

Declare Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt ==> eutt)
         (@ITree.map E R S).

Declare Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt ==> eutt) (@interp E F f R).

End SimpleInterface.

(** * Implementation *)

(* TODO: implement *)
(*
Module Import Simple : SimpleInterface.

Include ITree.Core.ITree.

Section General.

Context {E : Type -> Type} {R : Type}.

Parameter eutt : itree E R -> itree E R -> Prop.

Infix "≈" := eutt (at level 40).

Global Declare Instance Equivalence_eutt :
    Equivalence eutt.

Parameter itree_eta : forall (t : itree E R),
    t ≈ go (observe t).

Parameter tau_eutt : forall (t : itree E R),
    Tau t ≈ t.

Parameter eutt_ret : forall (r1 r2 : R),
    r1 = r2 <-> Ret r1 ≈ Ret r2.

Parameter eutt_vis : forall {U : Type} (e : E U) (k1 k2 : U -> itree E R),
    (forall u, k1 u ≈ k2 u) <-> Vis e k1 ≈ Vis e k2.

Global Declare Instance eutt_go :
  Proper (going eutt ==> eutt) (@go E R).

Global Declare Instance eutt_observe :
  Proper (eutt ==> going eutt) (@observe E R).

Global Declare Instance eutt_TauF :
  Proper (eutt ==> going eutt) (@TauF E R _).

Global Declare Instance eutt_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).

End General.

Infix "≈" := eutt (at level 40).

Parameter unfold_bind
  : forall {E R S} (t : itree E R) (k : R -> itree E S),
    ITree.bind t k
  ≈ ITree._bind k (fun t => ITree.bind t k) (observe t).

Parameter ret_bind : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.

Parameter tau_bind : forall {E R} U t (k: U -> itree E R),
    ITree.bind (Tau t) k ≈ Tau (ITree.bind t k).

Parameter vis_bind
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).

Parameter bind_ret : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.

Parameter bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).

Hint Rewrite @ret_bind : itree.
Hint Rewrite @tau_bind : itree.
Hint Rewrite @vis_bind : itree.
Hint Rewrite @bind_ret : itree.
Hint Rewrite @bind_bind : itree.

Declare Instance eutt_bind {E R S} :
  Proper (eutt ==> pointwise_relation _ eutt ==> eutt)
         (@ITree.bind E R S).

Declare Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt ==> eutt)
         (@ITree.map E R S).

Parameter unfold_aloop
  : forall {E A B} (f : A -> itree E A + B) (x : A),
    ITree.aloop f x
  ≈ ITree._aloop id (ITree.aloop f) (f x).

End Simple.
*)
