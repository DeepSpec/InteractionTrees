(** * Simplified interface *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require
     Core.ITree
     Eq.UpToTaus.

From ITree Require Import
     Eq.Shallow.

Set Primitive Projections.
(* end hide *)

(** This is implemented by the (opaque) module
    [ITree.Simple.Simple]. *)
Module Type SimpleInterface.

(** ** Core definitions *)
Include ITree.Core.ITree.

(** ** Equational theory *)

Section General.

Context {E : Type -> Type} {R : Type}.

(** The standard [itree] equivalence: "Equivalence Up To Taus",
    or _weak bisimulation_. *)
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

End SimpleInterface.

(** * Implementation *)

(* TODO: implement *)

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
