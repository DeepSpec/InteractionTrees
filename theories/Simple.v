(** * Simplified interface *)

(* begin hide *)
Set Warnings "-notation-overridden".

From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Eq.Shallow.
(* end hide *)

(** ** Core definitions *)

(** Reexported from the library. *)

Require Export ITree.Core.ITreeDefinition.
Export ITreeNotations.
#[global] Open Scope itree_scope.
(* This scope is open by default to make this "tutorial module" as
   straightforward as possible. *)

(**
   - [itree : (Type -> Type) -> Type -> Type] type
   - [Ret], [Tau], [Vis] notations
   - [ITree.bind : itree E R -> (R -> itree E S) -> itree E S]
   - [ITree.map : (R -> S) -> itree E R -> itree E S]
   - [ITree.trigger : E R -> itree E R]
   - Notations for [bind t k]: ["t >>= k"], ["x <- t ;; k x"]
 *)

(** The main functions are meant to be imported qualified, e.g., [ITree.bind],
    [ITree.trigger], to avoid ambiguity with identifiers of the same
    name (some of which are overloaded generalizations of these).
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
   - [trigger_inl1 : D ~> itree (D +' E)]
   - [rec : (A -> itree (callE A B +' E) B -> A -> itree E B]
     and the notation [rec-fix]
   - [call : A -> itree (callE A B +' E) B]
 *)

Require ITree.Interp.Handler.
Export ITree.Interp.Handler.Handler.
(** Combinators for event handlers:

   - [case_ : (E ~> itree G) -> (F ~> itree G) -> (E +' F ~> itree G)]
   - [bimap : (E ~> itree G) -> (F ~> itree H) -> (E +' F ~> itree (G +' H))]
   - [inl1_ : E ~> itree (E +' F)]
   - [inr1_ : F ~> itree (E +' F)]
   - [cat : (E ~> itree F) -> (F ~> itree G) -> (E ~> itree G)]
 *)

(** ** Equational theory *)

Module Type SimpleTheory.
(** This interface is implemented by the module
    [ITree.Simple.Simple] below (exported by default). *)

Section EquivalenceUpToTaus.

Context {E : Type -> Type} {R : Type}.

(** The standard [itree] equivalence: "Equivalence Up To Taus"
    ([eutt] for short), or _weak bisimulation_. *)
Parameter eutt : itree E R -> itree E R -> Prop.

Infix "≈" := eutt (at level 70) : type_scope.

(** [eutt] is an equivalence relation. *)
#[global] Declare Instance Equivalence_eutt :
    Equivalence eutt.

(** We can erase taus unter [eutt]. *)
Parameter tau_eutt : forall (t : itree E R),
    Tau t ≈ t.

Parameter itree_eta : forall (t : itree E R),
    t ≈ go (observe t).

Parameter eutt_ret : forall (r1 r2 : R),
    r1 = r2 -> Ret r1 ≈ Ret r2.

Parameter eutt_vis : forall {U : Type} (e : E U) (k1 k2 : U -> itree E R),
    (forall u, k1 u ≈ k2 u) -> Vis e k1 ≈ Vis e k2.

Parameter eutt_inv_ret : forall (r1 r2 : R),
    Ret r1 ≈ Ret r2 -> r1 = r2.

Parameter eutt_inv_vis : forall {U : Type} (e : E U) (k1 k2 : U -> itree E R),
     Vis e k1 ≈ Vis e k2 -> (forall u, k1 u ≈ k2 u).

End EquivalenceUpToTaus.

Infix "≈" := eutt (at level 70).

(** *** Rewriting lemmas *)

Parameter bind_ret : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.

Parameter bind_vis
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).

Parameter bind_ret_r : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.

Parameter bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).

#[global] Hint Rewrite @tau_eutt : itree.
#[global] Hint Rewrite @bind_ret : itree.
#[global] Hint Rewrite @bind_vis : itree.
#[global] Hint Rewrite @bind_ret_r : itree.
#[global] Hint Rewrite @bind_bind : itree.

(** *** Monadic interpretation: [interp] *)

Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R
  := match ot with
     | RetF r => Ret r
     | TauF t => Tau (interp f t)
     | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
     end.

Parameter unfold_interp
  : forall {E F R} {f : E ~> itree F} (t : itree E R),
    interp f t ≈ (_interp f (observe t)).

(** The next three are immediate corollaries of [unfold_interp]. *)
Parameter interp_ret
  : forall {E F R} {f : E ~> itree F} (x: R),
    interp f (Ret x) ≈ Ret x.

Parameter interp_vis
  : forall {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R),
    interp f (Vis e k)
  ≈ ITree.bind (f _ e) (fun x => interp f (k x)).

Parameter interp_trigger : forall {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F)) (e : E R),
    interp f (ITree.trigger e) ≈ f _ e.

Parameter interp_bind : forall {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S),
    interp f (ITree.bind t k)
  ≈ ITree.bind (interp f t) (fun r => interp f (k r)).

#[global] Hint Rewrite @interp_ret : itree.
#[global] Hint Rewrite @interp_vis : itree.
#[global] Hint Rewrite @interp_trigger : itree.
#[global] Hint Rewrite @interp_bind : itree.

(** *** Simple recursion: [rec] *)

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B)
  : (callE A B +' E) ~> itree E
  := case_ (calling' (rec f)) ITree.trigger.

Parameter rec_as_interp
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (a : A),
    rec f a
  ≈ interp (recursive f) (f a).

Parameter interp_recursive_call
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (x : A),
    interp (recursive f) (call x)
  ≈ rec f x.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive {D E} (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.trigger.

Parameter mrec_as_interp
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    mrec ctx d
  ≈ interp (mrecursive ctx) (ctx _ d).

Parameter interp_mrecursive
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    interp (mrecursive ctx) (trigger_inl1 d)
  ≈ mrec ctx d.

#[global] Hint Rewrite @interp_recursive_call : itree.
#[global] Hint Rewrite @interp_mrecursive : itree.

(** *** [Proper] lemmas *)

#[global]
Declare Instance eutt_go {E R} :
  Proper (going eutt ==> eutt) (@go E R).

#[global]
Declare Instance eutt_observe {E R} :
  Proper (eutt ==> going eutt) (@observe E R).

#[global]
Declare Instance eutt_TauF {E R} :
  Proper (eutt ==> going eutt) (@TauF E R _).

#[global]
Declare Instance eutt_VisF {E R X} (e: E X) :
  Proper (pointwise_relation _ (@eutt E R) ==> going eutt) (VisF e).

#[global]
Declare Instance eutt_bind {E R S} :
  Proper (eutt ==> pointwise_relation _ eutt ==> eutt)
         (@ITree.bind E R S).

#[global]
Declare Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt ==> eutt)
         (@ITree.map E R S).

#[global]
Declare Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt ==> eutt) (@interp E (itree F) _ _ _ f R).

(** *** Tactics *)

(** Remove all taus from the left hand side of the goal
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps :=
  repeat (
      rewrite itree_eta at 1; cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] => fail 1
      | _ => try rewrite tau_eutt
      end).

End SimpleTheory.

(* begin hide *)
(** * Implementation *)

From ITree Require Import
     Eq.Eqit
     Eq.UpToTaus
     Interp.InterpFacts
     Interp.RecursionFacts.

Module Export Simple : SimpleTheory.
(** This interface is implemented by the module
    [ITree.Simple.Simple] below. *)

Section EquivalenceUpToTaus.

Context {E : Type -> Type} {R : Type}.

(** The standard [itree] equivalence: "Equivalence Up To Taus",
    or _weak bisimulation_. *)
Definition eutt : itree E R -> itree E R -> Prop :=
  ITree.Eq.Eqit.eutt eq.

Notation "x ≈ y" := (eutt x y) (at level 70) : type_scope.

(** [eutt] is an equivalence relation. *)
Global Instance Equivalence_eutt : Equivalence eutt.
Proof.
  apply ITree.Eq.Eqit.Equivalence_eutt. econstructor; eauto using trans_eq. 
Qed.

(** We can erase taus unter [eutt]. *)
Lemma tau_eutt : forall (t : itree E R),
    Tau t ≈ t.
Proof. intros. rewrite ITree.Eq.Eqit.tau_eutt. reflexivity. Qed.

Lemma itree_eta : forall (t : itree E R),
    t ≈ go (observe t).
Proof. intros. rewrite <- ITree.Eq.Eqit.itree_eta. reflexivity. Qed.

Lemma eutt_ret (r1 r2 : R)
  : r1 = r2 -> Ret r1 ≈ Ret r2.
Proof. intros. subst. reflexivity. Qed.

Lemma eutt_vis {U : Type} (e : E U) (k1 k2 : U -> itree E R)
  : (forall u, k1 u ≈ k2 u) -> Vis e k1 ≈ Vis e k2.
Proof.
  intros. ITree.Eq.UpToTaus.einit. ITree.Eq.UpToTaus.evis.
  intros. ITree.Eq.UpToTaus.efinal. apply H.
Qed.

Lemma eutt_inv_ret (r1 r2 : R)
  : Ret r1 ≈ Ret r2 ->
    r1 = r2.
Proof. apply ITree.Eq.Eqit.eqit_inv_Ret. Qed.

Lemma eutt_inv_vis {U : Type} (e : E U) (k1 k2 : U -> itree E R)
  : Vis e k1 ≈ Vis e k2 ->
    (forall u, k1 u ≈ k2 u).
Proof. apply ITree.Eq.Eqit.eqit_inv_Vis; auto. Qed.

End EquivalenceUpToTaus.

Infix "≈" := eutt (at level 70).

(** *** Rewriting lemmas *)

Lemma bind_ret : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.
Proof. intros; rewrite ITree.Eq.Shallow.bind_ret_; reflexivity. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  ITree.bind (Tau t) k ≈ Tau (ITree.bind t k).
Proof. rewrite bind_tau_. reflexivity. Qed.

Lemma bind_vis
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).
Proof. intros; rewrite ITree.Eq.Shallow.bind_vis_; reflexivity. Qed.

Lemma bind_ret_r : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.
Proof. intros; rewrite ITree.Eq.Eqit.bind_ret_r; reflexivity. Qed.

Lemma bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).
Proof. intros; rewrite ITree.Eq.Eqit.bind_bind; reflexivity. Qed.

#[global] Hint Rewrite @tau_eutt : itree.
#[global] Hint Rewrite @bind_ret : itree.
#[global] Hint Rewrite @bind_tau : itree.
#[global] Hint Rewrite @bind_vis : itree.
#[global] Hint Rewrite @bind_ret_r : itree.
#[global] Hint Rewrite @bind_bind : itree.

(** **** Monadic interpretation: [interp] *)

Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R
  := match ot with
     | RetF r => Ret r
     | TauF t => Tau (interp f t)
     | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
     end.

Lemma unfold_interp
  : forall {E F R} {f : E ~> itree F} (t : itree E R),
    interp f t ≈ (_interp f (observe t)).
Proof.
  intros; rewrite <- ITree.Interp.InterpFacts.unfold_interp.
  reflexivity.
Qed.

(** The next two are immediate corollaries of [unfold_interp]. *)
Lemma interp_ret
  : forall {E F R} {f : E ~> itree F} (x: R),
    interp f (Ret x) ≈ Ret x.
Proof.
  intros; rewrite unfold_interp; reflexivity.
Qed.

Lemma interp_vis
  : forall {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R),
    interp f (Vis e k)
  ≈ ITree.bind (f _ e) (fun x => interp f (k x)).
Proof.
  intros; rewrite InterpFacts.interp_vis; setoid_rewrite tau_eutt; reflexivity.
Qed.

Lemma interp_trigger : forall {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F)) (e : E R),
    interp f (ITree.trigger e) ≈ f _ e.
Proof.
  intros; rewrite ITree.Interp.InterpFacts.interp_trigger.
  reflexivity.
Qed.

Lemma interp_bind : forall {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S),
    interp f (ITree.bind t k)
  ≈ ITree.bind (interp f t) (fun r => interp f (k r)).
Proof.
  intros; rewrite ITree.Interp.InterpFacts.interp_bind.
  reflexivity.
Qed.

#[global] Hint Rewrite @interp_ret : itree.
#[global] Hint Rewrite @interp_vis : itree.
#[global] Hint Rewrite @interp_trigger : itree.
#[global] Hint Rewrite @interp_bind : itree.

(** **** Simple recursion: [rec] *)

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B)
  : (callE A B +' E) ~> itree E
  := case_ (calling' (rec f)) ITree.trigger.

Lemma rec_as_interp
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (a : A),
    rec f a
  ≈ interp (recursive f) (f a).
Proof.
  intros. rewrite ITree.Interp.RecursionFacts.rec_as_interp. reflexivity.
Qed.

Lemma interp_recursive_call
  : forall {E A B} (f : A -> itree (callE A B +' E) B) (x : A),
    interp (recursive f) (call x)
  ≈ rec f x.
Proof.
  intros. rewrite ITree.Interp.RecursionFacts.interp_recursive_call.
  reflexivity.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive {D E} (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.trigger.

Lemma mrec_as_interp
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    mrec ctx d
  ≈ interp (mrecursive ctx) (ctx _ d).
Proof.
  intros; rewrite ITree.Interp.RecursionFacts.mrec_as_interp. reflexivity.
Qed.

Lemma interp_mrecursive
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    interp (mrecursive ctx) (trigger_inl1 d)
  ≈ mrec ctx d.
Proof.
  intros; rewrite ITree.Interp.RecursionFacts.interp_mrecursive.
  reflexivity.
Qed.

#[global] Hint Rewrite @interp_recursive_call : itree.
#[global] Hint Rewrite @interp_mrecursive : itree.

(** *** [Proper] lemmas *)

#[global] Instance eutt_go {E R} :
  Proper (going eutt ==> eutt) (@go E R).
Proof. repeat red; intros. rewrite H. apply reflexivity. Qed.

#[global] Instance eutt_observe {E R} :
  Proper (eutt ==> going eutt) (@observe E R).
Proof. repeat red; intros. rewrite H. apply reflexivity. Qed.

#[global] Instance eutt_TauF {E R} :
  Proper (eutt ==> going eutt) (@TauF E R _).
Proof. repeat red; intros. rewrite H. apply reflexivity. Qed.

#[global] Instance eutt_VisF {E R X} (e: E X) :
  Proper (pointwise_relation _ (@eutt E R) ==> going eutt) (VisF e).
Proof. repeat red; intros. rewrite H. apply reflexivity. Qed.

#[global] Instance eutt_bind {E R S} :
  Proper (eutt ==> pointwise_relation _ eutt ==> eutt)
         (@ITree.bind E R S).
Proof. repeat red; intros. rewrite H, H0. apply reflexivity. Qed.

#[global] Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt ==> eutt)
         (@ITree.map E R S).
Proof. repeat red; intros. rewrite H, H0. apply reflexivity. Qed.

#[global] Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt ==> eutt) (@interp E (itree F) _ _ _ f R).
Proof. repeat red; intros. rewrite H. apply reflexivity. Qed.

End Simple.
(* end hide *)
