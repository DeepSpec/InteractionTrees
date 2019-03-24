(** * Simplified interface *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ITree Require Import
     Eq.Shallow.
(* end hide *)

(** ** Core definitions *)

(** Reexported from the library. *)

Require Export ITree.Core.ITreeDefinition.
Import ITreeNotations.
Open Scope itree_scope.
(**
   - [itree : (Type -> Type) -> Type -> Type] type
   - [Ret], [Tau], [Vis] notations
   - [ITree.bind : itree E R -> (R -> itree E S) -> itree E S]
   - [ITree.map : (R -> S) -> itree E R -> itree E S]
   - [ITree.send : E R -> itree E R]
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
   - [send_inl1 : D ~> itree (D +' E)]
   - [rec : (A -> itree (callE A B +' E) B -> A -> itree E B]
     and the notation [rec-fix]
   - [call : A -> itree (callE A B +' E) B]
 *)

Require ITree.Interp.Handler.
Export ITree.Interp.Handler.Handler.
(** Combinators for effect handlers:

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

(** The standard [itree] equivalence: "Equivalence Up To Taus",
    or _weak bisimulation_. *)
Parameter eutt : itree E R -> itree E R -> Prop.

Infix "≈" := eutt (at level 40).

(** [eutt] is an equivalence relation. *)
Global Declare Instance Equivalence_eutt :
    Equivalence eutt.

(** We can erase taus unter [eutt]. *)
Parameter tau_eutt : forall (t : itree E R),
    Tau t ≈ t.

Parameter itree_eta : forall (t : itree E R),
    t ≈ go (observe t).

Parameter eutt_ret : forall (r1 r2 : R),
    Ret r1 ≈ Ret r2 <-> r1 = r2.

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
Parameter bind_ret : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.

Parameter bind_vis
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).

Parameter bind_ret2 : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.

Parameter bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).

Hint Rewrite @tau_eutt : itree.
Hint Rewrite @bind_ret : itree.
Hint Rewrite @bind_vis : itree.
Hint Rewrite @bind_ret2 : itree.
Hint Rewrite @bind_bind : itree.

(** *** Monadic interpretation: [interp] *)

Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R
  := match ot with
     | RetF r => Ret r
     | TauF t => Tau (interp f t)
     | VisF e k => Tau (f _ e >>= (fun x => interp f (k x)))
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
  ≈ Tau (ITree.bind (f _ e) (fun x => interp f (k x))).

Parameter interp_send : forall {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F)) (e : E R),
    interp f (ITree.send e) ≈ f _ e.

Parameter interp_bind : forall {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S),
    interp f (ITree.bind t k)
  ≈ ITree.bind (interp f t) (fun r => interp f (k r)).

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_send : itree.
Hint Rewrite @interp_bind : itree.

(** *** Simple recursion: [rec] *)

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B)
  : (callE A B +' E) ~> itree E
  := case_ (calling' (rec f)) ITree.send.

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
  case_ (mrec f) ITree.send.

Parameter mrec_as_interp
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    mrec ctx d
  ≈ interp (mrecursive ctx) (ctx _ d).

Parameter interp_mrecursive
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    interp (mrecursive ctx) (send_inl1 d)
  ≈ mrec ctx d.

Hint Rewrite @interp_recursive_call : itree.
Hint Rewrite @interp_mrecursive : itree.

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

From ITree Require
     Eq.UpToTausEquivalence
     Interp.InterpFacts
     Interp.RecursionFacts.

Module Export Simple.
(** This interface is implemented by the module
    [ITree.Simple.Simple] below. *)

Section EquivalenceUpToTaus.

Context {E : Type -> Type} {R : Type}.

(** The standard [itree] equivalence: "Equivalence Up To Taus",
    or _weak bisimulation_. *)
Definition eutt : itree E R -> itree E R -> Prop :=
  ITree.Eq.UpToTaus.eutt eq.

Infix "≈" := eutt (at level 40).

(** [eutt] is an equivalence relation. *)
Global Existing Instance ITree.Eq.UpToTausEquivalence.Equivalence_eutt.

(** We can erase taus unter [eutt]. *)
Lemma tau_eutt : forall (t : itree E R),
    Tau t ≈ t.
Proof. exact ITree.Eq.UpToTausCore.tau_eutt. Qed.

Lemma itree_eta : forall (t : itree E R),
    t ≈ go (observe t).
Proof.
  intros; rewrite <- ITree.Eq.Eq.itree_eta.
  reflexivity.
Qed.

Lemma eutt_ret : forall (r1 r2 : R),
    Ret r1 ≈ Ret r2 <-> r1 = r2.
Proof. apply ITree.Eq.UpToTausCore.eutt_ret. Qed.

Lemma eutt_vis : forall {U : Type} (e : E U) (k1 k2 : U -> itree E R),
    (forall u, k1 u ≈ k2 u) <-> Vis e k1 ≈ Vis e k2.
Proof. apply ITree.Eq.UpToTausCore.eutt_vis. Qed.

End EquivalenceUpToTaus.

Infix "≈" := eutt (at level 40).

(** *** Rewriting lemmas *)

Lemma unfold_bind
  : forall {E R S} (t : itree E R) (k : R -> itree E S),
    ITree.bind t k
  ≈ ITree._bind k (fun t => ITree.bind t k) (observe t).
Proof. intros; rewrite <- ITree.Eq.Shallow.unfold_bind; reflexivity. Qed.

(** The next two are immediate corollaries of [unfold_bind]. *)
Lemma bind_ret : forall {E R S} (r : R) (k : R -> itree E S),
    ITree.bind (Ret r) k ≈ k r.
Proof. intros; rewrite ITree.Eq.Shallow.bind_ret; reflexivity. Qed.

Lemma bind_vis
  : forall {E R} U V (e: E V) (ek: V -> itree E U) (k: U -> itree E R),
    ITree.bind (Vis e ek) k
  ≈ Vis e (fun x => ITree.bind (ek x) k).
Proof. intros; rewrite ITree.Eq.Shallow.bind_vis; reflexivity. Qed.

Lemma bind_ret2 : forall {E R} (s : itree E R),
    ITree.bind s (fun x => Ret x) ≈ s.
Proof. intros; rewrite ITree.Eq.Eq.bind_ret2; reflexivity. Qed.

Lemma bind_bind
  : forall {E R S T}
           (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h
  ≈ ITree.bind s (fun r => ITree.bind (k r) h).
Proof. intros; rewrite ITree.Eq.Eq.bind_bind; reflexivity. Qed.

Hint Rewrite @tau_eutt : itree.
Hint Rewrite @bind_ret : itree.
Hint Rewrite @bind_tau : itree.
Hint Rewrite @bind_vis : itree.
Hint Rewrite @bind_ret2 : itree.
Hint Rewrite @bind_bind : itree.

(** **** Monadic interpretation: [interp] *)

Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R
  := match ot with
     | RetF r => Ret r
     | TauF t => Tau (interp f t)
     | VisF e k => Tau (f _ e >>= (fun x => interp f (k x)))
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
  ≈ Tau (ITree.bind (f _ e) (fun x => interp f (k x))).
Proof.
  intros; rewrite unfold_interp; reflexivity.
Qed.

Lemma interp_send : forall {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F)) (e : E R),
    interp f (ITree.send e) ≈ f _ e.
Proof.
  intros; rewrite ITree.Interp.InterpFacts.interp_send, tau_eutt.
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

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_send : itree.
Hint Rewrite @interp_bind : itree.

(** **** Simple recursion: [rec] *)

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive {E A B} (f : A -> itree (callE A B +' E) B)
  : (callE A B +' E) ~> itree E
  := case_ (calling' (rec f)) ITree.send.

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
  intros. rewrite ITree.Interp.RecursionFacts.interp_recursive_call. apply tau_eutt.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive {D E} (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.send.

Lemma mrec_as_interp
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    mrec ctx d
  ≈ interp (mrecursive ctx) (ctx _ d).
Proof.
  intros; rewrite ITree.Interp.RecursionFacts.mrec_as_interp. reflexivity.
Qed.

Lemma interp_mrecursive
  : forall {D E T} (ctx : D ~> itree (D +' E)) (d : D T),
    interp (mrecursive ctx) (send_inl1 d)
  ≈ mrec ctx d.
Proof.
  intros; rewrite ITree.Interp.RecursionFacts.interp_mrecursive. apply tau_eutt.
Qed.

Hint Rewrite @interp_recursive_call : itree.
Hint Rewrite @interp_mrecursive : itree.

(** *** [Proper] lemmas *)

Instance eutt_go {E R} :
  Proper (going eutt ==> eutt) (@go E R).
Proof. apply ITree.Eq.UpToTausCore.eutt_cong_go. Qed.

Instance eutt_observe {E R} :
  Proper (eutt ==> going eutt) (@observe E R).
Proof. apply ITree.Eq.UpToTausCore.eutt_cong_observe. Qed.

Instance eutt_TauF {E R} :
  Proper (eutt ==> going eutt) (@TauF E R _).
Proof. apply ITree.Eq.UpToTausCore.eutt_cong_tauF. Qed.

Instance eutt_VisF {E R X} (e: E X) :
  Proper (pointwise_relation _ (@eutt E R) ==> going eutt) (VisF e).
Proof. apply ITree.Eq.UpToTausCore.eutt_cong_VisF. Qed.

Instance eutt_bind {E R S} :
  Proper (pointwise_relation _ eutt ==> eutt ==> eutt)
         (@ITree.bind' E R S).
Proof. apply ITree.Eq.UpToTausEquivalence.eutt_bind. Qed.

Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt ==> eutt)
         (@ITree.map E R S).
Proof. apply ITree.Eq.UpToTausEquivalence.eutt_map. Qed.

Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt ==> eutt) (@interp E (itree F) _ _ _ f R).
Proof. apply ITree.Interp.InterpFacts.eutt_interp'. Qed.

Ltac tau_steps :=
  repeat (
      rewrite itree_eta at 1; cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] => fail 1
      | _ => try rewrite tau_eutt
      end).

End Simple.
(* end hide *)
