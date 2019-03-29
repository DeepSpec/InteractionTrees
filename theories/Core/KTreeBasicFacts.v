(* begin hide *)
From Coq Require Import
     Morphisms.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Core.KTree
     Eq.UpToTausEquivalence.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree_scope.
Local Open Scope cat_scope.
Local Opaque paco2.
(* end hide *)

Global Instance Equivalence_eq_ktree {E A B} : @Equivalence (ktree E A B) eq2.
Proof.
  split.
  - intros ab a; reflexivity.
  - intros ab ab' eqAB a; symmetry; auto.
  - intros ab ab' ab'' eqAB eqAB' a; etransitivity; eauto.
Qed.

(* Facts about [loop] *)

Notation loop_once_ f loop_ :=
  (loop_once f (fun cb => Tau (loop_ f%function cb))).

Lemma unfold_loop'' {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    observe (loop_ f x)
  = observe (loop_once f (fun cb => Tau (loop_ f cb)) x).
Proof. reflexivity. Qed.

Lemma unfold_loop' {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    loop_ f x
  ≅ loop_once f (fun cb => Tau (loop_ f cb)) x.
Proof.
  rewrite itree_eta, (itree_eta (loop_once _ _ _)).
  reflexivity.
Qed.

Lemma unfold_loop {E A B C} (f : C + A -> itree E (C + B)) (x : C + A) :
    loop_ f x
  ≈ loop_once f (loop_ f) x.
Proof.
  rewrite unfold_loop'.
  apply eutt_bind; try reflexivity.
  intros []; try reflexivity.
  rewrite tau_eutt; reflexivity.
Qed.
