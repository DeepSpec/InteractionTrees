(** This file is about the structure of itree morphisms induced by
    event morphisms via the [translate] operation defined herein.

    Translate should be defined separately from the Morphisms because it
    is conceptually at a different level and translation always yields
    strong bisimulations.  We can relate them via the law:

    translate h t ≈ interp (liftE ∘ h) t
 *)

From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics
     Core
     Effect.Sum
     OpenSum.

Open Scope itree_scope.

(** A plain effect morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {E F R} (h : E ~> F) (rec: itree E R -> itree F R) (t : itreeF E R _) : itree F R  :=
  match t with
  | RetF x => Ret x
  | TauF t => Tau (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

CoFixpoint translate {E F R} (h : E ~> F) (t : itree E R) : itree F R
  := translateF h (translate h) (observe t).

(* SAZ: Should be moved to TranslateFacts.v *)
(* translate facts ---------------------------------------------------------- *)
From ITree Require Import
     Eq
     UpToTaus.

From Paco Require Import paco.

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

Section TranslateFacts.
  Context {E F : Type -> Type}.
  Context {R : Type}.
  Context (h : E ~> F).

Lemma unfold_translate : forall (t : itree E R),
    observe (translate h t) = observe (translateF h (translate h) (observe t)).
Proof.
  intros t. reflexivity.
Qed.

Lemma translate_ret : forall (r:R), translate h (Ret r) ≅ Ret r.
Proof.
  intros r.
  rewrite itree_eta.
  rewrite unfold_translate. cbn. reflexivity.
Qed.

Lemma translate_tau : forall (t : itree E R), translate h (Tau t) ≅ Tau (translate h t).
Proof.
  intros t.
  rewrite itree_eta.
  rewrite unfold_translate. cbn. reflexivity.
Qed.

Lemma translate_vis : forall X (e:E X) (k : X -> itree E R),
    translate h (Vis e k) ≅ Vis (h _ e) (fun x => translate h (k x)).
Proof.
  intros X e k. 
  rewrite itree_eta.
  rewrite unfold_translate. cbn. reflexivity.
Qed.

Global Instance translate_Proper : Proper ( (eq_itree (@eq R)) ==> eq_itree eq) (translate h).
Proof.
  repeat red.
  intros x y H. 
  pupto2_init.
  revert x y H.
  pcofix CIH.
  intros x y H.
  rewrite itree_eta.
  rewrite (itree_eta (translate h y)).
  repeat rewrite unfold_translate. unfold translateF.
  rewrite (itree_eta x) in H.
  rewrite (itree_eta y) in H.
  destruct (observe x); destruct (observe y); pinversion H; subst; cbn.
  - pupto2_final. apply Reflexive_eq_itree. (* SAZ: typeclass resolution not working *)
  - pupto2_final. pfold. constructor.  right. apply CIH. eauto.
  - pupto2_final. pfold.
    repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
            end). subst.
    constructor.
    inversion H.
    repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
            end). subst. 
    right. apply CIH. 
    eapply transitivity. pclearbot. apply REL0. reflexivity.
Qed.
End TranslateFacts.

Lemma translate_bind : forall {E F R S} (h : E ~> F) (t : itree E S) (k : S -> itree E R),
    translate h (x <- t ;; k x) ≅ (x <- (translate h t) ;; translate h (k x)).
Proof.
  intros E F R S h t k. 
  pupto2_init.
  revert S t k.
  pcofix CIH.
  intros s t k.
  rewrite itree_eta.
  rewrite (itree_eta (x <- translate h t;; translate h (k x))).
  rewrite unfold_translate.  
  repeat rewrite bind_unfold.
  rewrite unfold_translate.
  unfold translateF.
  unfold ITree.bind_match.
  destruct (observe t); cbn.
  - rewrite unfold_translate. unfold translateF.
    pupto2_final. apply Reflexive_eq_itree.
  - pfold. econstructor. pupto2_final. right. apply CIH.
  - pfold. econstructor. intros.  pupto2_final. right.  apply CIH.
Qed.

(* categorical properties --------------------------------------------------- *)

Import Sum1.

Lemma translate_id : forall E R (t : itree E R), translate idE t ≅ t.
Proof.
  intros E R t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite itree_eta.
  rewrite (itree_eta t).
  rewrite unfold_translate.
  unfold translateF.
  destruct (observe t); cbn.
  - pupto2_final. apply Reflexive_eq_itree.
  - pfold. econstructor. pupto2_final. right.  apply CIH.
  - pfold. econstructor. intros.  pupto2_final. right.  apply CIH.
Qed.

Lemma translate_cmpE : forall E F G R (g : F ~> G) (f : E ~> F) (t : itree E R),
    translate (cmpE g f) t ≅ translate g (translate f t).
Proof.
  intros E F G R g f t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite itree_eta.
  rewrite (itree_eta (translate g (translate f t))).
  repeat rewrite unfold_translate.
  unfold translateF.
  destruct (observe t); cbn.
  - pupto2_final. apply Reflexive_eq_itree.
  - pfold. econstructor. pupto2_final. right.  apply CIH.
  - pfold. econstructor. intros.  pupto2_final. right.  apply CIH.
Qed.

(* SAZ: TODO - it would be good to allow for rewriting of event morphisms under translate:

   E ~~ F -> translate E t ≅ translate F t

   Where E ~~ F is extensional equality.
*)