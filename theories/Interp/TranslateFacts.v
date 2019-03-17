(* translate facts ---------------------------------------------------------- *)

From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITree
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
     Interp.Interp.

Import ITreeNotations.

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
    observing eq (translate h t) (translateF h (translate h) (observe t)).
Proof.
  intros t. econstructor. reflexivity.
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

Global Instance translate_Proper :
  Proper (eq_itree (@eq R) ==> eq_itree eq) (translate h).
Proof.
  ucofix CIH.
  intros x y H.
  rewrite itree_eta.
  rewrite (itree_eta (translate h y)), !unfold_translate, <-!itree_eta.
  rewrite (itree_eta x), (itree_eta y) in H.
  uunfold H. genobs_clear x ox. genobs_clear y oy. repeat red in H.
  destruct ox, oy; dependent destruction H; constructor; eauto with paco.
Qed.

Global Instance translateF_Proper :
  Proper (going (eq_itree eq) ==> eq_itree (@eq R)) (translateF h (translate h)).
Proof.
  repeat red. intros.
  replace x with (observe (go x)) by auto.
  replace y with (observe (go y)) by auto.
  rewrite <- !unfold_translate.
  rewrite H. apply reflexivity.
Qed.

End TranslateFacts.

Lemma translate_bind : forall {E F R S} (h : E ~> F) (t : itree E S) (k : S -> itree E R),
    translate h (x <- t ;; k x) ≅ (x <- (translate h t) ;; translate h (k x)).
Proof.
  intros E F R S h t k.
  revert S t k.
  ucofix CIH.
  intros s t k.
  rewrite !unfold_translate, !unfold_bind.
  genobs_clear t ot. destruct ot; cbn.
  - rewrite unfold_translate. apply reflexivity.
  - econstructor. ubase. apply CIH.
  - econstructor. intros. ubase. apply CIH.
Qed.

(* categorical properties --------------------------------------------------- *)

Lemma translate_id : forall E R (t : itree E R), translate (id_ _) t ≅ t.
Proof.
  intros E R t.
  revert t.
  ucofix CIH.
  intros t.
  rewrite itree_eta.
  rewrite (itree_eta t).
  rewrite unfold_translate.
  unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity.
  - econstructor. ubase. apply CIH.
  - econstructor. intros. ubase. apply CIH.
Qed.

Import CatNotations.

Lemma translate_cmpE : forall E F G R (g : F ~> G) (f : E ~> F) (t : itree E R),
    translate (f >>> g)%cat t ≅ translate g (translate f t).
Proof.
  intros E F G R g f t.
  revert t.
  ucofix CIH.
  intros t.
  rewrite !unfold_translate.
  genobs_clear t ot. destruct ot; cbn.
  - apply reflexivity.
  - econstructor. ubase. apply CIH.
  - econstructor. intros. ubase. apply CIH.
Qed.

(* SAZ: TODO - it would be good to allow for rewriting of event morphisms under translate:

   E ~~ F -> translate E t ≅ translate F t

   Where E ~~ F is extensional equality.
*)
