(** * Theorems about [Interp.translate] *)

(* begin hide *)
From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTausEquivalence
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Interp.

Import ITreeNotations.

From Paco Require Import paco.

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.
(* end hide *)

Section TranslateFacts.
  Context {E F : Type -> Type}.
  Context {R : Type}.
  Context (h : E ~> F).

Lemma unfold_translate : forall (t : itree E R),
      observing eq
        (translate h t)
        (translateF h (fun t => translate h t) (observe t)).
Proof.
  intros t. econstructor. reflexivity.
Qed.

Lemma unfold_translate_ : forall (t : itree E R),
    eq_itree eq
        (translate h t)
        (translateF h (fun t => translate h t) (observe t)).
Proof.
  intros; apply observing_eq_itree_eq, unfold_translate.
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

Global Instance eq_itree_translate' :
  Proper (eq_itree eq ==> eq_itree eq) (@translate _ _ h R).
Proof.
  ucofix CIH.
  intros x y H.
  rewrite itree_eta.
  rewrite (itree_eta (translate h y)), !unfold_translate, <-!itree_eta.
  rewrite (itree_eta x), (itree_eta y) in H.
  uunfold H. genobs_clear x ox. genobs_clear y oy. repeat red in H.
  destruct ox, oy; dependent destruction H; constructor; eauto with paco.
Qed.

Global Instance eq_itree_translateF :
  Proper (going (eq_itree eq) ==> eq_itree eq)
         (translateF h (@translate _ _ h R)).
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

(**)

Definition respectful_eq_itree {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eq_itree eq) (fun _ => eq_itree eq).

Definition respectful_eutt {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eutt eq) (fun _ => eutt eq).

Require ITree.Core.KTreeBasicFacts. (* TODO: only needed to avoid a universe inconsistency right around here (errors if you try to move this to the end of the file, or just under the next instance)... *)

Instance eq_itree_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eq_itree ==> eq_itree eq ==> eq_itree eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red; eauto.
Qed.

Instance eutt_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eutt ==> eutt eq ==> eutt eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red; eauto.
Qed.

Instance eq_itree_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eq_itree)
            translate.
Proof.
  intros f g Hfg T.
  ucofix CIH; rename r into rr; intros l r Hlr.
  rewrite 2 unfold_translate.
  uunfold Hlr; red in Hlr.
  destruct Hlr; cbn.
  - constructor; auto.
  - constructor; auto with paco.
  - rewrite Hfg. constructor; auto with paco.
Qed.

Instance eutt_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            translate.
Proof.
  repeat red.
  intros until T.
  ucofix CIH. red. ucofix CIH'. intros.
  rewrite !unfold_translate. do 2 uunfold H1.
  induction H1; intros; subst; simpl.
  - econstructor. eauto.
  - rewrite H. constructor.
    intros w. right.
    ubase. eapply CIH'. edestruct (EUTTK w); eauto with paco.
  - econstructor. eauto 7 with paco.
  - constructor. eutt0_fold. rewrite unfold_translate. auto.
  - constructor. eutt0_fold. rewrite unfold_translate. auto.
Qed.

Instance eutt_translate' {E F : Type -> Type} {R : Type} (f : E ~> F) :
  Proper (eutt eq ==> eutt eq)
         (@translate E F f R).
Proof.
  repeat red.
  apply eutt_translate.
  reflexivity.
Qed.
