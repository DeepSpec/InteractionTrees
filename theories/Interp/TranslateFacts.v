(** * Theorems about [Interp.translate] *)

(* begin hide *)
From ExtLib Require
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Core.Subevent
     Eq.Eq
     Eq.UpToTaus
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

Lemma unfold_translate_ : forall (t : itree E R),
      observing eq
        (translate h t)
        (translateF h (fun t => translate h t) (observe t)).
Proof.
  intros t. econstructor. reflexivity.
Qed.

Lemma unfold_translate : forall (t : itree E R),
    eq_itree eq
        (translate h t)
        (translateF h (fun t => translate h t) (observe t)).
Proof.
  intros. rewrite unfold_translate_. reflexivity.
Qed.

Lemma translate_ret : forall (r:R), translate h (Ret r) ≅ Ret r.
Proof.
  intros r.
  rewrite itree_eta, unfold_translate. cbn. reflexivity.
Qed.

Lemma translate_tau : forall (t : itree E R), translate h (Tau t) ≅ Tau (translate h t).
Proof.
  intros t.
  rewrite itree_eta, unfold_translate. cbn. reflexivity.
Qed.

Lemma translate_vis : forall X (e:E X) (k : X -> itree E R),
    translate h (Vis e k) ≅ Vis (h _ e) (fun x => translate h (k x)).
Proof.
  intros X e k.
  rewrite itree_eta, unfold_translate. cbn. reflexivity.
Qed.

Global Instance eq_itree_translate' :
  Proper (eq_itree eq ==> eq_itree eq) (@translate _ _ h R).
Proof.
  ginit. gcofix CIH.
  intros x y H.
  rewrite itree_eta, (itree_eta (translate h y)), !unfold_translate, <-!itree_eta.
  punfold H. gstep. red in H |- *.
  destruct (observe x); dependent destruction H; try discriminate;
    pclearbot; simpobs; simpl; eauto 7 with paco.
Qed.

Global Instance eq_itree_translateF :
  Proper (going (eq_itree eq) ==> eq_itree eq)
         (translateF h (@translate _ _ h R)).
Proof.
  repeat red. intros.
  rewrite (itree_eta' x), (itree_eta' y), <- !unfold_translate, H.
  apply reflexivity.
Qed.

End TranslateFacts.

Lemma translate_bind : forall {E F R S} (h : E ~> F) (t : itree E S) (k : S -> itree E R),
    translate h (x <- t ;; k x) ≅ (x <- (translate h t) ;; translate h (k x)).
Proof.
  intros E F R S h t k.
  revert S t k.
  ginit. gcofix CIH.
  intros s t k.
  rewrite !unfold_translate, !unfold_bind.
  genobs_clear t ot. destruct ot; cbn.
  - rewrite unfold_translate. apply reflexivity.
  - gstep. constructor. eauto with paco.
  - gstep. constructor. eauto with paco.
Qed.

Lemma translate_id : forall E R (t : itree E R), translate (id_ _) t ≅ t.
Proof.
  intros E R t.
  revert t.
  ginit. gcofix CIH.
  intros t.
  rewrite itree_eta.
  rewrite (itree_eta t).
  rewrite unfold_translate.
  unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity.
  - gstep. econstructor. gbase. apply CIH.
  - gstep. econstructor. intros. gbase. apply CIH.
Qed.

Import CatNotations.

Lemma translate_cmpE : forall E F G R (g : F ~> G) (f : E ~> F) (t : itree E R),
    translate (f >>> g)%cat t ≅ translate g (translate f t).
Proof.
  intros E F G R g f t.
  revert t.
  ginit. gcofix CIH.
  intros t.
  rewrite !unfold_translate.
  genobs_clear t ot. destruct ot; cbn.
  - apply reflexivity.
  - gstep. econstructor. gbase. apply CIH.
  - gstep. econstructor. intros. gbase. apply CIH.
Qed.

(**)

Definition respectful_eq_itree {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eq_itree eq) (fun _ => eq_itree eq).

Definition respectful_eutt {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eutt eq) (fun _ => eutt eq).

Require ITree.Core.KTreeFacts. (* TODO: only needed to avoid a universe inconsistency right around here (errors if you try to move this to the end of the file, or just under the next instance)... *)

Instance eq_itree_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eq_itree ==> eq_itree eq ==> eq_itree eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red. intros. repeat red in H. eauto.
Qed.

Instance eutt_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eutt ==> eutt eq ==> eutt eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red. intros. repeat red in H. eauto.
Qed.

Instance eq_itree_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eq_itree)
            translate.
Proof.
  intros f g Hfg T.
  ginit. gcofix CIH; rename r into rr; intros l r Hlr.
  rewrite 2 unfold_translate.
  punfold Hlr; red in Hlr.
  destruct Hlr; cbn; try discriminate; pclearbot.
  - gstep. constructor; auto.
  - gstep. constructor; auto with paco.
  - rewrite Hfg. gstep. constructor; red; auto with paco.
Qed.

Instance eutt_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            translate.
Proof.
  repeat red.
  intros until T.
  ginit. gcofix CIH. intros.
  rewrite !unfold_translate. punfold H1. red in H1.
  induction H1; intros; subst; simpl.
  - gstep. econstructor. eauto.
  - gstep. econstructor. pclearbot. eauto with paco.
  - gstep. rewrite H. econstructor. pclearbot. red. eauto 7 with paco.
  - rewrite tau_euttge, unfold_translate. eauto.
  - rewrite tau_euttge, unfold_translate. eauto.
Qed.

Instance eutt_translate' {E F : Type -> Type} {R : Type} (f : E ~> F) :
  Proper (eutt eq ==> eutt eq)
         (@translate E F f R).
Proof.
  repeat red.
  apply eutt_translate.
  reflexivity.
Qed.

Lemma eutt_translate_gen :
      forall {E F X Y} (f : E ~> F) (RR : X -> Y -> Prop) (t : itree E X) (s : itree E Y),
        eutt RR t s ->
        eutt RR (translate f t) (translate f s).
Proof.
  intros *.
  revert t s.
  einit.
  ecofix CIH.
  intros * EUTT.
  rewrite !unfold_translate. punfold EUTT. red in EUTT.
  induction EUTT; intros; subst; simpl; pclearbot.
  - estep.
  - estep. 
  - estep; intros ?; ebase.
  - rewrite tau_euttge, unfold_translate. eauto.
  - rewrite tau_euttge, unfold_translate. eauto.
Qed. 

Lemma translate_trigger {E F G} `{E -< F} :
  forall X (e: E X) (h: F ~> G),
    translate h (trigger e) ≈ trigger (h _ (subevent X e)).
Proof.
  intros; unfold trigger; rewrite translate_vis; setoid_rewrite translate_ret; reflexivity.
Qed.

