(** * Theorems about [Interp.translate] *)

(* begin hide *)
From Stdlib Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Coinduction Require Import all. 

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Core.Subevent
     Eq.Shallow
     Eq.Eqit
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Interp.

Import ITreeNotations.
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

#[global]
Instance eq_itree_translate' :
  Proper (eq_itree eq ==> eq_itree eq) (@translate _ _ h R).
Proof.
  intros!. revert x y H. icoinduction c cih. intros. 
  to_mon. 
  rewrite itree_eta, (itree_eta (translate h y)), !unfold_translate, <-!itree_eta.
  step in H.
  induction H; simpobs; simpl; eauto with itree.  
Qed.

#[global]
Instance eq_itree_translateF :
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
  icoinduction c cih. 
  intros s t k. to_mon. 
  match goal with
  | [ |- _ ?t1 ?t2 ] => rewrite (itree_eta_ t1), (itree_eta_ t2)
  end; cbn.
  unfold observe; cbn.
  destruct (observe t); cbn; eauto with itree. 
Qed.

Lemma translate_id : forall E R (t : itree E R), translate (id_ _) t ≅ t.
Proof.
  intros E R t.
  revert t.
  bcoinduction c cih. intros. 
  rewrite itree_eta.
  rewrite (itree_eta t).
  rewrite unfold_translate.
  unfold translateF.
  destruct (observe t); cbn; try constructor; eauto. 
Qed.

Import CatNotations.

Lemma translate_cmpE : forall E F G R (g : F ~> G) (f : E ~> F) (t : itree E R),
    translate (f >>> g)%cat t ≅ translate g (translate f t).
Proof.
  intros E F G R g f t.
  revert t.
  bcoinduction c cih. intros. 
  rewrite !unfold_translate.
  genobs_clear t ot. destruct ot; cbn; try constructor; eauto. 
Qed.

(**)

Definition respectful_eq_itree {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eq_itree eq) (fun _ => eq_itree eq).

Definition respectful_eutt {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eutt eq) (fun _ => eutt eq).

Require ITree.Core.KTreeFacts. (* TODO: only needed to avoid a universe inconsistency right around here (errors if you try to move this to the end of the file, or just under the next instance)... *)

#[global]
Instance eq_itree_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eq_itree ==> eq_itree eq ==> eq_itree eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red. intros. repeat red in H. eauto.
Qed.

#[global]
Instance eutt_apply_IFun {E F : Type -> Type} {T : Type}
  : Proper (respectful_eutt ==> eutt eq ==> eutt eq)
           (@apply_IFun (itree E) (itree F) T).
Proof.
  repeat red. intros. repeat red in H. eauto.
Qed.

#[global]
Instance eq_itree_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eq_itree)
            translate.
Proof.
  intros f g Hfg T.
  bcoinduction c cih. intros. 
  rewrite 2 unfold_translate.
  step in H. 
  destruct H; cbn; try easy; try rewrite Hfg; eauto with itree. 
Qed.

#[global]
Instance eutt_translate {E F}
  : @Proper (IFun E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            translate.
Proof.
  repeat red.
  intros until T.
  bcoinduction c cih. intros.
  rewrite !unfold_translate. step in H0. 
  induction H0; subst; simpl; eauto with itree. 
  - rewrite H. econstructor. eauto with itree.
Qed.

#[global]
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
  bcoinduction c cih. intros. 
  rewrite !unfold_translate. step in H. 
  induction H; intros; subst; simpl; eauto with itree. 
Qed. 

Lemma translate_trigger {E F G} `{E -< F} :
  forall X (e: E X) (h: F ~> G),
    translate h (trigger e) ≈ trigger (h _ (subevent X e)).
Proof.
  intros; unfold trigger; rewrite translate_vis; setoid_rewrite translate_ret; reflexivity.
Qed.

(** Inversion principles *)

Lemma translate_Vis_inv {E F} {R T} (h: E ~> F) (t: itree E R) (e': F T) k':
  translate h t ≅ Vis e' k' ->
  exists (e: E T) k, t ≅ Vis e k /\ e' = h _ e /\ (forall x, k' x ≅ translate h (k x)).
Proof.
  intros. rewrite (itree_eta t) in H. setoid_rewrite (itree_eta t).
  desobs t Ht; clear t Ht; rewrite unfold_translate in H; cbn in H.
  - step in H; easy. 
  - sinv H; easy.  
  - apply eqitree_inv_Vis_r in H; break H. 
    cbn in H. inv_Vis. 
    exists e, k. repeat now split. 
Qed.
