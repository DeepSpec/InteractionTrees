(** * Theorems about [interp] *)

(** Main facts:
    - [unfold_interp]: Unfold lemma.
    - [interp_bind]: [interp] is a monad morphism.
    - [interp_trigger]: Events are interpreted using a handler.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Shallow
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts.

Import ITreeNotations.
(* end hide *)

#[global]
Instance Equivalence_eq_Handler {E F : Type -> Type}
  : Equivalence (@eq_Handler E F).
Proof.
  unfold eq_Handler.
  apply (Equivalence_i_pointwise (fun R => eq_itree eq)).
Qed.

#[global]
Instance Equivalence_eutt_Handler {E F : Type -> Type}
  : Equivalence (@eutt_Handler E F).
Proof.
  unfold eutt_Handler.
  apply (Equivalence_i_pointwise (fun R => eutt eq)).
Qed.

Definition Equivalence_eq2_Handler {E F : Type -> Type}
  : @Equivalence (Handler E F) eq2.
Proof.
  exact Equivalence_eutt_Handler.
Qed.

(** Unfolding of [interp]. *)
Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f t)
  | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
  end.

(** Unfold lemma. *)
Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f t ≅ (_interp f (observe t)).
Proof.
  unfold interp, Basics.iter, MonadIter_itree. rewrite unfold_iter.
  destruct (observe t); cbn;
    rewrite ?bind_ret_l, ?bind_map. all: try reflexivity.
Qed.

(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Lemma interp_ret {E F R} {f : E ~> itree F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f (Vis e k)) (ITree.bind (f _ e) (fun x => Tau (interp f (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_trigger {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≳ f _ e.
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  setoid_rewrite tau_euttge. rewrite bind_ret_r.
  reflexivity.
Qed.

#[global] Hint Rewrite @interp_ret : itree.
#[global] Hint Rewrite @interp_vis : itree.
#[global] Hint Rewrite @interp_trigger : itree.

(** ** [interp] properness *)
#[global]
Instance eq_itree_interp {E F}
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq_Handler ==> respectful_eq_itree)
            interp.
Proof.
  intros f g Hfg T.
  ginit. pcofix CIH.
  intros l r0 Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
  guclo eqit_clo_bind. econstructor; [eapply Hfg|].
  intros ? _ [].
  gstep; econstructor; eauto with paco itree.
Qed.

#[global]
Instance eq_itree_interp' {E F R f}
  : Proper (eq_itree eq ==> eq_itree eq) (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  eapply eq_itree_interp.
  reflexivity.
Qed.

#[global]
Instance eutt_interp (E F : Type -> Type)
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            interp.
Proof.
  repeat red.
  intros until T.
  ginit. pcofix CIH. intros.

  rewrite !unfold_interp. punfold H1. red in H1.
  induction H1; intros; subst; pclearbot; simpl.
  - gstep. constructor. eauto.
  - gstep. constructor. eauto with paco.
  - guclo eqit_clo_bind; econstructor; [apply H|].
    intros; subst.
    gstep; constructor; eauto with paco itree.
  - rewrite tau_euttge, unfold_interp. auto.
  - rewrite tau_euttge, unfold_interp. auto.
Qed.

#[global]
Instance euttge_interp (E F : Type -> Type)
  : @Proper (Handler E F -> (itree E ~> itree F))
            (i_pointwise (fun _ => euttge eq) ==>
             i_respectful (fun _ => euttge eq) (fun _ => euttge eq))
            interp.
Proof.
  repeat red.
  intros until T.
  ginit. pcofix CIH. intros.

  rewrite !unfold_interp. punfold H1. red in H1.
  induction H1; intros; subst; pclearbot; simpl.
  - gstep. constructor. eauto.
  - gstep. constructor. eauto with paco.
  - guclo eqit_clo_bind; econstructor; [apply H|].
    intros; subst.
    gstep; constructor; eauto with paco itree.
  - rewrite tau_euttge, unfold_interp. auto.
  - discriminate.
Qed.

#[global]
Instance eutt_interp' {E F : Type -> Type} {R : Type} (RR: R -> R -> Prop) (f : E ~> itree F) :
  Proper (eutt RR ==> eutt RR)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  einit.
  ecofix CIH. intros.
  rewrite !unfold_interp.
  punfold H0.
  induction H0; intros; subst; pclearbot; simpl.
  - estep.
  - estep.
  - ebind; econstructor.
    + reflexivity.
    + intros; subst. estep. ebase.
  - rewrite tau_euttge, unfold_interp. eauto.
  - rewrite tau_euttge, unfold_interp. eauto.
Qed.

#[global]
Instance euttge_interp' {E F : Type -> Type} {R : Type} (f : E ~> itree F) :
  Proper (euttge eq ==> euttge eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red. apply euttge_interp. reflexivity.
Qed.

(* Proof of
   [interp f (t >>= k) ~ (interp f t >>= fun r => interp f (k r))]

   "By coinduction", case analysis on t:

    - [t = Ret r] or [t = Vis e k] (...)

    - [t = Tau t]:
          interp f (Tau t >>= k)
        = interp f (Tau (t >>= k))
        = Tau (interp f (t >>= k))
        { by "coinductive hypothesis" }
        ~ Tau (interp f t >>= fun ...)
        = Tau (interp f t) >>= fun ...
        = interp f (Tau t) >>= fun ...
        (QED)

 *)

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  ≅ ITree.bind (interp f t) (fun r => interp f (k r)).
Proof.
  revert R t k. ginit. pcofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite bind_ret_l. apply reflexivity.
  - rewrite bind_tau, !interp_tau.
    gstep. econstructor. eauto with paco.
  - rewrite interp_vis, bind_bind.
    guclo eqit_clo_bind; econstructor; try reflexivity.
    intros; subst.
    rewrite bind_tau. gstep; constructor; eauto with paco.
Qed.

#[global] Hint Rewrite @interp_bind : itree.

(** *** Identities for [interp] *)

Lemma interp_id_h {A R} (t : itree A R)
  : interp (id_ A) t ≳ t.
Proof.
  revert t. ginit. pcofix CIH. intros.
  rewrite (itree_eta t), unfold_interp.
  destruct (observe t); try (gstep; constructor; auto with paco).
  cbn. gstep. red; cbn. constructor; red; intros.
  ITree.fold_subst.
  rewrite bind_ret_l, tau_euttge. eauto with paco.
Qed.

Lemma interp_trigger_h {E R} (t : itree E R) :
  interp ITree.trigger t ≈ t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_interp. rewrite (itree_eta t) at 2.
  destruct (observe t); try estep.
  unfold ITree.trigger. simpl. rewrite bind_vis.
  evis. intros. rewrite bind_ret_l, tau_euttge.
  auto with paco.
Qed.

(** ** Composition of [interp] *)

Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp f t)
    ≅ interp (fun _ e => interp g (f _ e)) t.
Proof.
  ginit. pcofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite interp_ret. gstep. constructor. reflexivity.
  - rewrite interp_tau. gstep. constructor. auto with paco.
  - rewrite interp_bind.
    guclo eqit_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      rewrite interp_tau.
      gstep; constructor.
      auto with paco.
Qed.

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g (translate f t) ≅ interp (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ginit. pcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate_. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - gstep. constructor. gbase. apply CIH.
  - guclo eqit_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. gstep; constructor; auto with paco.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.trigger (f _ e)) t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  destruct (observe t); try estep.
  unfold ITree.trigger. simpl. rewrite bind_vis.
  evis. intros. rewrite bind_ret_l, tau_euttge. auto with paco.
Qed.

Lemma interp_forever {E F} (f : E ~> itree F) {R S}
      (t : itree E R)
  : interp f (ITree.forever t)
  ≅ @ITree.forever F R S (interp f t).
Proof.
  ginit. pcofix CIH.
  rewrite (unfold_forever t).
  rewrite (unfold_forever (interp _ _)).
  rewrite interp_bind.
  guclo eqit_clo_bind. econstructor; [reflexivity |].
  intros ? _ []. rewrite interp_tau.
  gstep. constructor; auto with paco.
Qed.

Lemma interp_iter' {E F} (f : E ~> itree F) {I A}
      (t  : I -> itree E (I + A))
      (t' : I -> itree F (I + A))
      (EQ_t : forall i, eq_itree eq (interp f (t i)) (t' i))
  : forall i,
    interp f (ITree.iter t i)
  ≅ ITree.iter t' i.
Proof.
  ginit. pcofix CIH; intros i.
  rewrite 2 unfold_iter.
  rewrite interp_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  { apply EQ_t. }
  intros [] _ []; cbn.
  - rewrite interp_tau; gstep; constructor; auto with paco.
  - rewrite interp_ret. gstep; constructor; auto.
Qed.

Lemma interp_iter {E F} (f : E ~> itree F) {A B}
      (t : A -> itree E (A + B)) a0
  : interp f (iter (C := ktree E) t a0) ≅ iter (C := ktree F) (fun a => interp f (t a)) a0.
Proof.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  apply interp_iter'.
  reflexivity.
Qed.

Lemma interp_iter'_eutt {E F} (f: E ~> itree F) {I A}
    (t : I -> itree E (I + A))
    (t': I -> itree F (I + A))
    (Heq: forall i, interp f (t i) ≈ t' i):
  forall i, interp f (ITree.iter t i) ≈ ITree.iter t' i.
Proof.
  ginit. gcofix CIH; intros i.
  rewrite 2 unfold_iter.
  rewrite interp_bind.
  guclo eqit_clo_bind; econstructor; eauto. apply Heq.
  intros [] _ []; cbn.
  - rewrite interp_tau; gstep; constructor; auto with paco.
  - rewrite interp_ret. gstep; constructor; auto.
Qed.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) a :
  interp f (loop (C := ktree E) t a) ≅ loop (C := ktree F) (fun ca => interp f (t ca)) a.
Proof.
  unfold loop. unfold cat, Cat_Kleisli, ITree.cat; cbn.
  rewrite interp_bind.
  apply eqit_bind.
  { unfold inr_, Inr_Kleisli, lift_ktree, pure; cbn.
    rewrite interp_ret.
    reflexivity.
  }
  repeat intro.
  rewrite interp_iter.
  apply eq_itree_iter.
  intros ? ? [].
  rewrite interp_bind.
  apply eqit_bind; try reflexivity.
  intros []; cbn. unfold cat. rewrite interp_bind.
  - unfold inl_, Inl_Kleisli, inr_, Inr_Kleisli, lift_ktree; cbn.
    rewrite interp_ret, !bind_ret_l, interp_ret.
    reflexivity.
  - unfold cat, id_, Id_Kleisli, inr_, Inr_Kleisli, lift_ktree, pure; cbn.
    rewrite interp_bind, interp_ret, !bind_ret_l, interp_ret.
    reflexivity.
Qed.

Lemma translate_iter {E F I R} (b: I -> itree E (I + R)) (h: E ~> F) i:
  translate h (ITree.iter b i) ≈ ITree.iter (fun x => translate h (b x)) i.
Proof.
  rewrite translate_to_interp.
  rewrite interp_iter'_eutt. reflexivity. clear i.
  intros i. cbn. rewrite translate_to_interp. reflexivity.
Qed.
