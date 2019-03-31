From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Category
     Basics.Basics
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeBasicFacts
     Eq.UpToTausEquivalence
     Indexed.Sum
     Core.Subevent
     Indexed.Function
     Indexed.Relation
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts.

Import ITreeNotations.

Definition respectful_eq_itree {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eq_itree eq) (fun _ => eq_itree eq).

Definition respectful_eutt {E F : Type -> Type}
  : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop
  := i_respectful (fun _ => eutt eq) (fun _ => eutt eq).

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

Instance Equivalence_eq_Handler {E F : Type -> Type}
  : Equivalence (@eq_Handler E F).
Proof.
  unfold eq_Handler.
  apply (Equivalence_i_pointwise (fun R => eq_itree eq)).
Qed.

Require ITree.Core.KTreeFacts. (* TODO: only needed to avoid a universe inconsistency right around here (errors if you try to move this to the end of the file, or just under the next instance)... *)

Instance Equivalence_eutt_Handler {E F : Type -> Type}
  : Equivalence (@eutt_Handler E F).
Proof.
  unfold eutt_Handler.
  apply (Equivalence_i_pointwise (fun R => eutt eq)).
Qed.

Instance Equivalence_eq2_Handler {E F : Type -> Type}
  : @Equivalence (Handler E F) eq2.
Proof.
  exact Equivalence_eutt_Handler.
Qed.

(** * [interp] *)

(* Unfolding of [interp]. *)
Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f t)
  | VisF e k => Tau (f _ e >>= (fun x => interp f (k x)))
  end.

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f t ≅ (_interp f (observe t)).
Proof.
  unfold interp. unfold aloop, ALoop_itree. rewrite unfold_aloop'.
  destruct (observe t); cbn.
  - reflexivity.
  - rewrite bind_ret_; reflexivity. (* TODO: [bind_ret] is incredibly slow *)
  - rewrite map_bind. apply eq_itree_Tau. eapply eq_itree_bind.
    reflexivity.
    intros ? _ []; reflexivity.
Qed.

(** ** [interp] and constructors *)

Lemma interp_ret {E F R} {f : E ~> itree F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f (Vis e k)) (Tau (ITree.bind (f _ e) (fun x => interp f (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

(** ** [interp] properness *)
Instance eq_itree_interp {E F}
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq_Handler ==> respectful_eq_itree)
            interp.
Proof.
  intros f g Hfg.
  intros T l r Hlr.
  revert l r Hlr; ucofix CIH.
  rename r into rr; intros l r Hlr.
  rewrite 2 unfold_interp.
  uunfold Hlr; red in Hlr.
  destruct Hlr; cbn.
  - constructor; auto.
  - constructor; auto with paco.
  - constructor.
    uclo @eq_itree_clo_bind. econstructor.
    eapply Hfg.
    intros ? _ [].
    auto with paco.
Qed.

Instance eq_itree_interp' {E F R f}
  : Proper (eq_itree eq ==> eq_itree eq) (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  eapply eq_itree_interp.
  reflexivity.
Qed.

Instance eutt_interp (E F : Type -> Type)
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            interp.
Proof.
  repeat red.
  intros until T.
  ucofix CIH. red. ucofix CIH'. intros.

  rewrite !unfold_interp. do 2 uunfold H1.
  induction H1; intros; subst; simpl.
  - econstructor. eauto.
  - constructor.
    uclo eutt0_clo_bind.
    econstructor; [apply H|].
    intros; subst.
    ubase. eapply CIH'; edestruct (EUTTK v2); eauto with paco.
  - econstructor. eauto 7 with paco.
  - constructor. eutt0_fold. rewrite unfold_interp. auto.
  - constructor. eutt0_fold. rewrite unfold_interp. auto.
Qed.

Instance eutt_interp' {E F : Type -> Type} {R : Type} (f : E ~> itree F) :
  Proper (eutt eq ==> eutt eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  apply eutt_interp.
  reflexivity.
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
  revert R t k; ucofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t). (* TODO: slow *)
  destruct (observe t); cbn.
  - rewrite bind_ret. apply reflexivity.
  - rewrite bind_tau, !interp_tau.
    econstructor. eauto with paco.
  - rewrite interp_vis, bind_tau. rewrite bind_bind.
    constructor.
    uclo (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. auto with paco.
Qed.

Lemma interp_trigger {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≅ Tau (f _ e).
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  apply eq_itree_Tau.
  setoid_rewrite interp_ret.
  rewrite bind_ret2.
  reflexivity.
Qed.

(** *** Identities for [interp] *)

Lemma interp_id_h {A R} (t : itree A R)
  : interp (id_ A) t ≈ t.
Proof.
  revert t. ucofix CIH. red. ucofix CIH'. intros.
  rewrite unfold_interp. unfold _interp. repeat red.
  destruct (observe t); cbn; eauto 8 with paco.
  unfold id_, Id_Handler, Handler.id_, ITree.trigger. eutt0_fold. rewrite bind_vis_.
  do 2 constructor.
  left; rewrite bind_ret; auto with paco.
Qed.

Lemma interp_trigger_h {E R} (t : itree E R) :
  interp (fun _ e => ITree.trigger e) t ≈ t.
Proof.
  revert t. ucofix CIH. red. ucofix CIH'. intros.
  rewrite unfold_interp. repeat red.
  destruct (observe t); cbn; eauto with paco.
  unfold ITree.trigger. constructor. rewrite bind_vis.
  constructor.
  left. rewrite bind_ret.
  auto with paco.
Qed.

(** ** Composition of [interp] *)

Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp f t)
    ≅ interp (fun _ e => interp g (f _ e)) t.
Proof.
  ucofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite interp_ret. constructor. reflexivity.
  - rewrite interp_tau. constructor. auto with paco.
  - rewrite interp_tau, interp_bind.
    constructor.
    uclo eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      auto with paco.
Qed.

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g (translate f t) ≅ interp (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ucofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - constructor. ubase. apply CIH.
  - constructor.
    uclo eq_itree_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. auto with paco.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.trigger (f _ e)) t.
Proof.
  revert t. ucofix CIH. red. ucofix CIH'. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, _interp. repeat red.
  destruct (observe t); cbn; simpl in *; eauto 7 with paco.
  unfold ITree.trigger. econstructor. rewrite bind_vis.
  do 2 constructor.
  rewrite bind_ret. auto with paco.
Qed.

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_trigger : itree.
Hint Rewrite @interp_bind : itree.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) ca :
  interp f (loop_ t ca) ≅ loop_ (fun ca => interp f (t ca)) ca.
Proof.
  revert ca. ucofix CIH. intros.
  unfold loop. rewrite !unfold_loop'. unfold loop_once.
  rewrite interp_bind.
  uclo eq_itree_clo_bind. econstructor; [reflexivity|].
  intros. subst. rewrite unfold_interp.
  destruct u2; econstructor; eauto with paco.
Qed.
