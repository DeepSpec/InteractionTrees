From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Core.KTree
     Core.KTreeBasicFacts
     Eq.UpToTausEquivalence
     Indexed.Sum
     Indexed.OpenSum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts.

Import ITreeNotations.



(** * [interp] *)

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
Instance eq_itree_interp {E F R}:
  Proper (i_respectful (fun _ => eq_itree eq) ==> eq_itree eq ==> eq_itree eq)
         (fun f => @interp E (itree F) _ _ _ f R).
Proof.
  intros f g Hfg.
  intros l r Hlr.
  revert l r Hlr; wcofix CIH.
  rename r into rr; intros l r Hlr.
  rewrite 2 unfold_interp.
  wunfold Hlr; red in Hlr.
  destruct Hlr; cbn; wstep.
  - constructor; auto.
  - constructor; auto with paco.
  - constructor.
    wclo @eq_itree_clo_bind. econstructor.
    eapply Hfg.
    intros ? _ [].
    auto with paco.
Qed.

Global Instance Proper_interp_eq_itree {E F R f}
: Proper (eq_itree eq ==> eq_itree eq) (@interp E (itree F) _ _ _ f R).
Proof.
  eapply eq_itree_interp.
  red. reflexivity.
Qed.

(* Note that this allows rewriting of handlers. *)
Definition eutt_interp_gen (E F : Type -> Type) (R : Type) :
  Proper (i_respectful (fun _ => eutt eq) ==> eutt eq ==> eutt eq)
         (fun f => @interp E (itree F) _ _ _ f R).
Proof.
  wcofix CIH; wstep. wcofix CIH'. intros.

  rewrite !unfold_interp. do 2 wunfold H1.
  induction H1; intros; subst; simpl.
  - wstep. constructor. eauto.
  - wstep. constructor.
    wclo eutt0_clo_bind.
    econstructor; [apply H0|].
    intros; subst.
    wbase. eapply CIH'; edestruct (EUTTK v2); eauto with paco.
  - wstep. econstructor. eauto 7 with paco.
  - apply eutt0_tau_left. rewrite unfold_interp. auto.
  - apply eutt0_tau_right. rewrite unfold_interp. auto.
Qed.

Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt eq ==> eutt eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  apply eutt_interp_gen.
  red; reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  ≅ ITree.bind (interp f t) (fun r => interp f (k r)).
Proof.
  revert R t k; wcofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t). (* TODO: slow *)
  destruct (observe t); cbn.
  - rewrite bind_ret. apply reflexivity.
  - rewrite bind_tau, !interp_tau.
    wstep. econstructor. eauto with paco.
  - rewrite interp_vis, bind_tau. rewrite bind_bind.
    wstep. constructor.
    wclo (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. auto with paco.
Qed.

Lemma interp_send {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.send e) ≅ Tau (f _ e).
Proof.
  unfold ITree.send. rewrite interp_vis.
  apply eq_itree_Tau.
  setoid_rewrite interp_ret.
  rewrite bind_ret2.
  reflexivity.
Qed.


(** ** Composition of [interp] *)

Lemma interp_id_send {E R} (t : itree E R) :
  interp (fun _ e => ITree.send e) t ≈ t.
Proof.
  revert t. wcofix CIH. wstep. wcofix CIH'. intros.
  rewrite unfold_interp. rewrite (itree_eta t) at 2.
  destruct (observe t); simpl; try (wstep; constructor; eauto with paco; fail).
  apply eutt0_tau_left.
  unfold ITree.send. rewrite bind_vis.
  wstep. constructor. intros.
  left. rewrite bind_ret_.
  auto with paco.
Qed.


Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp f t)
    ≅ interp (fun _ e => interp g (f _ e)) t.
Proof.
  wcofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite interp_ret. wstep. constructor. reflexivity.
  - rewrite interp_tau. wstep. constructor. auto with paco.
  - rewrite interp_tau, interp_bind.
    wstep. constructor.
    wclo eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      auto with paco.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g (translate f t) ≅ interp (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  wcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - wstep. constructor. wbase. apply CIH.
  - wstep. constructor.
    wclo eq_itree_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. auto with paco.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.send (f _ e)) t.
Proof.
  revert t. wcofix CIH. wstep. wcofix CIH'. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, _interp. repeat red.
  destruct (observe t); cbn; simpl in *; try (wstep; constructor; eauto with paco; fail).
  unfold ITree.send. apply eutt0_tau_right. rewrite bind_vis.
  wstep. constructor. left.
  rewrite bind_ret. auto with paco.
Qed.

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_send : itree.
Hint Rewrite @interp_bind : itree.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) ca :
  interp f (loop_ t ca) ≅ loop_ (fun ca => interp f (t ca)) ca.
Proof.
  revert ca. wcofix CIH. intros.
  rewrite !unfold_loop'. unfold loop_once.
  rewrite interp_bind.
  wclo eq_itree_clo_bind. econstructor; [reflexivity|].
  intros. subst. rewrite unfold_interp.
  destruct u2; simpl; wstep; constructor; eauto with paco.
Qed.