From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Core.ITree
     Eq.Eq
     Eq.UpToTaus
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
Definition _interp {E F} (f : E ~> itree F) R (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f _ t)
  | VisF e k => Tau (f _ e >>= (fun x => interp f _ (k x)))
  end.

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f _ t ≅ (_interp f _ (observe t)).
Proof.
  unfold interp. rewrite unfold_aloop'.
  destruct (observe t); cbn.
  - reflexivity.
  - rewrite ret_bind; reflexivity. (* TODO: Incredibly slow *)
  - rewrite map_bind. apply eq_itree_Tau. eapply eq_itree_bind.
    reflexivity.
    intros ? _ []; reflexivity.
Qed.

(** ** [interp] and constructors *)

Lemma ret_interp {E F R} {f : E ~> itree F} (x: R):
  interp f _ (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma tau_interp {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f _ (Tau t)) (Tau (interp f _ t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma vis_interp {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f _ (Vis e k)) (Tau (ITree.bind (f _ e) (fun x => interp f _ (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

(** ** [interp] properness *)
Instance eq_itree_interp {E F R}:
  Proper (i_respectful (fun _ => eq_itree eq) ==> eq_itree eq ==> eq_itree eq)
         (fun f => @interp E F f R).
Proof.
  intros f g Hfg.
  intros l r Hlr.
  uinit; revert l r Hlr; ucofix CIH.
  rename r into rr; intros l r Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; pclearbot; cbn.
  - ufinal. pfold. constructor; auto.
  - ufinal. pfold. constructor; auto.
  - constructor.
    uclo @eq_itree_clo_bind. econstructor.
    eapply Hfg.
    intros ? _ [].
    ufinal; auto.
Qed.

Global Instance Proper_interp_eq_itree {E F R f}
: Proper (eq_itree eq ==> eq_itree eq) (@interp E F f R).
Proof.
  eapply eq_itree_interp.
  red. reflexivity.
Qed.

(* Note that this allows rewriting of handlers. *)
Definition eutt_interp_gen (E F : Type -> Type) (R : Type) :
  Proper (i_respectful (fun _ => eutt eq) ==> eutt eq ==> eutt eq)
         (fun f => @interp E F f R).
Proof.
  uinit. ucofix CIH. uinit. ucofix CIH'. intros.

  rewrite !unfold_interp. do 2 punfold H1.
  induction H1; intros; subst; pclearbot; simpl; eauto with paco.
  - constructor.
    uclo eutt_nested_clo_bind.
    econstructor; [apply H0|].
    intros; subst. ufinal.
    right. eapply CIH'; edestruct (EUTTK v2); pclearbot; eauto.
  - econstructor. ufinal. eauto 7.
  - constructor. gcpn_fold. rewrite unfold_interp. auto.
  - constructor. gcpn_fold. rewrite unfold_interp. auto.
Qed.

Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt eq ==> eutt eq)
         (@interp E F f R).
Proof.
  apply eutt_interp_gen.
  red; reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
   (interp f _ (ITree.bind t k)) ≅ (ITree.bind (interp f _ t) (fun r => interp f _ (k r))).
Proof.
  uinit; revert R t k; ucofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t).
  destruct (observe t); cbn.
  (* TODO: [ret_bind] (0.8s) is much slower than [ret_bind_] (0.02s) *)
  - rewrite ret_bind. ufinal. apply reflexivity.
  - rewrite tau_bind, !tau_interp.
    ufinal. pfold. econstructor. eauto.
  - rewrite vis_interp, tau_bind. rewrite bind_bind.
    constructor.
    uclo (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. ufinal. auto.
Qed.

Lemma interp_lift {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f _ (ITree.lift e) ≅ Tau (f _ e).
Proof.
  unfold ITree.lift. rewrite vis_interp.
  apply eq_itree_Tau.
  setoid_rewrite ret_interp.
  rewrite bind_ret.
  reflexivity.
Qed.


(** ** Composition of [interp] *)

Lemma interp_id_lift {E R} (t : itree E R) :
  interp (fun _ e => ITree.lift e) _ t ≈ t.
Proof.
  revert t. uinit. ucofix CIH. uinit. ucofix CIH'. intros.
  rewrite unfold_interp.
  destruct (observe t); cbn; eauto with paco.
  - constructor. ufinal. eauto.
  - unfold ITree.lift. rewrite vis_bind; cbn.
    constructor; constructor.
    left. rewrite ret_bind.
    auto with paco.
Qed.


Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g _ (interp f _ t)
    ≅ interp (fun _ e => interp g _ (f _ e)) _ t.
Proof.
  uinit. ucofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite ret_interp. ufinal. pfold. constructor. reflexivity.
  - rewrite tau_interp. ufinal. pfold. constructor. auto.
  - rewrite tau_interp, interp_bind.
    constructor.
    uclo eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      ufinal; auto.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g _ (translate f  t) ≅ interp (fun _ e => g _ (f _ e)) _ t.
Proof.
  revert t.  
  uinit.
  ucofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - ufinal. apply Reflexive_eq_itree. (* SAZ: typeclass resolution failure? *)
  - constructor. ufinal. right. apply CIH.
  - constructor.
    uclo eq_itree_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. ufinal. auto.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.lift (f _ e)) _ t.
Proof.
  revert t. uinit. ucofix CIH. uinit. ucofix CIH'. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, _interp.
  destruct (observe t); cbn; simpl in *; eauto 7 with paco.
  unfold ITree.lift. rewrite vis_bind.
  do 2 constructor.
  left. rewrite ret_bind. auto with paco.
Qed.
