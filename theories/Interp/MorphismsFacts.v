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

Set Universe Polymorphism.


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
Definition interp_u {E F} (f : E ~> itree F) R (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f _ t)
  | VisF e k => Tau (f _ e >>= (fun x => interp f _ (k x)))
  end.

Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f _ t ≅ (interp_u f _ (observe t)).
Proof.
  unfold interp. rewrite unfold_aloop'.
  destruct (observe t); cbn.
  - reflexivity.
  - rewrite ret_bind; reflexivity. (* TODO: Incredibly slow *)
  - rewrite map_bind. apply eq_itree_tau. eapply eq_itree_bind.
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
  Proper (Rhom (fun _ => eq_itree eq) ==> eq_itree eq ==> eq_itree eq)
         (fun f => @interp E F f R).
Proof.
  intros f g Hfg.
  intros l r Hlr.
  pupto2_init; revert l r Hlr; pcofix CIH.
  rename r into rr; intros l r Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; pclearbot; cbn.
  - pupto2_final. pfold. constructor; auto.
  - pupto2_final. pfold. constructor; auto.
  - pfold; constructor.
    pupto2 @eq_itree_clo_bind. econstructor.
    eapply Hfg.
    intros ? _ [].
    pupto2_final; auto.
Qed.

Global Instance Proper_interp_eq_itree {E F R f}
: Proper (eq_itree eq ==> eq_itree eq) (@interp E F f R).
Proof.
  eapply eq_itree_interp.
  red. reflexivity.
Qed.

(* Note that this allows rewriting of handlers. *)
Definition eutt_interp_gen (E F : Type -> Type) (R : Type) :
  Proper (Rhom (fun _ => eutt eq) ==> eutt eq ==> eutt eq)
         (fun f => @interp E F f R).
Proof.
  repeat intro. pupto2_init. revert_until H. pcofix CIH. intros.
  pfold. pupto2_init. revert_until CIH. pcofix CIH'. intros.

  rewrite !unfold_interp. do 2 punfold H1.
  induction H1; intros; subst; pclearbot; simpl; eauto.
  - pfold; constructor.
    pupto2 eutt_nested_clo_bind.
    econstructor; [apply H|].
    intros; subst. pupto2_final.
    right. eapply CIH'. edestruct EUTTK; pclearbot; eauto.
  - pfold; econstructor. pupto2_final. eauto 7.
  - pfold; constructor. pfold2_reverse. rewrite unfold_interp. auto.
  - pfold; constructor. pfold2_reverse. rewrite unfold_interp. auto.
Qed.

Instance eutt_interp (E F : Type -> Type) f (R : Type) :
  Proper (eutt eq ==> eutt eq)
         (@interp E F f R).
Proof.
  apply eutt_interp_gen.
  red; reflexivity.
Qed.

Lemma interp_ret : forall {E F R} x
      (f : E ~> itree F),
   (interp f R (Ret x)) ≅ Ret x.
Proof.
  intros. apply observing_eq_itree_eq.
  constructor. reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
   (interp f _ (ITree.bind t k)) ≅ (ITree.bind (interp f _ t) (fun r => interp f _ (k r))).
Proof.
  pupto2_init; revert R t k; pcofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t).
  destruct (observe t); cbn.
  (* TODO: [ret_bind] (0.8s) is much slower than [ret_bind_] (0.02s) *)
  - rewrite ret_bind. pupto2_final. apply reflexivity.
  - rewrite tau_bind, !tau_interp.
    pupto2_final. pfold. econstructor. eauto.
  - rewrite vis_interp, tau_bind. rewrite bind_bind.
    pfold; constructor.
    pupto2 (eq_itree_clo_bind F S). econstructor.
    + reflexivity.
    + intros; subst. pupto2_final. auto.
Qed.

Lemma interp_liftE {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f _ (ITree.liftE e) ≅ Tau (f _ e).
Proof.
  unfold ITree.liftE. rewrite vis_interp.
  apply eq_itree_tau.
  setoid_rewrite ret_interp.
  rewrite bind_ret.
  reflexivity.
Qed.


(** ** Composition of [interp] *)

Lemma interp_id_liftE {E R} (t : itree E R) :
  interp (fun _ e => ITree.liftE e) _ t ≈ t.
Proof.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold. pupto2_init; revert t; pcofix CIH'; intros t.
  rewrite unfold_interp.
  destruct (observe t); cbn; eauto.
  - pfold. constructor. pupto2_final; auto.
  - unfold ITree.liftE. rewrite vis_bind; cbn.
    pfold; constructor; constructor.
    left. rewrite ret_bind.
    auto.
Qed.


Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g _ (interp f _ t)
    ≅ interp (fun _ e => interp g _ (f _ e)) _ t.
Proof.
  intros t.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite ret_interp. pupto2_final. pfold. constructor. reflexivity.
  - rewrite tau_interp. pupto2_final. pfold. constructor. auto.
  - rewrite tau_interp, interp_bind.
    pfold; constructor.
    pupto2 eq_itree_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      pupto2_final; auto.
Qed.

(* Commuting interpreters --------------------------------------------------- *)

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g _ (translate f  t) ≅ interp (fun _ e => g _ (f _ e)) _ t.
Proof.
  pupto2_init.
  revert t.
  pcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold interp_u.
  rewrite unfold_translate. unfold translateF.
  destruct (observe t); cbn.
  - pupto2_final. apply Reflexive_eq_itree. (* SAZ: typeclass resolution failure? *)
  - pfold. constructor. pupto2_final. right. apply CIH.
  - pfold; constructor.
    pupto2 eq_itree_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. pupto2_final. auto.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.liftE (f _ e)) _ t.
Proof.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold. pupto2_init; revert t; pcofix CIH'; intros t.
  rewrite unfold_translate.
  rewrite unfold_interp.
  unfold translateF, interp_u.
  destruct (observe t); cbn; simpl in *; eauto.
  - pfold. constructor. auto.
  - unfold ITree.liftE. rewrite vis_bind.
    pfold. do 2 constructor.
    left. rewrite ret_bind. auto.
Qed.
