From Paco Require Import paco.

From ITree Require Import
     paco2_respectful Core Morphisms Eq.Eq Eq.UpToTaus.

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

Lemma interp_unfold {E F R} {f : eff_hom E F} (t : itree E R) :
  interp f t = interp_match f (fun t' => interp f t') t.
Proof.
  setoid_rewrite (itree_eta (interp f t)). cbn.
  setoid_rewrite <-itree_eta. eauto.
Qed.

Lemma ret_interp {E F R} {f : eff_hom E F} (x: R):
  interp f (Ret x) = Ret x.
Proof.
  rewrite interp_unfold. reflexivity.
Qed.

Lemma tau_interp {E F R} {f : eff_hom E F} (t: itree E R):
  interp f (Tau t) = Tau (interp f t).
Proof.
  rewrite interp_unfold. reflexivity.
Qed.

Lemma vis_interp {E F R} {f : eff_hom E F} U (e: E U) (k: U -> itree E R) :
  interp f (Vis e k) = (x <- (f _ e);; Tau (interp f (k x))).
Proof.
  intros. rewrite interp_unfold. reflexivity.
Qed.

Lemma interp_bind {E F R S}
      (f : eff_hom E F) (t : itree E R) (k : R -> itree E S) :
   (interp f (ITree.bind t k)) ≅ (ITree.bind (interp f t) (fun r => interp f (k r))).
Proof.
  pupto2_init.
  revert R t k.
  pcofix CIH. intros.
  absobs t ot. destruct ot.
  - rewrite ret_interp, !ret_bind. pupto2_final.
    eapply paco2_mon; [apply Reflexive_eq_itree | contradiction].
  - rewrite tau_interp, !tau_bind, tau_interp.
    pupto2_final. pfold. unfold_eq_itree. cbn. eauto.
  - rewrite vis_interp, !vis_bind, vis_interp.
    pupto2 (eq_itree_clo_trans F S). econstructor; [reflexivity| |].
    { simpl. rewrite bind_bind. reflexivity. }
    pupto2 (eq_itree_clo_bind F S). econstructor; [reflexivity|].
    setoid_rewrite tau_bind. intros.
    pupto2_final. pfold. unfold_eq_itree. cbn. eauto.
Qed.

Lemma interp_state_liftE {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (e : E R) :
  (interp_state f (ITree.liftE e) s) ≅ (f _ e s).
Proof.
Admitted.

Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (t : itree E A) (k : A -> itree E B)
      (s : S) :
  (interp_state f (t >>= k) s)
    ≅
  (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
Proof.
Admitted.

Lemma interp_state_ret {E F : Type -> Type} {R S : Type}
      (f : forall T, E T -> S -> itree F (S * T)%type)
      (s : S) (r : R) :
  (interp_state f (Ret r) s) ≅ (Ret (s, r)).
Proof.
Admitted.
