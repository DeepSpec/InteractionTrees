From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     paco2_upto Core Morphisms Eq.Eq Eq.UpToTaus.

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
  observe (interp f t) = observe (interp_match f (interp f (R:=R)) (observe t)).
Proof. cbn. eauto. Qed.

Lemma unfold_interp {E F R} {f : eff_hom E F} (t : itree E R) :
  interp f t ≅ interp_match f (interp f (R:=R)) (observe t).
Proof. rewrite itree_eta, interp_unfold, <-itree_eta. reflexivity. Qed.

Lemma ret_interp {E F R} {f : eff_hom E F} (x: R):
  interp f (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma tau_interp {E F R} {f : eff_hom E F} (t: itree E R):
  interp f (Tau t) ≅ Tau (interp f t).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma vis_interp {E F R} {f : eff_hom E F} U (e: E U) (k: U -> itree E R) :
  interp f (Vis e k) ≅ ITree.bind (f _ e) (fun x => Tau (interp f (k x))).
Proof. rewrite unfold_interp. reflexivity. Qed.

Instance eq_itree_interp {E F R} f :
  Proper (@eq_itree E R ==>
          @eq_itree F R) (interp f).
Proof.
  repeat intro. pupto2_init. revert_until R.
  pcofix CIH. intros.
  rewrite itree_eta, (itree_eta (interp f y)), !interp_unfold.
  punfold H0; red in H0.
  genobs x ox; destruct ox; simpobs; dependent destruction H0; simpobs; pclearbot.
  - pupto2_final. pfold. red. cbn. eauto.
  - pupto2_final. pfold. red. cbn. eauto.
  - simpl. rewrite <- !itree_eta.
    pupto2 (eq_itree_clo_bind F R). econstructor; try reflexivity.
    intros. specialize (REL v). pclearbot.
    pupto2_final. pfold. econstructor. eauto.
Qed.

Lemma interp_bind {E F R S}
      (f : eff_hom E F) (t : itree E R) (k : R -> itree E S) :
   (interp f (ITree.bind t k)) ≅ (ITree.bind (interp f t) (fun r => interp f (k r))).
Proof.
  pupto2_init.
  revert R t k.
  pcofix CIH. intros.
  rewrite (itree_eta t). destruct (observe t).
  - rewrite ret_interp, !ret_bind. pupto2_final. apply eq_itree_refl.
  - rewrite tau_interp, !tau_bind, tau_interp.
    pupto2_final. pfold. econstructor. eauto.
  - rewrite vis_interp, !vis_bind, vis_interp, bind_bind.
    pupto2 (eq_itree_clo_bind F S). econstructor; [reflexivity|]. intros.
    rewrite tau_bind.
    pupto2_final. pfold. econstructor. eauto.
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
