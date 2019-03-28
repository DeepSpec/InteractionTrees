From ITree Require Import
     ITree ITreeFacts.

Import CatNotations.
Local Open Scope cat.

(* Test that we can indeed rewrite handlers under interp.  *)
Lemma interp_id_id {E R} (t : itree E R) :
  interp (id_ E >>> id_ E) t ≈ t.
Proof.
  rewrite (@fold_apply_IFun (itree E) (itree E)). (* TODO: don't require type annotations *)
  rewrite cat_id_r. (* Works *)
  rewrite <- fold_apply_IFun.
  rewrite interp_id_h.
  reflexivity.
  all: typeclasses eauto.
Qed.
