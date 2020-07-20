From ITree Require Import
     ITree ITreeFacts.

Import CatNotations.
Local Open Scope cat.

(* Test that we can indeed rewrite handlers under interp.  *)
Lemma interp_id_id {E R} (t : itree E R) :
  interp (id_ E >>> id_ E) t ≈ t.
Proof.
  rewrite (fold_apply_IFun (interp _)).
  rewrite cat_id_r.
  rewrite <- fold_apply_IFun.
  rewrite interp_id_h.
  reflexivity.
Qed.

(* Regression test for #182 ([ITree.iter] should be executable even when the loop is infinite
   (the body is always [Ret (inl _)]) *)
Definition iter_spin : itree void1 void :=
  iter (C := ktree _) (fun _ : unit => Ret (@inl unit void tt)) tt.

Require Extraction.

(* This should NOT loop forever. *)
Extraction "output/test.ml" iter_spin.
