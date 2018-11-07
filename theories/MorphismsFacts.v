From Paco Require Import paco.

From ITree Require Import
     ITree Morphisms Equivalence.

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

(* Failed naive attempt. (The [Tau] case is the interesting one.) *)
Lemma interp_bind_failed {E F R S}
      (f : eff_hom E F) (t : itree E R) (k : R -> itree E S) :
  ( interp f (t >>= k) ~
   (interp f  t >>= fun r => interp f (k r))).
Proof.
  revert t; pcofix interp_bind; rename r into e; intro t.
  pfold. constructor.
  { admit. }
  { admit. }
Abort.

Lemma interp_bind {E F R S}
      (f : eff_hom E F) (t : itree E R) (k : R -> itree E S) :
  ( interp f (t >>= k) ~
   (interp f  t >>= fun r => interp f (k r))).
Proof.
  revert t; pcofix interp_bind; rename r into e; intro t.
  pfold.
  split.
  - admit.
  - intros tk1' tk2' Htk1 Htk2.
    shelve.
Abort.
