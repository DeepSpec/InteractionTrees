
(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITree
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts
     Interp.MorphismsFacts.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

Lemma eh_cmp_id_left_strong {A R} (t : itree A R)
  : interp (id_ A) R t ≈ t.
Proof.
  pupto2_init; revert t; pcofix CIH; intros t.
  pfold; pupto2_init; revert t; pcofix CIH'; intros.
  rewrite unfold_interp. unfold interp_u.
  destruct (observe t); cbn; eauto.
  - pfold. econstructor. auto.
  - unfold id_, Id_Handler, ITree.liftE. rewrite vis_bind_.
    pfold; do 2 constructor.
    left; rewrite ret_bind; auto.
Qed.

Instance CatIdR_Handler : CatIdR Handler.
Proof.
  red; intros A B f X e.
  apply eh_cmp_id_left_strong.
Qed.

Instance CatIdL_Handler : CatIdL Handler.
Proof.
  red; intros A B f X e.
  unfold cat, Cat_Handler, id_, Id_Handler.
  rewrite interp_liftE, tau_eutt.
  reflexivity.
Qed.

Instance AssocCat_Handler : AssocCat Handler.
Proof.
  red; intros A B C D f g h X e.
  unfold cat, Cat_Handler.
  rewrite interp_interp.
  reflexivity.
Qed.
