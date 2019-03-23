
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
  revert t. ucofix CIH. red. ucofix CIH'. intros.
  rewrite unfold_interp. unfold _interp. repeat red.
  destruct (observe t); cbn; eauto 8 with paco.
  unfold id_, Id_Handler, Handler.id_, ITree.send. eutt0_fold. rewrite bind_vis_.
  do 2 constructor.
  left; rewrite bind_ret; auto with paco.
Qed.

Instance CatIdR_Handler : CatIdR Handler.
Proof.
  red; intros A B f X e.
  apply eh_cmp_id_left_strong.
Qed.

Instance CatIdL_Handler : CatIdL Handler.
Proof.
  red; intros A B f X e.
  unfold cat, Cat_Handler, Handler.cat, id_, Id_Handler, Handler.id_.
  rewrite interp_send, tau_eutt.
  reflexivity.
Qed.

Instance CatAssoc_Handler : CatAssoc Handler.
Proof.
  red; intros A B C D f g h X e.
  unfold cat, Cat_Handler, Handler.cat.
  rewrite interp_interp.
  reflexivity.
Qed.
