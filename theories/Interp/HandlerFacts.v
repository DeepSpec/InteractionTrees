
(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Eq.UpToTausEquivalence
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts
     Interp.InterpFacts.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

Instance CatIdR_Handler : CatIdR Handler.
Proof.
  red; intros A B f X e.
  apply interp_id_h.
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
