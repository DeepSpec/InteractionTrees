(** * Theorems for [ITree.Interp.Handler] *)

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
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts
     Interp.InterpFacts
     Interp.RecursionFacts.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

(* end hide *)

Section HandlerCategory.

Local Opaque eutt ITree.bind' interp Recursion.mrec ITree.trigger.

Instance Proper_Cat_Handler {A B C}
  : @Proper (Handler A B -> Handler B C -> Handler A C)
            (eq2 ==> eq2 ==> eq2)
            cat.
Proof.
  cbv; intros.
  apply eutt_interp; auto.
Qed.

Instance CatIdR_Handler : CatIdR Handler.
Proof.
  cbv; intros.
  rewrite interp_trigger_h. reflexivity.
Qed.

Instance CatIdL_Handler : CatIdL Handler.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CatAssoc_Handler : CatAssoc Handler.
Proof.
  cbv; intros.
  rewrite interp_interp.
  reflexivity.
Qed.

Global Instance Category_Handler : Category Handler.
Proof.
  split; typeclasses eauto.
Qed.

Global Instance InitialObject_Handler : InitialObject Handler void1.
Proof.
  cbv; contradiction.
Qed.

Instance Proper_Case_Handler {A B C}
  : @Proper (Handler A C -> Handler B C -> Handler (A +' B) C)
            (eq2 ==> eq2 ==> eq2)
            case_.
Proof.
  cbv; intros.
  destruct (_ : sum1 _ _ _); auto.
Qed.

Instance CaseInl_Handler : CaseInl Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CaseInr_Handler : CaseInr Handler sum1.
Proof.
  cbv; intros.
  rewrite interp_trigger, tau_eutt.
  reflexivity.
Qed.

Instance CaseUniversal_Handler : CaseUniversal Handler sum1.
Proof.
  cbv; intros.
  destruct (_ : sum1 _ _ _).
  - rewrite <- H, interp_trigger, tau_eutt. reflexivity.
  - rewrite <- H0, interp_trigger, tau_eutt. reflexivity.
Qed.

Global Instance Coproduct_Handler : Coproduct Handler sum1.
Proof.
  split; typeclasses eauto.
Qed.

Instance Proper_Iter_Handler {A B}
  : @Proper (Handler A (A +' B) -> Handler A B)
            (eq2 ==> eq2)
            iter.
Proof.
Abort. (** TODO *)

Instance IterUnfold_Handler : IterUnfold Handler sum1.
Proof.
  cbv; intros.
  rewrite mrec_as_interp.
  reflexivity.
Qed.

Instance IterNatural_Handler : IterNatural Handler sum1.
Proof.
Abort.

Instance IterDinatural_Handler : IterDinatural Handler sum1.
Proof.
Abort.

Instance IterCodiagonal_Handler : IterCodiagonal Handler sum1.
Proof.
Abort.

Instance Conway_Handler : Conway Handler sum1.
Proof.
Abort.

End HandlerCategory.
