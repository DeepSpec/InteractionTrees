From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     Events.Exception
     Core.Divergence
     Dijkstra.TracesIT
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
     Secure.SecureEqWcompat
     Secure.SecureEqBind
     Secure.SecureStateHandler
     Secure.StrongBisimProper
.

From SecureExample Require Import 
     LabelledImp
     Lattice
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

From Paco Require Import paco.

Section LabelledImpHandler.

Context (Labels : Lattice).

Definition priv_io (A : Type) (e : IOE Labels A) :=
  match e with
  | LabelledPrint _ s _ => s end.


Definition priv_exc (A : Type) (e : impExcE Labels A ) :=
  match e with
  | Throw _ s => s end.

Definition priv_exc_io := case_ priv_exc priv_io.

Definition product_rel {R1 R2 S1 S2} (RR1: R1 -> S1 -> Prop) (RR2 : R2 -> S2 -> Prop) 
           (p1 : R1 * R2) (p2 : S1 * S2) : Prop :=
  RR1 (fst p1) (fst p2) /\ RR2 (snd p1) (snd p2). 

Definition handle_case {E1 E2 : Type -> Type} {M : Type -> Type} (hl : E1 ~> M) (hr : E2 ~> M) : (E1 +' E2) ~> M :=
  fun _ e => match e with
          | inl1 el => hl _ el
          | inr1 er => hr _ er end.

Definition handle_state_io : forall A, (stateE +' (IOE Labels)) A ->
                                  stateT map (itree ((impExcE Labels) +' (IOE Labels))) A :=
  fun _ e => match e with
          | inl1 el => handleState _ el
          | inr1 er => fun s => r <- ITree.trigger (inr1 er);; Ret (s, r) end. 

Definition handle_imp : forall A, ((impExcE Labels) +' stateE +' (IOE Labels)) A ->
                             stateT map (itree ((impExcE Labels) +' (IOE Labels)) ) A :=
  fun _ e => match e with
          | inl1 el => fun s => r <- ITree.trigger (inl1 el);; Ret (s, r)
          | inr1 er => handle_state_io _ er end.

Definition interp_imp {R} (t : itree ((impExcE Labels) +' stateE +' (IOE Labels)) R ) : stateT map (itree ((impExcE Labels) +' (IOE Labels))) R :=
  interp_state handle_imp t. 

Hint Unfold interp_imp.
Hint Unfold handle_state_io.
Hint Unfold handle_imp.
Hint Unfold product_rel.
(*
Ltac use_simpobs :=
  repeat match goal with 
         | H : TauF _ = observe ?t |- _ => apply simpobs in H 
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

Ltac destruct_imp_ev := repeat match goal with
                        | e : (?E1 +' ?E2) ?A |- _ => destruct e
                        | exc : impExcE ?A |- _ => destruct exc
                        | st : stateE ?A |- _ => destruct st
                        | io : IOE ?A |- _ => destruct io
                        end.

 (* TODO : replace with labelled equiv *)
Lemma interp_eqit_secure_imp : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (priv_map : privacy_map) 
                                 (t1 : itree (impExcE +' stateE +' IOE) R1 ) 
                                 (t2 : itree (impExcE +' stateE +' IOE) R2),
    eqit_secure sense_preorder (priv_imp priv_map) RR true true Public t1 t2 ->
    low_eqit_secure_impstate true true priv_map RR (interp_imp t1 )  (interp_imp t2).
Proof.
  red. intros.
  eapply interp_eqit_secure_state; eauto.
  - constructor; red; intros; cbv; intros; auto. red in H1. rewrite H1; auto.
    rewrite H1; auto.
  - intros. destruct_imp_ev.
    + destruct s.
      * eapply respect_public'. cbv. auto. red. intros. cbn.
        setoid_rewrite bind_trigger. apply eqit_secure_public_Vis. cbv. auto.
        intros [].
      * eapply respect_private_e. cbv. auto. constructor. intros [].
        intros. setoid_rewrite bind_trigger. pfold. constructor. intros [].
        cbv. auto.
    + destruct (priv_map x) eqn : Hl.
      * apply respect_public'. cbv. rewrite Hl. auto.
        red. intros. cbn. apply secure_eqit_ret.  split; auto. cbv. rewrite H1; auto.
      * apply respect_private_ne. cbv. rewrite Hl. auto.
        constructor. exact 0. intros. cbn. apply terminates_ret. red. intros. auto.
    + destruct (priv_map x) eqn : Hl.
      * apply respect_public'. cbv. rewrite Hl. auto.
        red. intros. cbn. apply secure_eqit_ret. split; auto.
        cbn. apply low_equiv_update_public; auto.
      * apply respect_private_ne. cbv. rewrite Hl. auto.
        constructor. exact tt. intros. cbn. apply terminates_ret.
        apply low_equiv_update_private_r; auto. red; intros; auto.
    + destruct s.
      * eapply respect_public'. cbv. auto. red. intros. cbn.
        setoid_rewrite bind_trigger. apply eqit_secure_public_Vis. cbv. auto.
        intros []. apply secure_eqit_ret. split; auto.
      * eapply respect_private_ne. cbv. auto. constructor. exact tt.
        intros. cbn. setoid_rewrite bind_trigger. apply terminates_vis.
        intros []. apply terminates_ret. red; intros; auto.
         cbn. split; auto. constructor. exact tt.
Qed.
*)
End LabelledImpHandler.
