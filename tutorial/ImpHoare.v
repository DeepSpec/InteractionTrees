From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
.

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
     Core.Divergence
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad
     Dijkstra.StateSpecT
   (*  Simple *)
.

Require Import Imp.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Import ImpNotations.
Local Open Scope imp_scope.
From Paco Require Import paco.


Definition denote_imp (c : com) : stateT env Delay unit :=
  interp_imp (denote_com c).

Definition hoare_triple (P Q : env -> Prop) (c : com) : Prop :=
  forall (s s' :env), P s -> (denote_imp c s ≈ ret (s',tt)) -> Q s'.

Definition lift_imp_post (P : env -> Prop) : Delay (env * unit) -> Prop :=
  fun (t : Delay (env * unit) ) => (exists (s : env), ret (s, tt) ≈ t /\ P s).

Notation "{{ P }} c {{ Q }}" := (hoare_triple P Q c) (at level 70).

Definition is_bool (E : Type -> Type) (bc : bool) (be : bexp) (s : env) : Prop :=
   @interp_imp E bool (denote_bexp be) s ≈ ret (s, bc).

Definition is_true (b : bexp) (s : env) : Prop :=
  is_bool Void true b s.

Definition is_false  (b : bexp) (s : env) : Prop :=
  is_bool Void false b s.

(*
Ltac unf_intep := unfold interp_imp, interp_map, interp_state, interp, Basics.iter, MonadIter_stateT0, interp, Basics.iter, MonadIter_stateT0.
*)

Lemma aexp_term : forall (E : Type -> Type) (ae : aexp) (s : env),
    exists (n : nat), @interp_imp Void _ (denote_aexp ae) s ≈ Ret (s,n).
Proof.
  intros. induction ae.
  - exists n. cbn.  unfold interp_imp, interp_map, interp_state. rewrite interp_ret. 
    unfold interp, Basics.iter, MonadIter_stateT0. setoid_rewrite unfold_iter_ktree.
    repeat setoid_rewrite bind_ret. cbn. reflexivity.
    (*getvar case, extract to a lemma*)
  - cbn. exists (lookup_default x 0 s). 
    unfold interp_imp, interp_map, interp_state. rewrite interp_trigger.
     unfold interp, Basics.iter, MonadIter_stateT0. setoid_rewrite unfold_iter_ktree.
     setoid_rewrite bind_bind. cbn. setoid_rewrite map_ret.
     setoid_rewrite bind_ret. cbn. setoid_rewrite bind_ret. 
     rewrite tau_eutt. setoid_rewrite unfold_iter_ktree.
     setoid_rewrite bind_bind. cbn. setoid_rewrite bind_ret.
     setoid_rewrite bind_ret. cbn. rewrite tau_eutt. 
     setoid_rewrite unfold_iter_ktree. cbn. setoid_rewrite bind_bind.
     setoid_rewrite bind_ret. setoid_rewrite bind_ret. cbn. reflexivity.
   - basic_solve. exists (n + n0)%nat.
     cbn.
     unfold interp_imp, interp_map, interp_state. rewrite interp_bind.
     unfold interp, Basics.iter, MonadIter_stateT0. setoid_rewrite unfold_iter_ktree.
     cbn. 
Admitted.
     
    
Lemma bools_term : forall (be : bexp) (s : env),
    exists (bc : bool), @interp_imp Void _ (denote_bexp be) s ≈ Ret (s,bc).
Proof.
  intros. induction be.
  - exists true. cbn. unfold interp_imp, interp_map, interp_state. repeat rewrite interp_ret. 
    unfold interp. unfold Basics.iter, MonadIter_stateT0.
    setoid_rewrite unfold_iter_ktree. setoid_rewrite bind_bind. cbn.
    repeat setoid_rewrite bind_ret. cbn. reflexivity.
  - exists false. cbn. unfold interp_imp, interp_map, interp_state. repeat rewrite interp_ret. 
    unfold interp. unfold Basics.iter, MonadIter_stateT0.
    setoid_rewrite unfold_iter_ktree. setoid_rewrite bind_bind. cbn.
    repeat setoid_rewrite bind_ret. cbn. reflexivity.
  -
Admitted.

Lemma classic_bool : forall (b : bexp) (s : env), is_true b s \/ is_false b s.
Proof.
  intros. specialize (bools_term b s) as Hbs. 
  basic_solve. destruct bc; auto.
Qed.

(*   *)

Lemma hoare_seq : forall (c1 c2 : com) (P Q R : env -> Prop), {{P}} c1 {{Q}} -> {{Q}} c2 {{R}}  ->
                                                               {{P}} c1 ;;; c2 {{R}}.
Proof.
  unfold hoare_triple. intros c1 c2 P Q R Hc1 Hc2 s s' Hs Hs'.
  unfold denote_imp in Hs'. cbn in Hs'. rewrite interp_imp_bind in Hs'. 
  fold (denote_imp c1) in Hs'. fold (denote_imp c2) in Hs'.
  destruct (eutt_reta_or_div _ (denote_imp c1 s) ); basic_solve.
  - destruct a as [s'' [] ]. rewrite <- H in Hs'. setoid_rewrite bind_ret in Hs'. symmetry in H.
    eapply Hc2; eauto.
  - apply div_spin_eutt in H. rewrite H in Hs'. rewrite <- spin_bind in Hs'.
    symmetry in Hs'. exfalso. eapply not_ret_eutt_spin. eauto.
Qed.

Lemma hoare_if : forall (c1 c2 : com) (b : bexp) (P Q : env -> Prop),
    {{fun s => is_true b s /\ P s}} c1 {{Q}} ->
    {{fun s => is_false b s /\ P s}} c2 {{Q}} ->
    {{ P }} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  unfold hoare_triple. intros c1 c2 b P Q Hc1 Hc2 s s' Hs.
  unfold denote_imp. cbn.
  destruct (classic_bool b s).
  - unfold is_true, is_bool in H. rewrite interp_imp_bind.
    rewrite H. setoid_rewrite bind_ret. apply Hc1. auto.
  - unfold is_false, is_bool in H. rewrite interp_imp_bind.
    rewrite H. setoid_rewrite bind_ret. apply Hc2. auto.
Qed.

Lemma hoare_while : forall (c : com) (b : bexp) (P : env -> Prop),
    {{fun s => is_true b s /\ P s}} c {{ P  }} ->
    {{ P }} WHILE b DO c END {{ fun s => is_false b s /\ P s}}.
Proof.
  unfold hoare_triple. intros. unfold denote_imp in H1. cbn in H1.
  unfold while in H1. unfold interp_imp, interp_map, interp_state in H1.
  (*this moves interp inside the iter*)
  setoid_rewrite interp_iter in H1.
  unfold interp at 1 in H1.
  match goal with | H : context [KTree.iter (fun _ => ?body) _ ] |- _ => 
   set body as while_body end. fold while_body in H1.
  unfold Basics.iter, MonadIter_stateT0 in H1.
  (*this context is probably proper with eq_itree*)

  match goal with | H : Basics.iter ?g ?a  ≈ _ |- _ => set g as g'; set a as a' end. 

  fold g' in H1. fold a' in H1.
  set (iter_arrow_rel g') as rg'.
  destruct (classic_wf _ rg' a').
  - unfold a' in H2. induction H2.
    + unfold rg' in H2. unfold iter_arrow_rel in H2.
      setoid_rewrite unfold_iter_ktree in H1.
      destruct (eutt_reta_or_div _ (g' a) ); basic_solve.
      * symmetry in H3. exfalso. eapply H2; eauto.
      * destruct b0 as [s'' [] ]. rewrite <- H3 in H1.
        setoid_rewrite bind_ret in H1. basic_solve.
        unfold g' in H3.
        destruct a as [s'' t]. simpl in *.
        destruct (observe t) eqn : Heq.
        -- setoid_rewrite bind_ret in H3. simpl in *.
           basic_solve.
        
  - apply iter_inl_spin in H2. rewrite H2 in H1. symmetry in H1.
    exfalso.
    eapply not_ret_eutt_spin.  eauto.
  (*probably need to induce that arrow relation again*)
  (*invariant is something that has a few cases*)
  (*does burn preserve eutt? if so maybe write a tactic that just
    runs a tactic a bunch*)

  
