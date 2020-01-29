From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     Logic.Classical_Prop
     Logic.FunctionalExtensionality
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

Require Import Omega.
Require Import NArith.
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
  - exists n. cbn. tau_steps. reflexivity.
    (*getvar case, extract to a lemma*)
  - cbn. exists (lookup_default x 0 s). 
    tau_steps. reflexivity.
  - basic_solve. exists (n0 + n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 - n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
  - basic_solve. exists (n0 * n)%nat.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHae1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind. rewrite IHae2.
    tau_steps. reflexivity.
Qed.
     
    
Lemma bools_term : forall (be : bexp) (s : env),
    exists (bc : bool), @interp_imp Void _ (denote_bexp be) s ≈ Ret (s,bc).
Proof.
  intros. induction be.
  - exists true. cbn. unfold interp_imp, interp_map, interp_state. repeat rewrite interp_ret. 
    tau_steps. reflexivity.
  - exists false. tau_steps. reflexivity.
  - specialize (aexp_term Void a1 s) as Ha1. specialize (aexp_term Void a2 s) as Ha2.
    basic_solve. exists (n0 =? n).
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - specialize (aexp_term Void a1 s) as Ha1. specialize (aexp_term Void a2 s) as Ha2.
    basic_solve. exists (n0 <=? n).
    cbn. setoid_rewrite interp_imp_bind. rewrite Ha1.
    setoid_rewrite bind_ret. setoid_rewrite interp_imp_bind.
    rewrite Ha2. tau_steps. reflexivity.
  - basic_solve. exists (negb bc). cbn.
    setoid_rewrite interp_imp_bind. rewrite IHbe. tau_steps.
    reflexivity.
  - basic_solve. exists (bc0 && bc)%bool.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHbe1. setoid_rewrite bind_ret.
    cbn. setoid_rewrite interp_imp_bind. rewrite IHbe2. tau_steps.
    reflexivity.
Qed.

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
  match goal with | H : interp _ (?t0 ) _ ≈ _ |- _ => set t0 as t end.
  assert (t ≈ t); try reflexivity. unfold t in H2 at 2.
  
  setoid_rewrite interp_iter in H2. 
  match type of H2 with _ ≈ _ (fun _ => ?t0 ) _ => set t0 as while_body end.
  assert (while_body ≈ while_body); try reflexivity.
  unfold while_body in H3 at 2. 
  rewrite interp_bind in H3. fold while_body in H2.
  match type of H3 with _ ≈ ?t => set t as t' end.

  (*f (if b then x else y) = if b then f x else f y *)
  (*need good ways to streamline this interpretation*)
  match type of H3 with _ ≈ ITree.bind _ ?f => assert (eq2 f f) end; try reflexivity.
  assert (eq2 (fun r : bool =>
          interp (bimap handle_ImpState (id_ Void))
            (if r
             then ITree.bind (denote_com c) (fun _ : unit => Ret (inl tt))
             else Ret (inr tt)))
          (fun r : bool =>
          
            (if r
             then interp (bimap handle_ImpState (id_ Void)) (ITree.bind (denote_com c) (fun _ : unit => Ret (inl tt)))
             else interp (bimap handle_ImpState (id_ Void)) (Ret (inr tt))))).
  rewrite H4 in H3.

(*
  
  match goal with | H : context [KTree.iter (fun _ => ?body) _ ] |- _ => 
   set body as while_body end. fold while_body in H1.
  assert (while_body ≅ while_body); try reflexivity. 
  match goal with | H : interp ?f _ _ ≈ _ |- _ => set f as f' end. fold f' in H1.
  set (@interp_imp Void) as T. unfold interp_imp, interp_map, interp_state in T.
  unfold handle_ImpState in T. unfold handle_map in T.
  (*so apparently we interpret from impstateE into mapE and I don't like that
  *)
  
  unfold while_body in H2. fold f' in H2. setoid_rewrite bind_ret in H2. unfold denote_com in H2.
  specialize (@interp_imp_bind Void) as Hinterp. 
  unfold interp_imp, interp_map, interp_state in Hinterp.
  (*fold (@interp_imp Void _ (handle_map (id_ Void) ) ) in H2. *)
  setoid_rewrite interp_imp_bind in H2.
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
    runs a tactic a bunch*) *) Abort.

  
