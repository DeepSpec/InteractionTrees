(** * Mutable map whose lookup operation provides a default value.*)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Core.RelDec.

From ExtLib.Structures Require
     Functor Monoid Maps.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations
     ITree
     ITreeFacts
     Indexed.Sum
     Interp.Interp
     Events.State
     Events.StateFacts
     Events.MapDefault.

Import ITree.Basics.Basics.Monads.
Import Structures.Maps.
(* end hide *)

Section MapFacts.

  Variables (K V : Type).
  Context {map : Type}.
  Context {M : Map K V map}.
  Context {MOk: MapOk eq M}.
  Context {Kdec: @RelDec K eq}.
  Context {KdecOk: RelDec_Correct Kdec}.

  (* Should move to extlib *)
  Lemma lookup_add_eq: forall k v s, lookup k (add k v s) = Some v.
  Proof.
    intros.
    rewrite mapsto_lookup; apply mapsto_add_eq. 
    Unshelve.
    2: typeclasses eauto.
  Qed.

  (* Should move to extlib *)
  Lemma lookup_add_neq: forall k k' v s, k' <> k -> lookup k (add k' v s) = lookup k s.
  Proof.
    intros.
    generalize (@mapsto_add_neq _ _ _ eq _ _ s k' v k H); clear H; intros H.
    setoid_rewrite <- mapsto_lookup in H.
    destruct (lookup k s) as [v' |] eqn:EQ.
    - specialize (H v').
      apply H; auto.
    - destruct (lookup k (add k' v s)) as [v' |] eqn:EQ'; [| reflexivity].
      specialize (H v').
      symmetry; apply H; auto.
  Qed.

  (* Should move to extlib *)
  Lemma lookup_remove_eq:
    forall k s, lookup k (remove k s) = None.
  Proof.
    intros.
    match goal with
      |- ?x = _ => destruct x eqn:EQ
    end; [| reflexivity].
    rewrite mapsto_lookup in EQ.
    exfalso; eapply mapsto_remove_eq; eauto.
  Qed.

  (* Should move to extlib *)
  Lemma lookup_remove_neq:
    forall k k' s, k <> k' -> lookup k (remove k' s) = lookup k s.
  Proof.
    intros.
    match goal with
      |- ?x = _ => destruct x eqn:EQ
    end.
    - rewrite mapsto_lookup in EQ.
      apply mapsto_remove_neq in EQ; auto.
      symmetry; rewrite mapsto_lookup; eauto.
    -  match goal with
         |- _ = ?x => destruct x eqn:EQ'
       end; auto.
       rewrite mapsto_lookup in EQ'.
       eapply mapsto_remove_neq in EQ'; eauto.
       rewrite <- mapsto_lookup in EQ'.
       rewrite EQ in EQ'; inv EQ'.
       Unshelve.
       all: typeclasses eauto.
  Qed.

  Global Instance eq_map_refl {d} : Reflexive (@eq_map _ _ _ _ d).
  Proof.
    red. intros. unfold eq_map. tauto.
  Qed.    

  Global Instance eq_map_sym {d} : Symmetric (@eq_map _ _ _ _ d).
  Proof.
    repeat intro.
    unfold eq_map in H.
    rewrite H.
    reflexivity.
  Qed.

  Global Instance eq_map_trans {d} : Transitive (@eq_map _ _ _ _ d).
  Proof.
    repeat intro. 
    unfold eq_map in *.
    rewrite H. rewrite H0. reflexivity.
  Qed.


  Section Relations.
  Context {R1 R2 : Type}.
  Variable RR : R1 -> R2 -> Prop.

  Definition map_default_eq d {E} 
    : (stateT map (itree E) R1) -> (stateT map (itree E) R2) -> Prop :=
    fun t1 t2 => forall s1 s2, (@eq_map _ _ _ _ d) s1 s2 -> eutt (prod_rel (@eq_map _ _ _ _ d) RR) (t1 s1) (t2 s2).

  End Relations.

  Lemma eq_map_add:
    forall (d : V) (s1 s2 : map) (k : K) (v : V), (@eq_map _ _ _ _ d) s1 s2 -> (@eq_map _ _ _ _ d) (add k v s1) (add k v s2).
  Proof.
    intros d s1 s2 k v H.
    unfold eq_map in *.
    intros k'.
    destruct (rel_dec_p k k').
    - subst.
      unfold lookup_default in *.
      rewrite 2 lookup_add_eq; reflexivity.
    - unfold lookup_default in *.
      rewrite 2 lookup_add_neq; auto.
  Qed.      

  Lemma eq_map_remove:
    forall (d : V) (s1 s2 : map) (k : K), (@eq_map _ _ _ _ d) s1 s2 -> (@eq_map _ _ _ _ d) (remove k s1) (remove k s2).
  Proof.
    intros d s1 s2 k H.
    unfold eq_map in *; intros k'.
    unfold lookup_default.
    destruct (rel_dec_p k k').
    - subst; rewrite 2 lookup_remove_eq; auto.
    - rewrite 2 lookup_remove_neq; auto.
      apply H.
  Qed.
  
  Lemma handle_map_eq : 
    forall d E X (s1 s2 : map) (m : mapE K d X),
      (@eq_map _ _ _ _ d) s1 s2 ->
      eutt (prod_rel (@eq_map _ _ _ _ d) eq) (handle_map m s1) ((handle_map m s2) : itree E (map * X)).
  Proof.
    intros.
    destruct m; cbn; red; apply eqit_Ret; constructor; auto.
    - apply eq_map_add. assumption.
    - apply eq_map_remove. assumption.
  Qed.


  Global Instance Proper_handle_map {E R}  d :
    Proper (eq ==> map_default_eq eq d) (@handle_map _ _ _ _ E d R).
  Proof.
    repeat intro.
    subst.
    apply handle_map_eq.
    assumption.
  Qed.
    
  
  (* This lemma states that the operations provided by [handle_map] respect
     the equivalence on the underlying map interface *)
  Lemma interp_map_id d {E X} (t : itree (mapE K d +' E) X) :
    map_default_eq eq d (interp_map t) (interp_map t).
  Proof.
    unfold map_default_eq, interp_map; intros.
    revert t s1 s2 H.
    ginit.
    gcofix CH.
    intros.
    repeat rewrite unfold_interp_state. unfold _interp_state.
    destruct (observe t).
    - gstep. constructor. constructor; auto.
    - gstep. constructor. gbase. apply CH. assumption.
    - guclo eqit_clo_bind. econstructor.
      unfold pure_state.
      destruct e.
      + cbn. eapply eqit_mon. 4 : { apply handle_map_eq. assumption. }
        auto. auto. intros.  apply PR.
      + cbn. apply eqit_Vis. intros.  apply eqit_Ret. constructor; auto.
      + intros. destruct u1. destruct u2. cbn.
        inversion H. subst.
        gstep; constructor.
        gbase. apply CH. assumption.
  Qed.
 
  Global Instance interp_map_proper {R E d} {RR : R -> R -> Prop} :
    Proper ((eutt RR) ==> (@map_default_eq _ _ RR d E)) (@interp_map _ _ _ _ E d R).
  Proof.
    unfold map_default_eq, interp_map.
    repeat intro.
    revert x y H s1 s2 H0.
    einit.
    ecofix CH.
    intros.
    rewrite! unfold_interp_state. 
    punfold H0. red in H0.
    revert s1 s2 H1.
    induction H0; intros; subst; simpl; pclearbot.
    - eret. 
    - etau.
    - ebind.
      apply pbc_intro_h with (RU := prod_rel (@eq_map _ _ _ _ d) eq).
      { (* SAZ: I must be missing some lemma that should solve this case *)
        unfold case_. unfold Case_sum1, case_sum1.
        destruct e. apply handle_map_eq. assumption.
        unfold pure_state.
        pstep. econstructor. intros. constructor. pfold. econstructor. constructor; auto.
      } 
      intros.
      inversion H. subst.
      estep; constructor. ebase.
    - rewrite tau_euttge, unfold_interp_state.
      eauto.
    - rewrite tau_euttge, unfold_interp_state.
      eauto.
  Qed.
    
End MapFacts.
