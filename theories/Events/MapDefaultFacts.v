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
    intros.
    unfold lookup_default in *.
  Admitted.

  Lemma eq_map_remove:
    forall (d : V) (s1 s2 : map) (k : K), (@eq_map _ _ _ _ d) s1 s2 -> (@eq_map _ _ _ _ d) (remove k s1) (remove k s2).
  Proof.
    intros d s1 s2 k H.
  Admitted.

  
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
  Lemma run_map_id d {E X} (t : itree (mapE K d +' E) X) :
    map_default_eq eq d (run_map t) (run_map t).
  Proof.
    unfold map_default_eq, run_map; intros.
    revert t s1 s2 H.
    ginit.
    gcofix CH.
    intros.
    repeat rewrite unfold_interp_state. unfold _interp_state.
    destruct (observe t).
    - gstep. constructor. constructor; auto.
    - gstep. constructor. gbase. apply CH. assumption.
    - gstep. constructor.
      guclo eqit_clo_bind. econstructor.
      unfold pure_state.
      destruct e.
      + cbn. eapply eqit_mon. 4 : { apply handle_map_eq. assumption. }
        auto. auto. intros.  apply PR.
      + cbn. apply eqit_Vis. intros.  apply eqit_Ret. constructor; auto.
      + intros. destruct u1. destruct u2. cbn.
        inversion H. subst.
        gbase. apply CH. assumption.
  Qed.
 
  Global Instance run_map_proper {R E d} {RR : R -> R -> Prop} :
    Proper ((eutt RR) ==> (@map_default_eq _ _ RR d E)) (@run_map _ _ _ _ E d R).
  Proof.
    unfold map_default_eq, run_map.
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
    - etau.
      ebind.
      apply pbc_intro_h with (RU := prod_rel (@eq_map _ _ _ _ d) eq).
      { (* SAZ: I must be missing some lemma that should solve this case *)
        unfold case_. unfold Case_sum1, case_sum1.
        destruct e. apply handle_map_eq. assumption.
        unfold pure_state.
        pstep. econstructor. intros. constructor. pfold. econstructor. constructor; auto.
      } 
      intros.
      inversion H. subst.
      simpl.
      ebase.
    - rewrite tau_eutt, unfold_interp_state.
      eauto.
    - rewrite tau_eutt, unfold_interp_state.
      eauto.
  Qed.
    
  
End MapFacts.