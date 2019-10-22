Require Import Imp.
Require Import Paco.paco.
From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     StateFacts
     StateKleisli
     Eq.
From Coq Require Import
     String
     Setoid
     Morphisms
     Arith.

(**
   The chapter [Equiv] from _Programming Language Foundations_ introduced a
   notion of behavioral equivalence over _Imp_ programs.
   Two _com_ [c_1] and [c_2] were said to be equivalent if for any initial state,
   [c_1] reduced according to the language's big step semantics to a final state
   if and only if [c_2] reduced to the same final state.
   We investigate in this chapter how behavioral equivalence is phrased at the
   level of itrees, and how it can be proved on simple examples.
*)

(* Defining the notion at the itree level offers the benefit of uniformity:
   the notion is language independent.
   YZ: Not really though, depends on the interpretation obviously
 *)

Definition run_state {E A} (R : Monads.stateT env (itree E) A) (st: env) : itree E (env * A) :=     R st.

Definition aequiv_strong (a1 a2: aexp): Prop :=
  denote_aexp a1 ≈ denote_aexp a2.

Definition eval_aexp (a: aexp) :=
  @interp_imp void1 value (denote_aexp a).

Definition aequiv (a1 a2: aexp): Prop :=
  forall s, run_state (eval_aexp a1) s ≈ run_state (eval_aexp a2) s.

Definition cequiv (c1 c2: com): Prop :=
  forall s, run_state (@interp_imp void1 _ (denote_com c1)) s ≈ run_state (interp_imp (denote_com c2)) s.

Section Examples.

  Import ImpNotations.

  Definition W : string := "W".
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".

  Lemma interp_imp_ret: forall {R} (v: R) (E: Type -> Type) (g : env),
     run_state (interp_imp (Ret v)) g ≅ (Ret (g, v) : itree E (env * R)).  
  Proof.
    intros.
    unfold interp_imp, interp_map, run_state.
    rewrite interp_ret. 
    rewrite interp_state_ret.
    reflexivity.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S E} (t: itree (ImpState +' E) R) (k: R -> itree (ImpState +' E) S) (g : env),
      run_state (interp_imp (ITree.bind t k)) g
    ≅ (ITree.bind (run_state (interp_imp t) g) (fun '(g',  x) => run_state (interp_imp (k x)) g')).
  Proof.
    intros.
    unfold interp_imp.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
  Admitted. 
 
  
  Instance run_state_proper {E A} : Proper (eqm ==> eq ==> eutt eq) (@run_state E A).
  Admitted.

  Instance interp_state_proper {T E F S} (h: forall T : Type, E T -> Monads.stateT S (itree F) T) : Proper (eutt eq ==> eqm) (State.interp_state h (T := T)).
  Admitted. 

  Lemma interp_imp_trigger_get_var: forall (E: Type -> Type) (x: var) (g: env),
    run_state (interp_imp (trigger (GetVar x))) g ≈ (Ret (g, lookup_default x 0 g) : itree E (env * value)).
  Proof.
    intros. unfold interp_imp, interp_map. rewrite interp_trigger.
    rewrite tau_eutt. cbn. unfold cat, Cat_Handler, Handler.cat.
  Admitted. 
                                                                                                     
  Theorem aequiv_example: aequiv (X - X) 0.
  Proof.
    unfold aequiv. intros s. unfold eval_aexp. simpl.
    rewrite interp_imp_ret.   
    rewrite interp_imp_bind.
    rewrite interp_imp_trigger_get_var.
    rewrite bind_ret, interp_imp_bind, interp_imp_trigger_get_var, bind_ret, interp_imp_ret.
    cbn. rewrite Nat.sub_diag.
    reflexivity.
  Qed. 
    
    
      
   
