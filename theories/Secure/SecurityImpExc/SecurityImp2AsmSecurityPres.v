From Coq Require Import
     Strings.String
     List
     Program.Basics
     Morphisms
     ZArith
     Setoid
     RelationClasses.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.CategorySub
     Basics.HeterogeneousRelations
     Events.StateFacts
     Events.MapDefault
     Secure.SecureEqHalt
     Secure.SecurityImpExc.SecurityImp
     Secure.SecurityImpExc.SecurityImpHandler
     Secure.SecurityImpExc.SecurityAsm
     Secure.SecurityImp.Utils_tutorial
     Secure.SecurityImpExc.SecurityAsmCombinators
     Secure.SecurityImpExc.SecurityImp2Asm
     Secure.SecurityImp.Fin
     Secure.SecurityImp.KTreeFin
     Secure.SecurityImpExc.SecurityImp2AsmCorrectness
     Secure.SecureEqEuttTrans
     Secure.SecurityImpExc.SecurityImpTypes
     Secure.SecureEqProgInsens
     Secure.SecureEqProgInsensFacts
     Secure.SecurityImpExc.SecurityImpTypesProgInsens
.

Import ITreeNotations.

Import Monads.
Open Scope monad_scope.


Section SecurityPreservation.

Context (Γ : var -> sensitivity).
Context (l : label).

Definition labelled_sim : map -> (registers * memory) -> Prop :=
  fun g_imp g_asm => labelled_equiv Γ l g_imp (snd g_asm).

Lemma state_rel_aux:
  forall (p1 : map * unit) (p2 : registers * memory * fin 1),
    rcompose (product_rel (labelled_equiv Γ l) eq) (state_invariant TT) p1 p2 ->
    product_rel labelled_sim TT p1 p2.
Proof.
  intros [σ [] ] [ [regs mem] ?] Hcomp. inv Hcomp.
  destruct r2 as [σ' [] ]. destruct REL1. split; red; auto.
  cbn. red in REL2. destruct REL2 as [Hst _ ]. cbn in *.
  assert (labelled_equiv Γ l σ' mem).
  { red in Hst. do 2 red. intros. auto. }
  etransitivity; eauto.
Qed.

Section ProgressSensitive.

Definition labelled_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree (impExcE +' stateE +' IOE) A ) (t2 : itree (impExcE +'
 Reg +' Memory +' IOE) B) :=
  forall (g_imp : map) (g_asm : memory) (regs : registers),
    labelled_equiv Γ l g_imp g_asm ->
    eqit_secure sense_preorder priv_exc_io (product_rel labelled_sim RAB) true true l (interp_imp t1 g_imp ) (interp_asm t2 (regs, g_asm)).

Lemma compile_preserves_ps_security : forall (c : stmt),
    label_state_sec_eutt Γ l eq  (interp_imp (denote_stmt c)) (interp_imp (denote_stmt c)) ->
    labelled_bisimilar TT (denote_stmt c) (denote_asm (compile c) f0 ) .
Proof.
  intros s Hsecs. red in Hsecs. red. intros g_imp g_asm regs Hs.
  assert (labelled_equiv Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm Hs).
  specialize (Heutt g_asm g_asm regs H0) .
  specialize (eutt_secure_eqit_secure) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Heutt.
  apply state_rel_aux; auto.
Qed.
End ProgressSensitive.

Section ProgressInsensitive.

Definition labelled_pi_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree (impExcE +' stateE +' IOE) A ) (t2 : itree (impExcE +'
 Reg +' Memory +' IOE) B) :=
  forall (g_imp : map) (g_asm : memory) (regs : registers),
    labelled_equiv Γ l g_imp g_asm ->
    pi_eqit_secure sense_preorder priv_exc_io (product_rel labelled_sim RAB) true true l (interp_imp t1 g_imp ) (interp_asm t2 (regs, g_asm)).

Lemma compile_preserves_pi_security : forall (c : stmt),
    label_state_pi_sec_eutt Γ l eq  (interp_imp (denote_stmt c)) (interp_imp (denote_stmt c)) ->
    labelled_pi_bisimilar TT (denote_stmt c) (denote_asm (compile c) f0 ) .
Proof.
  intros s Hsecs. red in Hsecs. red. intros g_imp g_asm regs Hs.
  assert (labelled_equiv Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm Hs).
  specialize (Heutt g_asm g_asm regs H0) .
  Locate proper_eutt_pi_secure_eutt.
  specialize (pi_eqit_secure_mixed_trans) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply pi_eqit_secure_RR_imp; try apply Heutt.
  apply state_rel_aux; auto.
Qed.


End ProgressInsensitive.

  
End SecurityPreservation.
(*
stmt :=
     | throw
     | try c1 catch c2

itree (state +' IOE +' Exc) tt


denote_throw := trigger Throw


denote_catch



block := ...
         | throw


compile p : asm 1 1


compile p : asm 1 2

*)
