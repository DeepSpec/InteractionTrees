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
     Secure.SecureEqEuttTrans
     Secure.SecureEqProgInsens
     Secure.SecureEqProgInsensFacts
.

From SecureExample Require Import 
     Utils_tutorial
     Fin
     KTreeFin
     LabelledImp
     LabelledAsm
     LabelledAsmCombinators
     LabelledImp2Asm
     LabelledImp2AsmCorrectness
     LabelledImpHandler
     LabelledImpTypes
     LabelledImpTypesProgInsens
     Lattice
.

Import ITreeNotations.

Import Monads.
Open Scope monad_scope.


Section SecurityPreservation.

Context (Γ : var -> sensitivity).
Context (l : sensitivity).

Instance labell_equiv_equiv {Γ' l'} : Equivalence (labelled_equiv sensitivity_lat Γ' l').
Proof.
  constructor; red; intros; red; red; intros; auto.
  - rewrite H; auto.
  - rewrite H; auto.
Qed.

Definition labelled_sim : map -> (registers * memory) -> Prop :=
  fun g_imp g_asm => labelled_equiv sensitivity_lat Γ l g_imp (snd g_asm).

Definition asm_eq : registers * memory -> registers * memory -> Prop :=
  fun '(regs1, mem1) '(regs2, mem2) => labelled_equiv sensitivity_lat Γ l mem1 mem2.

Lemma state_rel_aux:
  forall (p1 : map * unit) (p2 : registers * memory * fin 1),
    rcompose (product_rel (labelled_equiv sensitivity_lat Γ l) eq) (state_invariant TT) p1 p2 ->
    product_rel labelled_sim TT p1 p2.
Proof.
  intros [σ [] ] [ [regs mem] ?] Hcomp. inv Hcomp.
  destruct r2 as [σ' [] ]. destruct REL1. split; red; auto.
  cbn. red in REL2. destruct REL2 as [Hst _ ]. cbn in *.
  assert (labelled_equiv _ Γ l σ' mem).
  { red in Hst. do 2 red. intros. auto. }
  etransitivity; eauto.
Qed.

Lemma state_rel_aux':
  forall x0 x1 : registers * memory * fin 1,
    flip
      (rcompose
         (flip
            (rcompose (product_rel (LabelledImpTypes.labelled_equiv sensitivity_lat Γ l) (@eq unit) )
                      (state_invariant TT))) (state_invariant TT)) x0 x1 ->
    product_rel asm_eq eq x0 x1.
Proof.
  intros [ [regs1  mem1] ? ] [ [reg2 mem2] ? ].
  intros H. inv H. inv REL1. split; cbn.
  2 :  setoid_rewrite unique_f0; auto.
   inv REL0. inv REL3. inv REL2. destruct r0. destruct r2. cbn in *.
   subst. transitivity m0.
   cbv; intros; auto. transitivity m; auto. cbv; intros; auto.
Qed.

Section ProgressSensitive.

Definition labelled_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree ((impExcE _) +' stateE +' (IOE _)) A ) (t2 : itree ((impExcE _) +'
 Reg +' Memory +' (IOE _)) B) :=
  forall (g_imp : map) (g_asm : memory) (regs : registers),
    labelled_equiv _ Γ l g_imp g_asm ->
    eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel labelled_sim RAB) true true l (interp_imp _ t1 g_imp ) (interp_asm t2 (regs, g_asm)).

Lemma compile_preserves_ps_security : forall (c : stmt _),
    label_state_sec_eutt _ Γ l eq  (interp_imp _ (denote_stmt _ c)) (interp_imp _ (denote_stmt _ c)) ->
    labelled_bisimilar TT (denote_stmt _ c) (denote_asm (compile c) f0 ) .
Proof.
  intros s Hsecs. red in Hsecs. red. intros g_imp g_asm regs Hs.
  assert (labelled_equiv _ Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm Hs).
  specialize (Heutt g_asm g_asm regs H0) .
  specialize (eutt_secure_eqit_secure) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Heutt.
  apply state_rel_aux; auto.
Qed.

Lemma compile_preserves_ps_ni : forall (c : stmt _),
    label_state_sec_eutt _ Γ l eq  (interp_imp _ (denote_stmt _ c)) (interp_imp _ (denote_stmt _ c)) ->
    forall σ1 σ2, asm_eq σ1 σ2 -> 
             eqit_secure _ (priv_exc_io _) (product_rel asm_eq eq) true true l
             (interp_asm (denote_asm (compile c) f0) σ1) ((interp_asm (denote_asm (compile c) f0)) σ2).
Proof.
  intros c Hsecc [regs1 mem1] [regs2 mem2]. intros Hasmeq.
  assert (labelled_equiv _ Γ l mem1 mem1). reflexivity.
  assert (labelled_equiv _ Γ l mem2 mem2). reflexivity.
  specialize (compile_correct c) as Heutt. do 2 red in Heutt.
  assert (Renv mem1 mem1). reflexivity.
  assert (Renv mem2 mem2). reflexivity.
  do 2 red in Hsecc.
  assert (Hmem12 : labelled_equiv _ Γ l mem1 mem2). auto.
  specialize (Hsecc mem1 mem2 Hmem12) as Hsecc'.
  specialize (Heutt mem1 mem1 regs1 H1) as Heutt1.
  specialize (Heutt mem2 mem2 regs2 H2) as Heutt2.
  specialize (eutt_secure_eqit_secure) as Htrans.
  eapply Htrans in Heutt1 as Heutt1'; eauto.
  eapply Htrans in Heutt2 as Heutt2'; eauto. 
  eapply Htrans in Hsecc'; eauto.
  apply eqit_secure_sym in Hsecc'.
  eapply Htrans in Hsecc'; eauto.
  apply eqit_secure_sym in Hsecc'.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Hsecc'; eauto.
  intros.
  apply state_rel_aux'; auto.
Qed.

  
End ProgressSensitive.

Section ProgressInsensitive.

Definition labelled_pi_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree ((impExcE _) +' stateE +' (IOE _)) A ) (t2 : itree ((impExcE _) +'
 Reg +' Memory +' (IOE _)) B) :=
  forall (g_imp : map) (g_asm : memory) (regs : registers),
    labelled_equiv _ Γ l g_imp g_asm ->
    pi_eqit_secure _ (priv_exc_io _) (product_rel labelled_sim RAB) true true l (interp_imp _ t1 g_imp ) (interp_asm t2 (regs, g_asm)).

Lemma compile_preserves_pi_security : forall (c : stmt _),
    label_state_pi_sec_eutt _ Γ l eq  (interp_imp _ (denote_stmt _ c)) (interp_imp _ (denote_stmt _ c)) ->
    labelled_pi_bisimilar TT (denote_stmt _ c) (denote_asm (compile c) f0 ) .
Proof.
  intros s Hsecs. red in Hsecs. red. intros g_imp g_asm regs Hs.
  assert (labelled_equiv _ Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm Hs).
  specialize (Heutt g_asm g_asm regs H0) .
  specialize (pi_eqit_secure_mixed_trans) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply pi_eqit_secure_RR_imp; try apply Heutt.
  apply state_rel_aux; auto.
Qed.

Lemma compile_preserves_pi_ni : forall (c : stmt _),
    label_state_pi_sec_eutt _ Γ l eq  (interp_imp _ (denote_stmt _ c)) (interp_imp _ (denote_stmt _ c)) ->
    forall σ1 σ2, asm_eq σ1 σ2 -> 
             pi_eqit_secure _ (priv_exc_io _) (product_rel asm_eq eq) true true l
             (interp_asm (denote_asm (compile c) f0) σ1) ((interp_asm (denote_asm (compile c) f0)) σ2).
Proof.
  intros c Hsecc [regs1 mem1] [regs2 mem2]. intros Hasmeq.
  assert (labelled_equiv _ Γ l mem1 mem1). reflexivity.
  assert (labelled_equiv _ Γ l mem2 mem2). reflexivity.
  specialize (compile_correct c) as Heutt. do 2 red in Heutt.
  assert (Renv mem1 mem1). reflexivity.
  assert (Renv mem2 mem2). reflexivity.
  do 2 red in Hsecc.
  assert (Hmem12 : labelled_equiv _ Γ l mem1 mem2). auto.
  specialize (Hsecc mem1 mem2 Hmem12) as Hsecc'.
  specialize (Heutt mem1 mem1 regs1 H1) as Heutt1.
  specialize (Heutt mem2 mem2 regs2 H2) as Heutt2.
  specialize (pi_eqit_secure_mixed_trans) as Htrans.
  eapply Htrans in Heutt1 as Heutt1'; eauto.
  eapply Htrans in Heutt2 as Heutt2'; eauto. 
  eapply Htrans in Hsecc'; eauto.
  apply pi_eqit_secure_sym in Hsecc'.
  eapply Htrans in Hsecc'; eauto.
  apply pi_eqit_secure_sym in Hsecc'.
  eapply pi_eqit_secure_RR_imp; try apply Hsecc'; eauto.
  intros.
  apply state_rel_aux'; auto.
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
