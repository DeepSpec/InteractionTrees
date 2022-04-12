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
     LabelledImpInline
     LabelledAsm
     LabelledImpInline2Asm
     LabelledImpInline2AsmCorrectness
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

Section ProgressSensitive.

Definition labelled_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree ((impExcE _) +' Reg +' Memory +' (IOE _)) A ) (t2 : itree ((impExcE _) +'
 Reg +' Memory +' (IOE _)) B) :=
  forall (g_imp : map) (g_asm : memory) (regs1 regs2 : registers),
    labelled_equiv _ Γ l g_imp g_asm ->
    (*  maybe I can refactor the double product_rel to something nicer, labelled_equiv instead of Renv? *)
    eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 Renv) RAB) true true l 
                (interp_asm t1 (regs1, g_imp )) (interp_asm t2 (regs2, g_asm)).

Lemma compile_preserves_ps_security : forall (c : stmt _),
    valid_stmt c ->
    labelled_bisimilar TT (denote_stmt _ c) (denote_stmt _ c) ->
    labelled_bisimilar TT (denote_stmt _ c) (denote_asm _ (compile c) f0 ) .
Proof.
  intros s Hs Hsecs. red in Hsecs. red. intros g_imp g_asm regs1 regs2 Hs'.
  assert (labelled_equiv _ Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s Hs) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm regs1 regs2 Hs') as Hsecs'.
  specialize (Heutt g_asm g_asm regs1 regs2 H0) as Heutt.
  specialize (eutt_secure_eqit_secure) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Heutt.
  intros. inv PR. inv REL1. destruct x0. destruct r2. clear Hsecs' Htrans Heutt. cbn in *.
  destruct x1. constructor; auto. constructor; auto. cbn. destruct REL2. cbn in *.
  destruct H1. cbn in *. etransitivity; eauto.
Qed.

Lemma compile_preserves_ps_ni : forall (c : stmt _),
    valid_stmt c ->
    labelled_bisimilar TT (denote_stmt _ c) (denote_stmt _ c) ->
    labelled_bisimilar TT (denote_asm _ (compile c) f0) (denote_asm _ (compile c) f0 ) .
Proof.
  intros s Hs Hsecs. red. intros g_imp g_asm regs1 regs2 Hs'.
  specialize (compile_correct s Hs) as Heutt. do 2 red in Heutt.
  specialize (compile_preserves_ps_security s Hs Hsecs) as Hcomp. unfold interp_imp_inline in *.
  red in Hsecs. specialize (Hsecs g_imp g_asm regs1 regs2 Hs') as Hsecs'.
  red in Hcomp.
  assert (Renv g_asm g_asm). reflexivity.
  assert (Renv g_imp g_imp). reflexivity.
  specialize (SecureEqEuttHalt.eqit_secure_trans) as Htrans.
  assert (Hsec'' : eqit_secure (PreOrderOfLattice sensitivity_lat) (priv_exc_io sensitivity_lat)
             (product_rel (product_rel top2 Renv) TT) true true l
             (interp_asm (denote_stmt _ s) (regs1, g_imp))
             (interp_asm (denote_asm _ (compile s) f0 ) (regs2, g_asm) )
         ).
  {
    eapply SecureEqEuttHalt.eqit_secure_RR_imp with (RR1 := rcompose _ _ ).
    2 : eapply Htrans; eauto. 2 : eapply Hcomp. 2 : reflexivity.
    intros. inv PR. inv REL1. inv REL2. inv H1. inv H3. constructor; auto.
    constructor; auto. etransitivity; eauto.
  }
  eapply Htrans in Hsec''; eauto.
  2 : {
    apply eqit_secure_sym. eapply Hcomp. reflexivity.
  }
  Unshelve. 2 : apply regs1.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Hsec''.
  intros. inv PR. inv REL1. inv REL2. inv H1. inv H3. constructor; auto.
  constructor; auto. etransitivity; eauto. etransitivity; eauto. symmetry. eauto.
  reflexivity.
Qed.
  
  
End ProgressSensitive.

Section ProgressInsensitive.

Definition labelled_pi_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree ((impExcE _) +' Reg +' Memory +' (IOE _)) A ) (t2 : itree ((impExcE _) +'
 Reg +' Memory +' (IOE _)) B) :=
  forall (g_imp : map) (g_asm : memory) (regs1 regs2 : registers),
    labelled_equiv _ Γ l g_imp g_asm ->
    (*  maybe I can refactor the double product_rel to something nicer *)
    pi_eqit_secure _ (priv_exc_io sensitivity_lat) (product_rel (product_rel top2 Renv) RAB) true true l 
                (interp_asm t1 (regs1, g_imp )) (interp_asm t2 (regs2, g_asm)).

Lemma compile_preserves_pi_security : forall (c : stmt _),
    valid_stmt c ->
    labelled_pi_bisimilar TT (denote_stmt _ c) (denote_stmt _ c) ->
    labelled_pi_bisimilar TT (denote_stmt _ c) (denote_asm _ (compile c) f0 ) .
Proof.
  intros s Hs Hsecs. red in Hsecs. red. intros g_imp g_asm regs1 regs2 Hs'.
  assert (labelled_equiv _ Γ l g_imp g_imp). reflexivity.
  specialize (compile_correct s Hs) as Heutt. do 2 red in Heutt.
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecs g_imp g_asm regs1 regs2 Hs') as Hsecs'.
  specialize (Heutt g_asm g_asm regs1 regs2 H0) as Heutt.
  specialize (pi_eqit_secure_mixed_trans) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply pi_eqit_secure_RR_imp; try apply Heutt.
  intros. inv H1. inv REL1. inv H1. constructor; auto. constructor; auto.
  inv REL2. etransitivity; eauto.
Qed.


Lemma compile_preserves_pi_ni : forall (c : stmt _ ),
    valid_stmt c ->
    labelled_pi_bisimilar TT (denote_stmt _ c) (denote_stmt _ c) ->
    labelled_pi_bisimilar TT (denote_asm _ (compile c) f0) (denote_asm _ (compile c) f0 ) .
Proof.
  intros c Hc Hsecc. red. intros g_imp g_asm regs1 regs2. intros Hasmeq.
  assert (labelled_equiv _ Γ l g_imp g_imp). reflexivity.
  assert (labelled_equiv _ Γ l g_asm g_asm). reflexivity.
  specialize (compile_correct c Hc) as Heutt. do 2 red in Heutt.
  assert (Renv g_imp g_imp). reflexivity.
  assert (Renv g_asm g_asm). reflexivity.
  assert (Hmem12 : labelled_equiv _ Γ l g_imp g_asm). auto.
  apply compile_preserves_pi_security in Hc as Hsecc'; auto.
  do 2 red in Hsecc'.
  specialize (Hsecc' g_imp g_asm regs1 regs2 Hasmeq). apply pi_eqit_secure_sym in Hsecc'.
  specialize (Heutt g_imp g_imp regs1 regs1 H1) as Heutt1.
  specialize (pi_eqit_secure_mixed_trans) as Htrans.
  eapply Htrans in Heutt1; eauto. apply pi_eqit_secure_sym.
  eapply pi_eqit_secure_RR_imp; eauto. unfold flip.
  intros. inv H3. inv REL1. inv REL2. inv H3. constructor; auto.
  constructor; auto. etransitivity; eauto. etransitivity; eauto. symmetry. eauto.
  reflexivity.
Qed.


End ProgressInsensitive.

  
End SecurityPreservation.
