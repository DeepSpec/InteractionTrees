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
     Secure.SecurityImp
     Secure.SecurityImpHandler
     Secure.SecurityAsm
     Secure.Utils_tutorial
     Secure.SecurityAsmCombinators
     Secure.SecurityImp2Asm
     Secure.Fin
     Secure.KTreeFin
     Secure.SecurityAsmHandler
     Secure.SecurityImp2AsmCorrectness
     Secure.SecureEqEuttTrans
.

Import ITreeNotations.

Import Monads.
Open Scope monad_scope.


Section SecurityPreservation.

Context (priv : var -> sensitivity).

Definition low_state_equiv : map -> (registers * memory) -> Prop :=
  fun s '(r, m) => low_map_equiv priv s m.

Definition low_bisimilar {A B : Type} (RAB : A -> B -> Prop) 
           (t1 : itree (stateE +' IOE) A ) (t2 : itree (Reg +' Memory +' IOE) B) :=
  forall (g_imp : map) (g_asm : memory) (l : registers),
    low_map_equiv priv g_imp g_asm ->
    eqit_secure sense_preorder priv_io (product_rel low_state_equiv RAB) true true Public (interp_imp t1 g_imp ) (interp_asm t2 (l, g_asm)).

Lemma compile_preserves_security : forall (p : stmt),
    low_eqit_secure_impstate true true priv eq (interp_imp (denote_stmt p)) (interp_imp (denote_stmt p)) ->
    low_bisimilar TT (denote_stmt p) (denote_asm (compile p) f0 ) .
Proof.
  intros p Hsecp. red in Hsecp. red. intros g_imp g_asm l Hs.
  assert (low_map_equiv priv g_imp g_imp).
  { red. intros; auto. }
  (* there exists some g_imp' *)
  specialize (compile_correct p) as Heutt. do 2 red in Heutt.
  (* exists g_imp', Renv g_imp' g_asm /\ low_map_equiv g_imp g_imp' 
     I guess g_asm fits that category?
   *)
  assert (Renv g_asm g_asm). reflexivity.
  specialize (Hsecp g_imp g_asm Hs).
  specialize (Heutt g_asm g_asm l H0) .
  specialize (eutt_secure_eqit_secure) as Htrans.
  eapply Htrans in Heutt; eauto.
  eapply SecureEqEuttHalt.eqit_secure_RR_imp; try apply Heutt.
  (* show that low_map_equiv ∘ Renv <= low_map_equiv *)
  clear -priv.
  intros [g_imp ?] [ [l g_asm] ?] Hcomp.
  split.
  2 : { red. auto. }
  cbn. inv Hcomp. red in REL1. cbn in *.
  destruct r2 as [g_imp' ? ]. destruct REL1 as [REL1 _ ].
  cbn in *. red in REL2. cbn in *. destruct REL2 as [REL2 _ ].
  red. intros. red in REL1. red in REL2. rewrite <- REL2.
  apply REL1; auto.
Qed.
  
End SecurityPreservation.
