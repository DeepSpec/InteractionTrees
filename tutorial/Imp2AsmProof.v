Require Import Imp Asm Imp2Asm AsmCombinatorsCorrectness Imp2AsmCorrectness Label.

From Coq Require Import Fin.
From ITree Require Import ITree.

Section Correctness.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Context {HasExit: Exit -< E'}.
  Notation E := (Locals +' E').

Theorem compile_correct (s : stmt) :
  eq_locals TT Renv
            (denote_asm (compile s) F1)
            (denoteStmt s).
Proof.
  apply Imp2AsmCorrectness.compile_correct.
Qed.

End Correctness.
