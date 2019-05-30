(** * Main module with theorems *)

From ITree Require Export
     Basics.Basics
     Basics.Category
     Basics.FunctionFacts
     Core.ITreeDefinition
     Core.KTreeBasicFacts
     Core.KTreeFacts
     Indexed.FunctionFacts
     Interp.TranslateFacts
     Interp.InterpFacts
     Interp.HandlerFacts
     Interp.RecursionFacts
     .

Require Export ITree.Eq.
(* Coq sometimes thinks [From ITree Require Export Eq.] means
   [Require Export ITree.Eq.Eq.] *)
