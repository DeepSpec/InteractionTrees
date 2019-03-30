From ITree Require Import
     ITree ITreeFacts Effects.

(* Coq extraction seems to have problem with module synonyms.
   We just make these synonyms abstract for now. *)
Module Type Dummy.
End Dummy.

Module ITreeInterp : Dummy := ITree.Interp.Interp.
Module ITreeRecursion : Dummy := ITree.Interp.Recursion.
Module ITreeKTree : Dummy := ITree.Core.KTree.
