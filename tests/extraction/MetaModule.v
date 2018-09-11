From ITree Require Import
     ITree Equivalence UpTo MutFix.

(* Coq extraction seems to have problem with module synonyms.
   We just make these synonyms abstract for now. *)
Module Type Dummy.
End Dummy.

Module ITree : Dummy := ITree.
Module MutFix : Dummy := MutFix.

