From ITree Require Import
     ITree Eq.Eq Eq.UpToTaus.

(* Coq extraction seems to have problem with module synonyms.
   We just make these synonyms abstract for now. *)
Module Type Dummy.
End Dummy.

Module ITree : Dummy := ITree.
(* Module MutFix : Dummy := MutFix. *) (* TODO: uncomment this (this currently runs into an extraction bug) *)
