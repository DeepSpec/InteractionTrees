(** * Main module *)

(** The main definitions to construct programs with are
    gathered here.

    Theorems can be accessed via [ITree.ITreeFacts],
    and some standard effects via [ITree.Events].
 *)

From ITree Require Export
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Core.Subevent
     Eq.UpToTaus
     Indexed.Function
     Indexed.Sum
     Interp.Interp
     Interp.Handler
     Interp.Recursion
     .
