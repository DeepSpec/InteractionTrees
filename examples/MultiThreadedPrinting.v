Set Implicit Arguments.
Set Contextual Implicit.


From Coq Require Import
     String List.
Import ListNotations.

From ExtLib.Structures Require Import
     Monoid.

From ITree Require Import
     ITree
     Effect.Spawn.

Variant printE : Type -> Type :=
  Print : string -> printE unit.

Definition thread (s:string) : itree printE unit :=
  ITree.forever (lift (Print s)).

Definition main_thread : itree (spawnE printE +' printE) unit :=
  spawn (thread "Thread 1") ;;
  spawn (thread "Thread 2") ;;
  spawn (thread "Thread 3").

Definition scheduled_thread : itree printE unit := run_spawn main_thread.
