Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String.

From ITree Require Import
     ITree
     Events.Concurrency.

Import ITreeNotations.

(* An OCaml-interpreted event that just prints the given string. *)
Variant printE : Type -> Type :=
  Print : string -> printE unit.

(* A thread that loops, printing [s] forever. *)
Definition thread {E} `{printE -< E} (s:string) : itree E unit :=
  ITree.forever (trigger (Print s)).

(* Run three threads. *)
Definition main_thread : itree (spawnE printE +' printE) unit :=
  spawn (thread "Thread 1") ;;
  spawn (thread "Thread 2") ;;
  spawn (thread "Thread 3").

Definition scheduled_thread : itree printE unit := run_spawn main_thread.
