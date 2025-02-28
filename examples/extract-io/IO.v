From Coq Require Import Arith.
From ITree Require Import ITree.
Import ITreeNotations.

Inductive IO : Type -> Type :=
| Read : IO nat
| Write : nat -> IO unit.

Definition read : itree IO nat := embed Read.
Definition write : nat -> itree IO unit := embed Write.

Definition example : itree IO unit :=
  n <- read;;
  write n.

Definition SOME_NUMBER := 13.

Definition test_interp : itree IO unit -> bool := fun t =>
  match observe t with
  | VisF e k =>
    match e in IO X return (X -> _) -> _ with
    | Read => fun id =>
      match observe (k (id SOME_NUMBER)) with
      | VisF (Write n) _ => n =? SOME_NUMBER
      | _ => false
      end
    | _ => fun _ => false
    end (fun x => x)
  | _ => false
  end.

Example test : test_interp example = true := eq_refl.

Require Extraction.

Parameter exit_success : unit.
Parameter exit_failure : unit.
Extract Inlined Constant exit_success =>
  "print_endline ""OK!""; exit 0".
Extract Inlined Constant exit_failure =>
  "print_endline ""IO test failed!""; exit 1".

Definition test_io :=
  if test_interp example then
    exit_success
  else
    exit_failure.

Set Warnings "-extraction-default-directory".
Extraction "io.ml" test_io.
