From Coq Require Extraction ExtrOcamlNatInt.
From Coq Require Import Arith.

From ITree Require Import ITree.

Inductive IO : Type -> Type :=
| Input  : IO nat
| Output : nat -> IO unit.

CoFixpoint echo : itree IO void :=
  Vis Input (fun x => Vis (Output x) (fun _ => echo)).

CoFixpoint spin : itree IO void := Tau spin.

CoFixpoint kill9 : itree IO unit := Vis Input (fun x => if x =? 9 then Ret tt else kill9).

(* Extract the echo example *)
Extraction "echo.ml" itreeF itree observe IO echo.
