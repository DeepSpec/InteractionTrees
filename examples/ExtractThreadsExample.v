Require ExtrOcamlBasic.
Require ExtrOcamlString.
From Examples Require Import MultiThreadedPrinting.

Extraction Language Ocaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.
(* NOTE: assumes that this file is compiled from / *)
Cd "example/extracted".

Recursive Extraction Library MultiThreadedPrinting.
