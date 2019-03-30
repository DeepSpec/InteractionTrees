Require ExtrOcamlBasic.
Require ExtrOcamlString.
From Examples Require Import MultiThreadedPrinting.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.
(* NOTE: assumes that this file is compiled from examples/ *)
Cd "extracted".

Recursive Extraction Library MultiThreadedPrinting.

(* This is needed for the makefile to succeed for some reason. *)
Cd "..".
