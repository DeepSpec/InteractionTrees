From Coq Require ExtrOcamlBasic ExtrOcamlString.

From ITreeExamples Require Import MultiThreadedPrinting.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.

Extraction "MultiThreadedPrinting.ml" scheduled_thread.
