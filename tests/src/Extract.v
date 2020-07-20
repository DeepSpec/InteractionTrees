Require ITreeTest.MetaModule.

Require Extraction.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Cd "output".
Recursive Extraction Library MetaModule.
Cd "..".
