Tutorial for the Interaction Trees library
==========================================

This tutorial consists of:

- [`ITree.Simple`](../theories/Simple.v):
  simplified tutorial interface, available as a part of the library itself.

- [`Introduction.v`](./Introduction.v):
  a detailed exposition of the core features.

- A case study with a small commented compiler from Imp to Asm:

    + [`Imp.v`](./Imp.v): The Imp language definition
      (a minimal imperative language from Software Foundations)
    + [`Asm.v`](./Asm.v): The Asm language definition
      (a control-flow-graph language)
    - [`AsmCombinators.v`](./AsmCombinators.v): High-level combinators for Asm
    - [`Imp2Asm.v`](./Imp2Asm.v): The compiler
    - [`Imp2AsmCorrectness.v`](./Imp2AsmCorrectness.v):
      The correctness theorem (`compile_correct`).
