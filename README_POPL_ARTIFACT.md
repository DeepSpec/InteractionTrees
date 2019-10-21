Interaction Trees
=================

## Download and build

The project can be found at this URL:

```
https://github.com/DeepSpec/InteractionTrees/tree/popl20
```

The artifact evaluation should take place on the `popl20` branch.

The following command downloads the repository and checkouts the right branch:

```
git clone https://github.com/DeepSpec/InteractionTrees -b popl20
```

### Build

The recommended way is to build from source.

The following dependencies are required:

- `coq.8.9.1`
- `coq-paco.4.0.0`
- `coq-ext-lib.0.10.2`

Coq `8.8` and `8.9.0` also work, but the two other libraries must be exactly
those versions.

Assuming you have Opam, this command installs the library dependencies with the
right versions:

```
opam install coq.8.9.1 coq-paco.4.0.0 coq-ext-lib.0.10.2
```

You can now build the library (takes a few minutes at most):

```
make -j
```

And the compiler example is under the target `tutorial` (also takes less than a
few minutes):

```
make -j tutorial
```

### Reproducible build with Docker

In case of critical problems with the above steps, a Docker image is provided
with all dependencies preinstalled.

Assuming you have installed Docker, and its service is running, the
following command downloads the image and runs it:

```
# Might need sudo
docker run -it lysxia/itree:popl20
```

After a few minutes, a bash shell opens inside the library, and the same
commands as above will build the library and the compiler example.

```
make -j
make -j tutorial
```

(Note: leaving the shell discards the state of the container, and you
will have to enter these commands again next time you run it.)

You can use `less` to inspect files, and for any fancier usage, you will have
to install an editor via `apt-get` (GUIs don't work in Docker though).
You'll probably prefer to look at the source downloaded through git instead.

```
sudo apt-get update
sudo apt-get install nano
sudo apt-get install vim
sudo apt-get install emacs
```

## Repository organization

This project consists of a library, `coq-itree`, under the
directory `theories/`, and a compiler for a toy imperative language Imp (from
Software Foundations), under the directory `tutorial/`.
The `examples/` subdirectory contains additional supporting examples
and experiments.

### Axioms

The whole project depends only on those two axioms about heterogeneous
equality, arising from uses of the `dependent destruction` tactic and from the
Paco library. We believe these axioms can be avoided with minor changes to the
Paco library and a more careful definition of itree equivalence/bisimulation.

The file `tutorial/PrintAssumptions.v` contains commands showing the axioms
transitively used by the two main theorems in the compiler.

```
Axioms:
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U)
                                (Q : U -> Type) (x : Q p)
                                (h : p = p), x = eq_rect p Q x p h
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
```

## The ITree library

Where to find the definitions of elements mentioned in our paper.
A file-by-file breakdown of the library can be found in the file `README.md`.

### ITrees (Section 2)

- The definition of the `itree` type and some core operations is in
  `./theories/Core/ITreeDefinition.v`. (Section 2.1 and Figure 2)

- ITree equivalences (Section 2.2 and Figure 2, strong and weak bisimulation)
  are defined in `Eq/Eq.v`, together with most of the equational theory for `itree`
  (Figure 5).

- KTrees (Section 2.3) are defined in `Core/KTree.v`. They instantiate a general
  category interface (`id_`, `cat`, `case_`, `inl_`, `inr_`...) in
  `Basics/CategoryOps.v`. Laws for categories (with sums and an iteration
  operator) are given in a separate interface `Basics/CategoryTheory.v`, and
  proved, in the case of KTrees, in `Core/KTreeFacts.v`.

### Interpreters and Event Handlers (Section 3)

- The interpreter `interp` (Section 3.2 and Figure 7) is defined in
  `Interp/Interp.v`, and its equations are proved in `Interp/InterpFacts.v`.

- `interp_state` (Section 3.1) is defined in `Events/State.v`, as a
  specialization of `interp`. This specialization relies on a `MonadIter`
  instance of the state monad transformer, which can be found in
  `Basics/Basics.v`.

- Event Handlers (Section 3.3) are also, like KTrees, an instance of the
  category interface mentioned earlier (`Basics/CategoryOps.v`).
  The disjoint union of events `+'` is defined in
  `Indexed/Sum.v`.
  The `Subevent` (`-<`) type class is defined in
  `Core/Subevent.v`, along with the overloaded `trigger`. (The non-overloaded
  one lives in `ITreeDefinition`.)

- Standard event types (Figure 2) are found under `Events/`, but
  most of the development effort on this side has gone into the state event, in
  `Event/State.v`, `Event/StateFacts.v` and `Event/StateKleisli.v`.

### Recursion (Section 4)

- `iter` (Section 4.1) and `mrec` (Section 4.2) are found in
  `Core/ITreeDefinition.v` and `Interp/Recursion.v` respectively.
  They are both instances of the type class `Iter` for categories,
  defined in `Basics/CategoryOps.v`, with the associated equations in
  `Basics/CategoryTheory.v`. `iter` lives in the category of KTrees
  (the instance is defined in `Core/KTree.v` (TODO check)) and `mrec`
  lives in the category of event handlers in `Interp/Handler.v`.
  `loop` is derived from `iter` also in a general way in
  `Basics/CategoryOps.v`.

## Case Study: Verified compilation of Imp to Asm

The formalization of the case study described in *Section 5* of our POPL'20
submission is contained in the folder `tutorial/`.
Each file is generously documented, but we lay down through this Readme the
explicit correspondence between the paper's material and their formal counterpart.
More specifically:

- `tutorial/Imp.v`: The Imp language definition.
 This file contains the definitions from *Figure 10*: it provides the syntax, denotation
 and interpretation of the Imp language.
 All explanations from *Section 5.1* refer to this file.

- `tutorial/Asm.v`: The Asm language definition.
 This file contains the definitions from *Figure 11*: it provides the syntax, denotation
 and interpretation of the Asm language.
 Note a minor renaming: `den_asm` is named `denote_asm` in the formalization.
 The explanations from *Section 5.2* refer to this file.
 The last paragraph mentions proving that `interp_asm` and `interp_imp` are monad morphisms.
 For the former, it is found at the end of this file, in the section `InterpAsmProperties`.
 For the latter, a similar section can be found at the end of the file `Imp.v`.
 *Section 5.2* mentions the use of finite types `T:fin k` to represent labels, rather than
 a `T:Type`. The paper does not expand on this technical detail, but the
 required machinery is covered in the files `tutorial/Fin.v` and
 `tutorial/KTreeFin.v`.

- `tutorial/AsmCombinators.v`: Linking of Control-Flow Graphs.
 As explained through the first half of *Section 5.3*, we define four primitive
 combinators of open `asm` programs and prove them correct in the sense that
 their denotations commute with the corresponding categorical constructors over the
 continuation trees structure.
 Both the definitions and proofs are contained in this file.

- `tutorial/Imp2Asm.v`: The compiler.
 The remaining of *Section 5.3* introduces additional derived combinators for `asm`.
 Their definitions can be found with the definition of the compiler, presented at the
 beginning of *Section 5.4*, in this short file.

- `tutorial/Imp2AsmCorrectness.v`: The compiler correctness.
 This file covers the proof of correctness of the compiler, i.e. the remaining
 material from *Section 5.3 and 5.4* not covered yet.
 In particular, the correctness of the derived combinators `seq_asm_correct` and
 `while_asm_correct`, section `Linking`) from the end of *Section 5.3* are in this file.
 It also contains the precise statement of the established bisimulation `bisimilar`.
 Finally, section `Correctness` contains the proof of correctness of the compilation
 of expression (`compile_expr_correct`) as well as the main result `compile_correct`
 expressing the correctness of the compiler.

- `tutorial/AsmOptimization.v`: Correctness of an optimization.
 The content of this file is not covered in the paper.

### Extraction

For reasons of space we cut some discussion about extraction in our submitted
version, which will be restored in the upcoming revision. The supporting example is
reproduced in the file `examples/Echo.v` containing the small loop examples
from Section 2 and an extraction of one of them (`echo`), and the file
`examples/echo_driver.ml` containing an interpreter in OCaml.
This example can be compiled with this command:

```
make echo-example
```

which is a shortcut for the following commands

```
cd examples/
coqc -Q ../theories ITree Echo.v                 # Extract echo.mli, echo.ml
ocamlc echo.mli echo.ml echo_driver.ml -o echo   # Compile the OCaml code
```

The resulting executable reads numbers from standard input
and echoes them back on standard output.

```
./examples/echo
1
2
3
```
