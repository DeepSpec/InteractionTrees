# Interaction Trees [![Build Status](https://travis-ci.com/DeepSpec/InteractionTrees.svg?branch=master)](https://travis-ci.com/DeepSpec/InteractionTrees)

A Library for Representing Recursive and Impure Programs in Coq

** WARNING: This library is currently in a pre-alpha stage; the
  interfaces currently exposed by the repository are undergoing a
  great deal of exploration and there will likely be substantial
  changes in the future. Backwards compatibility will not be a
  priority as this library evolves, so dependencies should be wary of
  this. **

## Organization

We keep most theorems separated into `*Facts` modules, to allow
parallel compilation and to contain potential universe
inconsistencies, so the computational definitions may still be usable
for testing.

### Top-level modules

- `ITree.Simple`: Simplified tutorial interface.
  See also `tutorial/Introduction.v`.
- `ITree.ITree`: Definitions to program with interaction trees.
- `ITree.ITreeFacts`: Theorems to reason about interaction trees.
- `ITree.Effects`: Some standard effects.

### Library organization

- `Basics`: General-purpose definitions not tied to interaction trees.

    + `Basics`: The `~>` notation and names of common monad transformers.
    + `Category`: A simple theory of ((traced) (symmetric) monoidal) categories.

        * `CategoryOps`: Interfaces of operations to define categories.
        * `CategoryTheory`: Properties of categories.
        * `CategoryFacts`: General facts about categories.

    + `Function`: The category of Coq functions `A -> B` (symmetric monoidal).
    + `FunctionFacts`

- `Core`: Main definitions for interaction trees.

    + `ITreeDefinition`: Interaction trees, type declaration and primitives.
    + `KTree`: Continuation trees `A -> itree E B`, the first Kleisli category
      of `itree` (traced symmetric monoidal).
    + `KTreeFacts`, `KTreeBasicFacts`

- `Eq`: Equational theory of interaction trees.

    + `Shallow`: One-step unfolding of cofixpoints.
    + `Eq`: Strong bisimulation.
    + `UpToTaus`, `UpToTausCore`, `UpToTausEquivalence`: Weak bisimulation.
    + `SimUpToTaus`: Weak simulation.
    + `EqAxiom`: Axiom that strong bisimulation is propositional equality.

- `Indexed`: Indexed types `Type -> Type`.

    + `Sum`: Sum of indexed types.
    + `Function`: The category of parametric functions between indexed types,
      i.e., effect morphisms `E ~> F` (symmetric monoidal).
    + `FunctionFacts`
    + `OpenSum`: Combinators for extensible effects, injecting effects into
      sums. (Experimental)

- `Interp`: Interaction tree transformations.

    + `Interp`: Interpret itrees (`translate`, `interp`)
    + `TranslateFacts`, `InterpFacts`
    + `Handlers`: Effect handlers `E ~> itree F`, the second Kleisli category
      of `itree` (traced symmetric monoidal).
    + `HandlerFacts`
    + `Recursion`: Recursion combinators (`mrec`, `rec`)
    + `RecursionFacts`
    + `Traces`: Interpretation of itrees as sets of traces.

- `Effects`: Common effects (see `theories/Effects.v` for a summary).

## Dependencies

- [coq](https://coq.inria.fr/) (8.8 or 8.9)
- [coq-paco](https://github.com/snu-sf/paco)
- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib)

See `coq-itree.opam` for version details.

## Build instructions

Install dependencies with opam.

```
opam install coq-paco coq-ext-lib
```

Now you can build the project with:

```
make
```

## Building the Documentation

### 1. Basic Documention

You can build the `coqdoc` generated html files by doing:

```
make html
```
Then visit `html/toc.html` in your web browser.

### 2. Prettier Documentation

For a (much) nicer presentation of the documentation, you can use
[coqdocjs](https://github.com/tebbi/coqdocjs).

1. Download
  [coqdoc-master.zip](https://github.com/tebbi/coqdocjs/archive/master.zip) into
  the Interaction Trees root directory and unzip it.  (It should create the
  `coqdocjs-master` folder.)

2. Run
```
make COQDOCJS_DIR=coqdocjs-master html
```

Note: If you opt to clone the `coqdocjs` git project rather than
download the zip file, set the `COQDOCJS_DIR` appropriately.  (It will
probably just be `coqdocjs` not `coqdocjs-master`.)
