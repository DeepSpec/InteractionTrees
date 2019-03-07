# Interaction Trees

A Library for Representing Recursive and Impure Programs in Coq

**NOTE: This library is currently in a pre-alpha stage, the interfaces currently exposed by the repository are undergoing a great deal of exploration and there will likely be substantial changes in the future. Backwards compatibility will not be a priority as this library evolves, so dependencies should be wary of this.**

## Organization

Modules under `Core`, `Indexed`, and `Interp` keep theorems separated into
`*Facts` modules, to allow parallel compilation, and to contain potential
universe inconsistencies, so the computational content may still be
usable for testing.

- `Basics`: General-purpose definitions not tied to interaction trees.

    + `Basics`: The `~>` notation and names of common monad transformers.
    + `Category`: A simple theory of ((traced) (symmetric) monoidal) categories.

        * `CategoryOps`: Interfaces of operations to define categories.
        * `CategoryTheory`: Properties of categories.
        * `CategoryFacts`: General facts about categories.

    + `Function`: The category of Coq functions `A -> B` (symmetric monoidal).
    + `FunctionFacts`

- `Core`: Main definitions for interaction trees.

    + `ITree`: Interaction trees, type declaration and primitives.
    + `KTree`: Continuation trees `A -> itree E B`, the first Kleisli category
      of `itree` (traced symmetric monoidal).
    + `KTreeFacts`

- `Eq`: Equational theory of interaction trees.

    + `Shallow`: One-step unfolding of cofixpoints.
    + `Eq`: Strong bisimulation.
    + `UpToTaus`: Weak bisimulation.
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

    + `Interp`: `translate`, `interp`, `mrec`.
    + `InterpFacts`
    + `Handlers`: Effect handlers `E ~> itree F`, the second Kleisli category
      of `itree` (traced symmetric monoidal).
    + `HandlerFacts`
    + `Traces`: Interpretation of itrees as sets of traces.

- `Effects`:

    + `State`
    + `Nondet`
    + `Reader`
    + `Writer`
    + ???

## Dependencies

- [coq-paco](https://github.com/snu-sf/paco) (2.0.2 or later)
- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib) (0.10.0 or later)

## Build instructions

Choose one of the following methods.

### 1. Install dependencies with OPAM

```
opam install coq-paco coq-ext-lib
```

Now you can build the project with:

```
make
```

### 2. Use dependencies installed elsewhere

If you would like to use local versions of some of the dependencies, create a
`_CoqPath` file with the paths to the libraries that you would like to include.
For example,

```
-Q path/to/paco/src Paco
```

Now you can build the project with:

```
make
```
