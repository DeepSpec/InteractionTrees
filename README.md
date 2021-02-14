# Interaction Trees [![Build Status](https://travis-ci.com/DeepSpec/InteractionTrees.svg?branch=master)](https://travis-ci.com/DeepSpec/InteractionTrees)

A Library for Representing Recursive and Impure Programs in Coq

## Installation

### Via opam

Recommended for regular users.

```
opam install coq-itree
```

### Local build

Skip to [instructions for developers](#for-developers) if you want to work on the
library.

## Top-level modules

- `ITree.ITree`: Definitions to program with interaction trees.
- `ITree.ITreeFacts`: Theorems to reason about interaction trees.
- `ITree.Events`: Some standard event types.

### Introduction

For a quick overview of the core features of the library, see
[`examples/ReadmeExample.v`](./examples/ReadmeExample.v).

See also [the tutorial](./tutorial/README.md).

## Dependencies

- [coq](https://coq.inria.fr/) (8.9-8.13)
- [coq-paco](https://github.com/snu-sf/paco)
- [coq-ext-lib](https://github.com/coq-community/coq-ext-lib)

See [`coq-itree.opam`](./coq-itree.opam) for version details.

## Axioms

This library depends on UIP for the inversion lemma:

```coq
Lemma eqit_inv_Vis
  : eutt eq (Vis e k1) (Vis e k2) ->
    forall x, eutt eq (k1 x) (k2 x).
```

There are a few more lemmas that depend on it, but you might not actually need
it. For example, the compiler proof in `tutorial` doesn't need it and is
axiom-free.

That lemma also has a weaker, but axiom-free version using heterogeneous
equality: `eqit_inv_Vis_weak`.

The library exports the following axiom for convenience, though it's unlikely
you'll need it, and the rest of the library does not depend on it:

```coq
Axiom bisimulation_is_eq : t1 ≅ t2 -> t1 = t2.
```

## Contributions welcome

Feel free to open an issue or a pull request!

---

## For developers

### Build

Install dependencies with opam.

```
opam install coq-paco coq-ext-lib
```

Now you can build the project with:

```
make
```

### Build the Documentation

#### 1. Basic Documention

You can build the `coqdoc` generated html files by doing:

```
make html
```
Then visit `html/toc.html` in your web browser.

#### 2. Prettier Documentation

For a (much) nicer presentation of the documentation, you can use
[coqdocjs](https://github.com/coq-community/coqdocjs).

1. Download
  [coqdocjs-master.zip](https://github.com/coq-community/coqdocjs/archive/master.zip)
  into the Interaction Trees root directory and unzip it.  (It should create the
  `coqdocjs-master` folder.)

2. Run
```
make COQDOCJS_DIR=coqdocjs-master html
```

Note: You can also opt to clone the coqdocjs git project rather than
download the zip file, and set the `COQDOCJS_DIR` appropriately.  (It will
probably just be `coqdocjs` not `coqdocjs-master`.)

## Library internal organization

We keep most theorems separated into `*Facts` modules, to allow
parallel compilation and to contain potential universe
inconsistencies, so the computational definitions may still be usable
for testing.

- `Basics`: General-purpose definitions not tied to interaction trees.

    + `Basics`: The `~>` notation and names of common monad transformers.
    + `Category`: A simple theory of categories, monoidal and iterative.

        * `CategoryOps`: Interfaces of operations to define categories.
        * `CategoryTheory`: Properties of categories.
        * `CategoryFacts`: General facts about categories.
	    * `CategoryFunctor`: Classes of functors.
	    * `CategorySub`: Definition of sub-categories.
        * `CategoryKleisli`: Kleisli categories (for monads in the category of functions).
        * `CategoryKleisliFacts`

    + `Function`: The category of Coq functions `A -> B`.
    + `FunctionFacts`

    + `Monad`: Properties of monads (in the category of functions).
    + `MonadState`: The state monad transformer.
    + `MonadProp`: The nondeterminism monad.

- `Core`: Main definitions for interaction trees.

    + `ITreeDefinition`: Interaction trees, type declaration and primitives.
    + `KTree`: Continuation trees `A -> itree E B`, the first Kleisli category
      of `itree`.
    + `KTreeFacts`
    + `Subevent`: Combinators for extensible effects, injecting events into
      sums.
    + `ITreeMonad`: Instantiation of the `Basics.Monad` interface with
      `itree`.

- `Eq`: Equational theory of interaction trees.

    + `Shallow`: One-step unfolding of cofixpoints.
    + `Eq`: Strong bisimulation.
    + `UpToTaus`: Weak bisimulation.
    + `SimUpToTaus`: Weak simulation.
    + `EqAxiom`: Axiom that strong bisimulation is propositional equality.
      The library exports that axiom but does not itself make use of it.

- `Indexed`: Indexed types `Type -> Type`.

    + `Sum`: Sum of indexed types.
    + `Function`: The category of parametric functions between indexed types,
      i.e., event morphisms `E ~> F`.
    + `FunctionFacts`
    + `Relation`: Relations on indexed types, i.e.,
      `forall T, E T -> E T -> Prop`.

- `Interp`: Interaction tree transformations.

    + `Interp`: Interpret itrees (`translate`, `interp`).
    + `TranslateFacts`, `InterpFacts`
    + `Handlers`: Event handlers `E ~> itree F`, the second Kleisli category
      of `itree`.
    + `HandlerFacts`
    + `Recursion`: Recursion combinators (`mrec`, `rec`).
    + `RecursionFacts`
    + `Traces`: Interpretation of itrees as sets of traces.

- `Events`: Common event types (see [`theories/Events.v`](./theories/Events.v) for a summary).
