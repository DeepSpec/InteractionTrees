# Interaction Trees [![Build Status](https://travis-ci.com/DeepSpec/InteractionTrees.svg?branch=master)](https://travis-ci.com/DeepSpec/InteractionTrees)

A Library for Representing Recursive and Impure Programs in Coq

## Introduction

For a quick overview of the core features of the library, see
[`examples/ReadmeExample.v`](./examples/ReadmeExample.v).

See also [the tutorial](./tutorial/README.md).

[The coqdoc documentation for this library is available here.](https://deepspec.github.io/InteractionTrees/master/toc.html)

### Top-level modules

- `ITree.ITree`: Definitions to program with interaction trees.
- `ITree.ITreeFacts`: Theorems to reason about interaction trees.
- `ITree.Events`: Some standard event types.

## Installation

### Via opam

```
opam install coq-itree
```

### Dependencies

- [coq](https://coq.inria.fr/) (8.10 - 8.13)
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

See also [`DEV.md`](./DEV.md) for working on this library.
