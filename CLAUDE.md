# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

**Default build system: make**

```bash
# Install dependencies
opam install coq-paco coq-ext-lib

# Build everything
make all -j        # library + tutorial + tests

# Build specific targets
make               # library only
make tutorial
make tests
make html          # coqdoc HTML docs → html/toc.html
```

**Alternative build system: dune**

```bash
opam install coq-paco coq-ext-lib dune

dune build         # build everything
dune runtest       # run tests
dune build theories / tutorial / tests / examples
```

**Before editing Coq files interactively with dune**, set up `_CoqProject`:
```bash
cp _CoqProject.dune _CoqProject
```
Clean before switching between `make` and `dune` builds.

## Architecture Overview

This is a Rocq (Coq) library for **Interaction Trees** — a coinductive data structure for representing recursive/impure programs with principled equational reasoning.

### Core Data Type

`itree E R` (in [theories/Core/ITreeDefinition.v](theories/Core/ITreeDefinition.v)) is a coinductive tree with three constructors:
- `Ret r` — pure return value
- `Tau t` — silent step (enables coinductive looping)
- `Vis e k` — visible event `e : E X` with continuation `k : X -> itree E R`

The type is defined as a final coalgebra using `CoInductive` with a primitive projection `_observe`. Always use `observe` (not `_observe` directly), and prefer `cbn` over `simpl` when reducing `observe` of a `CoFixpoint`.

### Equational Theory (`theories/Eq/`)

The key file is [theories/Eq/Eqit.v](theories/Eq/Eqit.v). All three main relations are instances of `eqit b1 b2 RR`:

| Relation | Notation | `b1` | `b2` | Meaning |
|----------|----------|------|------|---------|
| `eq_itree RR` | `≅` | false | false | Strong bisimulation |
| `eutt RR` | `≈` | true | true | Weak bisimulation (up to `Tau`) |
| `euttge RR` | `≳` | true | false | Weak simulation (one-sided `Tau` elim) |

**Critical architectural detail**: This branch (`yannick-coinduction`) replaces the original paco-based coinduction with **Pous' `coinduction` library** (`From Coinduction Require Import all`). The `gfp` combinator defines coinductive relations as greatest fixed points of monotone functions. The `eqit_mon` record packages the monotone function for use with `gfp`.

Notations have three "layers":
- `t1 ≈ t2` — the `gfp` (greatest fixed point)
- `t1 [≈] t2` — the `elem` (membership in the chain)
- `t1 {≈} t2` — the `eqitF` functor applied to `elem _`

### Library Organization

- **`theories/Basics/`** — Category theory infrastructure (`~>` notation, Kleisli categories, monad transformers). Not ITree-specific.
- **`theories/Core/`** — ITree definition, `bind`/`map`, Kleisli category (`KTree`), `Subevent` for extensible effects.
- **`theories/Eq/`** — `eqit`/`eutt`/`eq_itree`, up-to-taus, simulation, heterogeneous relation (`Rutt`).
- **`theories/Props/`** — Propositional predicates on ITrees (finiteness, leaves, cofiniteness).
- **`theories/Interp/`** — `interp`, `translate`, `mrec`/`rec` recursion combinators, event handlers.
- **`theories/Events/`** — Standard event types: state, reader, writer, exceptions, nondeterminism, concurrency.
- **`extra/`** — Additional theories (ITrace, Dijkstra monads, secure information flow). Mapped to `ITree.Extra`.

### Key Convention

Theorems are kept in separate `*Facts` modules (e.g., `KTreeFacts`, `InterpFacts`) to enable parallel compilation and isolate potential universe inconsistencies from the computational definitions.

### Axioms

The core library uses UIP (`eq_rect_eq`) and functional extensionality (in `FunctionFacts`). The `extra/ITrace` theories additionally assume excluded middle and a type-theoretic axiom of choice (not used in the main `theories/` library). The axiom `bisimulation_is_eq : t1 ≅ t2 -> t1 = t2` is exported but not used internally.

### Tactics (in `theories/Basics/Utils.v` and `theories/Eq/Eqit.v`)

Custom tactics include `inv`, `hexploit`, `rewrite_everywhere`, `flatten_goal`/`flatten_hyp`/`flatten_all`, and `icoinduction` (wraps the `coinduction` library's tactic for ITree-specific goals).
