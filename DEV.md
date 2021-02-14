# Notes for developers

## Build

Install dependencies with opam.

```
opam install coq-paco coq-ext-lib
```

Then build the project with:

```
make -j all  # Build the library, tutorial (example compiler), and tests.

# Other targets
make  # Build the library
make tutorial
make tests
```

### Build the Documentation

#### 1. Basic Documention

Build the `coqdoc` generated html files by doing:

```
make html
```

Then visit `html/toc.html` in your web browser.

#### 2. Prettier Documentation

[coqdocjs](https://github.com/coq-community/coqdocjs) adds some modern-looking
CSS and JS to coqdoc's output.

1. Download and unzip
  [coqdocjs-master.zip](https://github.com/coq-community/coqdocjs/archive/master.zip).

2. Create a link to the unzipped directory (or move the directory into this repo):

    ```
    ln -s path/to/coqdocjs-master coqdocjs
    ```

2. Run

    ```
    make html
    ```

#### 3. Updating Github pages

The documentation is stored in the `gh-pages` branch.
The recommended setup is to create a fresh clone in the `doc` directory.

```
git clone -b gh-pages git@github.com:DeepSpec/InteractionTrees doc
```

There is a script in that branch to update the documentation.

```
cd doc
sh ./update.sh
git add -u
git commit -m "Update"
```

It will run "make html" in the parent directory and move the output where it
should go, in `doc/docs/master`.
Past releases are maintained in `doc/docs/$VERSION`.

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
