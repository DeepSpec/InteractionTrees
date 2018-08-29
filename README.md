# Interaction Trees

Formalization of the Interaction Tree Datatype in Coq

## Dependencies.

- [coq-paco](https://github.com/snu-sf/paco)
- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib)

## Build instructions

### Build everything locally

Run `setup.sh` from the root directory to download dependencies (in `lib/`) and build the project.

#### One-liner from scratch

```
git clone https://github.com/DeepSpec/InteractionTrees.git && cd InteractionTrees && ./setup.sh
```

### Install dependencies with OPAM

```
opam install coq-paco coq-ext-lib
```

Now you can build the project with :

```
make
```

### Use dependencies installed elsewhere

If you would like to use local versions of some of the dependencies, create a
`_CoqPath` file with the paths to the libraries that you would like to include.
For example,

```
-Q path/to/paco/src Paco
```

Once you do this, you can run `make _CoqProject` and it will build a `_CoqProject` that contains your local paths and the repository-specific paths. This target is built automatically with `make` so you don't need to run it manually.

Now you can build the project with :

```
make
```
