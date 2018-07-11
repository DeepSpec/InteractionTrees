# InteractionTrees
Formalization of the Interaction Tree Datatype in Coq


## Installation instructions

We recommend using [opam](http://coq.io/opam/) to install our dependencies. The one-liner for installing the dependencies is:

```sh
$ sh install-deps.sh
```

If you would like to use local versions of some of the dependencies, create a `_CoqPath` file and include the include paths for the libraries that you would like to include. For example,

```
-Q ...path/to/paco/theories... paco
```

Once you do this, you can run `make _CoqProject` and it will build a `_CoqProject` that contains your local paths and the repository-specific paths. This target is built automatically with `make` so you don't need to run it manually.

### Local Setup Instructions

- run `setup.sh` from the root directory to setup dependencies.
- run `make -C src` from the root directory to build.

** one liner **
```
git clone https://github.com/DeepSpec/InteractionTrees.git && \
      cd InteractionTrees/lib/ && ./setup.sh && cd src && make
```
