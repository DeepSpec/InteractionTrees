# InteractionTrees
Formalization of the Interaction Tree Datatype in Coq

## Installation instructions

Run `setup.sh` from the root directory to setup dependencies and build the project.

If you would like to use local versions of some of the dependencies, create a `_CoqPath` file and include the include paths for the libraries that you would like to include. For example,

```
-Q ...path/to/paco Paco
```

Once you do this, you can run `make _CoqProject` and it will build a `_CoqProject` that contains your local paths and the repository-specific paths. This target is built automatically with `make` so you don't need to run it manually.


**one liner**

```
git clone https://github.com/DeepSpec/InteractionTrees.git && ./setup.sh
```
