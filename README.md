# Interaction Trees

A Library for Representing Recursive and Impure Programs in Coq

**NOTE: This library is currently in a pre-alpha stage, the interfaces currently exposed by the repository are undergoing a great deal of exploration and there will likely be substantial changes in the future. Backwards compatibility will not be a priority as this library evolves, so dependencies should be wary of this.**

## Dependencies

- [coq-paco](https://github.com/snu-sf/paco) (2.0.3 or later)
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

## Building the Documentation

### 1. Basic Documention

You can build the `coqdoc` generated html files by doing:

```
make html
```
Then visit `html/toc.html` in your web browser.

### 2. Prettier Documentation

For a much nicer presentation of the documentation, you can use
[coqdocjs](https://github.com/tebbi/coqdocjs).

1. Download
  [coqdoc-master.zip](https://github.com/tebbi/coqdocjs/archive/master.zip) into
  the Interaction Trees root directory and unzip it.  (It should create the
  `coqdocjs-master` folder.)

2. Run
```
make COQDOCJS_DIR=coqdocjs-master html
```

Note: If you opt to clone the `coqdocjs` git project rather than download the zip
file, set the `COQDOCJS_DIR` appropriately.  (It will probably just be
`coqdocjs` not `coqdocjs-master`.
