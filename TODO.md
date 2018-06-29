# Software engineering issues

- common infrastructure for Vellvm and DeepWeb
    - move stuff from DW and Vellvm repos
- should we use Paco?
- which monad library (if any!)

# Research issues / topics

- trace inclusion / bisimulation (is there actually any role for
  bisimulation?)
- careful comparison with an alternative "set of traces" presentation
- should we do up-to tau equivalence?  or something more general?
- generalizing the Event combinators
- using ITrees to support both verification and testing
- what about Fork?  (or internal nondeterminism / branching time?)

# Contributions

- Proofs
- Haskell libraries don't need Tau (so the technicalities are easier)
- Extraction

# Reading / related work

- Peter Hancock might have had a similar library or theory?  (ask Conor)
- van Laarhoven Free Monad (Mauro Jaskelioff, Russell O'Connor)
    http://r6.ca/blog/20140210T181244Z.html
- Freer Monads
  http://okmij.org/ftp/Computation/free-monad.html
  http://okmij.org/ftp/Haskell/extensible/
- Operational Monads
  https://apfelmus.nfshost.com/articles/operational-monad.html
- see the paper references in the README to freer-simple!  (There are a few)
- Haskell stuff
    - e.g., freer-simple (and a few other libraries with the same interface)
    - BUT they don't have to have Tau (so the technicalities are easier)

- Other work on free monads in Coq: coq-io, FreeSpec

- For Paco: Gil's POPL 2013 paper
