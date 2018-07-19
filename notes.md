# Interaction Trees

## Penn Versions

*  Internal to the DeepWeb development, mostly created by Li-yao.
   - https://github.com/DeepSpec/DeepWeb/blob/master/src/Free/Monad/Free.v 
   - does not use paco
   - supports typeclassses for "event combinators"
   - intended to be compatible with coq-ext-lib?

*  The Vellvm variants
   - https://github.com/vellvm/vellvm/blob/master/src/coq/Trace.v
   - some branches have ported it to use Paco
   - instantiates the monad typeclasses adapted from Iris.  See
     https://github.com/vellvm/vellvm/blob/master/src/coq/Classes.v

*  Newly created repo, intended to unify the two above:
   https://github.com/DeepSpec/InteractionTrees


## Gregory Malecha's variant
   - https://github.com/gmalecha/coq-interaction-trees
   - uses paco
   - more generic?


## MIT Version
   - created by Adam Chlipala and 
   - ?


## Yale Version
   - Vilhelm knows something about it...


## Related reading

Freer Monads, More Extensible Effects
Oleg Kiselyov and Hiromi Ishii
http://okmij.org/ftp/Haskell/extensible/more.pdf

Turing-Completeness Totally Free
Conor McBride
https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf

Interactive Programs in Dependent Type Theory
Peter Hancock and Anton Setzer
http://www.cs.swan.ac.uk/~csetzer/articles/ioconf.pdf

