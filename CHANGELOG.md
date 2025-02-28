5.2.1 - February 2025
=====================

- Compatibility with Coq 8.20 and Paco 4.2.1-4.2.3

5.2.0 - April 2024
==================

- Compatibility with Coq 8.19
- Add `Hint Mode` on `MonadIter`, avoiding some infinite instance resolution loops
- Rename `ITree.Basics.Tacs` to `ITree.Basics.Utils`

5.1.2 - October 2023
====================

- Compatibility with Coq 8.18

5.1.1 - Mars 2023
=================

- Compatibility with Coq 8.16, 8.17, and paco 4.2.0
- Remove redundant `RelDec_string` instances

5.1.0 - December 2022
=====================

- In `ITree.Extra`:
    + Refactor `IForest` to reuse `ITree.Props.Leaf`.

- Add `Eq.RuttFacts`: properties of `rutt`.

- Add more lemmas about `eutt` and `Leaf`.

5.0.0 - May 2022
================

- Create `coq-itree-extra`. Under the namespace `ITree.Extra`:
    + `ITrace`: ITrees as sets of traces
    + `Dijkstra`: Dijkstra monads forever (POPL 2021)
    + `Secure`: Indistinguishability relation on ITrees
    + `IForest`: The "sets of itrees" monad

- Add `Hint Mode` on `ReSum`, preventing some infinite loops in instance resolution.

- Add `rutt`, a generalization of `eutt` relating trees with different event types,
  `rutt RE RA RS : itree E R -> itree F S -> Prop`.

- Add `Props.Divergence` and `Props.Finite`, with predicates (`may_diverge`,
  `must_diverge`, `BoxFinite`, `DiamondFinite`) about infinite and finite itrees.

- Add `Props.HasPost`, a predicate transformer semantics for itree.

- Add `Props.Leaf`, a membership relation on trees; `Leaf` can be seen as a dual to `has_post`.

- Add classes for cartesian closed categories in `Basics.CategoryTheory`.

- Add `Axioms`, collecting all axioms used by this library and associated tactics.

- Add `Events.ExceptionFacts`.

4.0.0 - March 2021
==================

- Change `ITree.bind` from a notation to a function. This may break some proofs.

    + After simplifications, if there is `ITree.subst` in the goal, use the tactic
      `ITree.fold_subst` to change it back to `ITree.bind`
    + After applying `eqit_bind`, the goals are reversed.

- Reduce dependency on axioms. Basically, we require UIP for one inversion
  lemma `ITree.Eq.Eq.eqit_inv_Vis` (and one notable corollary of it is
  `ITree.Eq.UpToTaus.eutt_conj`).

- Fixed: scopes are not opened globally anymore; add `Local Open Scope itree_scope`
  (also `cat_scope`, `monad_scope` (from ext-lib)) to use those scopes.

- Drop support for Coq 8.8 and 8.9.
  (This version technically still builds with Coq 8.9 using `make`, or Dune 2.8.4)

- Change the build system from `make` to `dune`.

- Deploy [coqdoc documentation on Github Pages](https://DeepSpec.github.io/InteractionTrees/).

- Add modules:
    + `ITree.Basics.HeterogeneousRelations`
    + `ITree.Basics.CategoryRelations` (the category of relations between types)
    + `ITree.Events.FailFacts`

- Add constructs for cartesian categories (i.e., categories with products) in
  `ITree.Basics.CategoryTheory`.

Miscellaneous changes
---------------------

- Change `eqit_Vis` from `<->` to `->`; the converse is `eqit_inv_Vis`.

- Rename theorems in `ITree.Eq.Eq` (trying to make them more consistent;
  mostly, uppercase initial of constructors, and lowercase `l`/`r`):
    + `eqitree_inv_Ret`
    + `eqitree_inv_Ret_r`
    + `eqitree_inv_Vis_r`
    + `eqitree_inv_Tau_r`
    + `eqit_inv_Ret`
    + `eqit_inv_Vis`
    + `eqit_inv_Tau`
    + `eqit_inv_Tau_l`
    + `eqit_inv_Tau_r`
    + `eqit_Tau_l`
    + `eqit_Tau_r`
    + `eutt_inv_Ret`
    + Contradiction lemmas (where the two sides in an `eqit` equation don't
      match) are refactored into `eqit_inv`.

- Add functions and theorems:
    + `ITree.Basics.liftState`
    + `ITree.Core.KTreeFacts.cat_iter`
    + `ITree.Eq.UpToTaus.eutt_conj`, `eutt_disj_l`, `eutt_disj_r`, `eutt_equiv`, `eutt_Proper_R`

- Add theorems in `ITree.Eq.Eq`:
    + `eqit_inv_Vis_weak` and `eqit_Vis_gen`,
      generalizing `eqit_inv_Vis` and `eqit_Vis`.
    + `eq_itree_inv_bind_Vis`
    + `eqit_inv_bind_Tau`
    + `eutt_inv_bind_Tau`
    + `eqitree_inv_bind_Tau`

3.2.0 - September 2020
======================

- Add module `ITree.Basics.MonadProp`: the nondeterminism monad (`_ -> Prop`)

- Rename concepts related to monad-specific equivalence:

    + `EqM` -> `Eq1`
    + `eqm` -> `eq1`
    + `EqMProps` -> `Eq1Equivalence`
    + `MonadLaws` -> `MonadLawsE` (to avoid confusion with coq-ext-lib)

- Fix the definition of `iter` to be more extractable.
  It no longer loops when the body always evaluates to a simple `Ret _`.

- Add some inversion lemmas

- Add `handle` and `handling` to convert explicitly between `Handler` and `_ ~> itree _`

- In `Simple.v`, fix the precedence level of the infix notation for `eutt` to 70.

3.1.0
=====

- Require coq-ext-lib >= 0.11.1
- Change precedence of `>>=` to level 58 (previously at level 50).
- Add `tau_eutt` and `tau_euttge` (the latter was actually renamed from
  `tau_eutt`).

3.0.0
=====

- Add compatibility with Coq 8.10 and 8.11

- Require coq-ext-lib 0.10.3 (only this one version, not 0.10.2 or 0.11.0!)
  for notation compatibility.

- Notation changes

    + Notation convention (from coq-ext-lib, PR 68): odd is right, even is left.

    + Change precedence of monad notations in `ITreeNotations`.
        + `x <- t1 ;; t2`, `t1 ;; t2`, `' p <- t1 ;; t2`, `>=>` at level 61
          (previously level 60).

    + Change precedence of notation `-<` at level 92 (previously level 90, but it
      is currently used by math-classes with right associativity).

    + Remove notations `KTree.iter` and `KTree.loop` (use `iter (C := ktree _)`
      instead for example).

- Add `pure_inl`, `pure_inr`.
- Add `eutt_interp_state` and `eutt_interp_state_eq` (the latter was actually
  renamed from `eutt_interp_state`).

2.0.0
=====

The previous release was not that stable... Too many changes to count.

Version 2.0.0 corresponds to our POPL20 paper.

1.0.0
=====

First stable release
