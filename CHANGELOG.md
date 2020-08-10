3.2.0
=====

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
