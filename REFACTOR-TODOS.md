- unify how we deal with each node of a tree. 

- rets: a constructor pattern that either concludes or leads to computation.
- taus: coinductive conclusion. 
- single tau: simple inductive conclusion. 
- vis: this is the tricky one, and the strongest reason for a unified front. 
there is some inv_Vis, some dependent destruction, some vis_gen... we need a 
single pipeline for concluding proofs about vis nodes. 
    - the 'refine match' pattern that appears here is not lovely either. 
      See Finite.v. 
- [ ] Generally clean up Eqit.v. 
  - [ ] rename and redo sections
  - [ ] keep building tests until rewriting robustness is clear
    - [ ] organize file
    - [ ] remove add parametric morphism
- [ ] rest of rtodos 

- [ ] Get "MWE ITree library" for RIP volume
      - want highlights of itrees 
NEXT: 
- [ ] Gather and organize knowledge for talk and RIP presentation about 
      how one would teach the essentials of itrees. 
- [ ] 