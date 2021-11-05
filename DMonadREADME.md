Comparison to paper notes:
	All Dijkstra Monad related library code is in the theories/Dijkstra folder

	The Hoare Logic and nat_sqrt example are in examples/ImpHoare.v

	The paper often uses names different from those used in this repo.
        We have included an index of translations of all lemmas and several
        important definitions in dmf_proof_pointers.txt

Building Notes:
	Follow the instructions in README.md to build the Interaction Trees Library
	We have tested that it builds on Coq 8.10 and Coq 8.12, we make no guarantees for any version older < 8.10

Admitted Proofs Notes:
	All Admitted lemmas in the attached code are unrelated to the project (all that I am aware of are tutorial) or commented out.

Main Toplevel results contained in DelaySpecMonad.v and TraceIT.v.. Our implementation of the Dijkstra Monad Framework implemented with Coq Typeclasses is in DijkstraMonad.v. Each file in the Dijkstra folder contains comments near the top explaining some of the main contributions of the file.
