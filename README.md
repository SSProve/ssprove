# SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq

This complementary material corresponds to the Coq formalisation of the results
mentioned in the paper.
This README serves as guide to installing this project and finding
correspondence between the claims in the paper and their formal proofs in Coq,
as well as listing the assumptions that the formalisation makes.

## Prerequisites

- Ocaml
- Coq `8.12.0`
- Equations `1.2.3`
- Mathcomp analysis `0.3.2`
- Coq Extructures `0.2.2`

To build the dependency graph, you can optionally install `graphviz`. On macOS,
`gsed` is additionally required for this.

You can get them from the `opam` package manager for `ocaml`:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.3 coq-mathcomp-analysis.0.3.2 coq-extructures.0.2.2
```

## Step-by-step compilation guide

Run `make` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings.

Run `make graph` to build a graph of dependencies between sources.

## Organisation of the directories

- theories/           : root of all the Coq files
- theories/Mon        : external development coming from "Dijkstra Monads For All"
- theories/Relational : external development coming from "The Next 700 Relational Program Logics"
- theories/Crypt      : this paper

## Mapping between paper and formalisation

## Axioms and assumptions

see theories/Crypt/Axioms.v
We use functional extensionality and proof irrelevance throughout the development. We also assume the existence of a mathcomp type of real numbers.


