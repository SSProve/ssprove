# SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq

This complementary material corresponds to the Coq formalisation of the results
mentioned in the paper.
This README serves as guide to installing this project and finding
correspondence between the claims in the paper and their formal proofs in Coq,
as well as listing the assumptions that the formalisation makes.

## Prerequisites

- Coq `8.12.0`
- Equations `1.2.3`
- Mathcomp analysis `0.3.2`
- Coq Extructures `0.2.2`

- (optionnal: graphviz, and gsed on macOS)

(Note: You of course need to have ocaml installed as well.)

You can get them from `opam`.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.3 coq-mathcomp-analysis.0.3.2 coq-extructures.0.2.2
```

## Step-by-step Guide

Run `make` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings and coq terms.

Run `make graph` to build a graph of dependencies between sources. graphviz must be installed. (On macOS, `gsed` is also required, they can both be
installed with homebrew.)

## Organisation of the directories

- theories/           : root of all the Coq files
- theories/Mon        : external development coming from "Dijkstra Monads For All"
- theories/Relational : external development coming from "The Next 700 Relational Program Logics"
- theories/Crypt      : this paper

### Notes (TODO: remove/move this)

- Category.v: Basic category theory (categories, functors,...)

- RelativeMonads.v: Categorical definitions of relative monads and a few constructions on these

- RelativeMonadExamples.v: Concrete instances of categories and relative
  monads to obtain the simple relational specification monads and
  the full relational specification monads

- Rel.v: Main definitions for the relational dependent type theory

- GenericRulesSimple.v: pure and monadic relational rules in the simpler setting

- Commutativity.v: Commuting elements of a monad and definition of relational
  effect observation out of unary effect observation

- RelationalState.v: specialization to stateful computations with examples
  of non interference

- RelationalIO.v: simple relational program logic for IO

- RelationalFinProb.v: relational program logic for (independent) finite probabilities

- RelationalExcSimple.v: specialization to computations raising exceptions

- GenericRulesComplex.v: pure and monadic relational rules in the full setting

## Axioms and assumptions

see theories/Crypt/Axioms.v
We use functional extensionality and proof irrelevance throughout the development. We also assume the existence of a mathcomp type of real numbers.


