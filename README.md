# The next 700 relational program logics

# Prerequisites

The development for this paper is based on the coq development accompanying
the paper **[Dijkstra Monads for All](https://arxiv.org/abs/1903.01237)**,
publicly available at https://gitlab.inria.fr/kmaillar/dijkstra-monads-for-all

The prerequisite are inherited from that developement, namely:
- It requires the `master` branch of Coq available from:
  https://github.com/coq/coq/commits/master
  (in particular the following commit is known to work: d501690a7d767d4a542867c5b6a65a722fa8c4c1)
- It also requires the equations plugin, `master` branch (only for the
  General recursion examples at the end of DijkstraMonadExamples.v;
  comment out if not needed): https://github.com/mattam82/Coq-Equations
  (in particular the following commit is known to work: 710f039ced8b6c016dd5954dad241888189e0d48)
- For examples based on probabilities, it requires the math-comp-analysis
  library (version 0.2.2) that can be obtained through opam.
 

# Step-by-step Guide

Run `make` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings and coq terms.

# Organisation of the directories

- theories/           : root of all the Coq files
- theories/Mon        : external development coming from "Dijkstra monads for all"
- theories/Relational : development for this paper

# Content of the files

## In theories/Relational:
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


# Axioms and assumptions

Most of the development uses the recent SProp feature of Coq (instead of relying on UIP axiom).

The functional extensionality axiom from Coq's standard library is used
extensively in the development, as well as two variations of it with 
respect to SProp (that can be found in `theories/sprop/SPropBase.v`, module `SPropAxioms`). 
This module also defines the axiom of propositional extensionality 
for strict propositions.

The use of these axioms can be checked for instance at the end of 
`theories/README.v` using `Print Assumptions term.`.

No proof in the developement is admitted.
