# CheesyCrypt

## Prerequisites

- Coq `8.12.0`
- Equations `1.2.3`
- Mathcomp analysis `0.3.2`

(Note: You of course need to have ocaml installed as well. It seems
4.07.1+flambda is recommended, and then anything beyond 4.10 with flambda.)

You can get them from `opam`.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.3 coq-mathcomp-analysis.0.3.2
```

## Step-by-step Guide

Run `make` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings and coq terms.

## Organisation of the directories

- theories/           : root of all the Coq files
- theories/Mon        : external development coming from "Dijkstra Monads For All"
- theories/Relational : external development coming from "The Next 700 Relational Program Logics"
- theories/Crypt      : this paper

### Notes

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

## Axioms and assumptions (obsolete?)

Most of the development uses the recent SProp feature of Coq (instead of relying on UIP axiom).

The functional extensionality axiom from Coq's standard library is used
extensively in the development, as well as two variations of it with
respect to SProp (that can be found in `theories/sprop/SPropBase.v`, module `SPropAxioms`).
This module also defines the axiom of propositional extensionality
for strict propositions.

The use of these axioms can be checked for instance at the end of
`theories/README.v` using `Print Assumptions term.`.

No proof in the developement is admitted.
