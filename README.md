Dijkstra Monads for All
=======================

Annonymous supplementary material for ICFP submission #40

Organisation
============

* appendix.pdf contains more detail and proofs did not fit in
  the paper body.

* The FStarExamples/ folder contains examples of programs using the
  new effect definition mechanism and implementing the examples from
  the paper. They verify using our version of F* included in the
  non-anonymized supplementary material. The README in that directory
  explains where each example is found and how to test them.

* The CoqExamples/ folder contains our Coq implementation of
  specification monads, Dijkstra monads and the examples from the
  paper. You can open it directly in emacs + Proof General or in
  CoqIDE, or you can build it with `coqc dijkstra.v` or alternatively
  by running `make`.

* The Categories/ folder contains a copy of
  https://github.com/amintimany/Categories extended with definitions
  of monads (in the Categories/Monad/ subfolder).

* The SM/ folder contains a formalization of the SM metalanguage with
  definition of the denotation and logical relation. It uses the
  Categories library and the Equations plugin (= 1.2). You can build
  this (including Categories) by runing `make` in the parent folder.


Requirements for Coq development
================================

- Coq version 8.8.2 or 8.9.0
- Equations version =1.2 (https://github.com/mattam82/Coq-Equations)
