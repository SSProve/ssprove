Dijkstra Monads for All
=======================

Coq development for the paper:
- Kenji Maillard, Danel Ahman, Robert Atkey, Guido Martinez,
  Cătălin Hriţcu, Exequiel Rivas, and Éric Tanter.
  **[Dijkstra Monads for All](https://arxiv.org/abs/1903.01237)**.
  arXiv:1903.01237. March, 2019.

Prerequisites
=============

- Coq version 8.8.2 or 8.9.0
- Equations version =1.2 (https://github.com/mattam82/Coq-Equations)

Building
========

Simply run `make` in the top folder.

Organisation
============

* The `CoqExamples/dijkstra.v` file contains our Coq implementation
  of specification monads, Dijkstra monads and the examples from the paper.

* The `Categories/` folder contains a copy of
  https://github.com/amintimany/Categories extended with definitions
  of monads (in the `Categories/Monad/` subfolder).

* The `SM/` folder contains a formalization of the SM metalanguage
  with definition of the denotation and logical relation. It uses the
  Categories library and the Equations plugin (version =1.2).

F* development
==============

There is also an F* development for this paper at:
https://github.com/FStarLang/FStar/tree/guido_effects/examples/dm4all
