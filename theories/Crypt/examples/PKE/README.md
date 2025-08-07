# Public-key encryption
This directory contains a case-study that proves properties in public-key cryptography.
In the case study we consider correctness and CPA-security.

The files should be read in the following order:
1. `Scheme.v` defines public-key cryptography, its correctness, and CPA-security. (15.1 JoC)
2. `LDDH.v` defines the two-stage decicional Diffie-Hellman assumption.
3. `ElGamal.v` defines the ElGamal public-key encryption scheme and proves corresness and CPA-security. (15.3 JoC)

The file `CyclicGroup.v` has various background theorems about cyclic groups.
