# Cryptographic Assumptions Explained

This directory provides formalization for some cryptographic assumptions that are used in SSProve.

## Table of Contents
1. [Discrete Logarithm Assumption](#dl-assumption)
2. [Decisional Diffie-Hellman Assumption](#dh-assumption)
3. [t-Strong Diffie Hellmann](#t-SDH-assumption)

<a id="dl-assumption"></a>
## Discrete Logarithm Assumption (DL)

### Overview

The Discrete Logarithm assumption (DL) posits that given a generator \( g \) of a cyclic group \( G \) of order \( n \) and an element \( h \) in \( G \), it is computationally infeasible to find an integer \( x \) such that \( g^x = h \). The integer \( x \) is known as the discrete logarithm of \( h \) with respect to \( g \).

It is formalized in the file `DL.v`.

### Mathematical Formulation

Given:
- A cyclic group \( G \) of order \( n \).
- A generator \( g \) of \( G \).
- An element \( h \) in \( G \).

Find:
- An integer \( x \) such that \( g^x = h \).

<a id="dh-assumption"></a>
## Decisional Diffie-Hellman Assumption (DDH)

### Overview

The Decisional Diffie-Hellman assumption posits that given a cyclic group \( G \) of order \( n \) with a generator \( g \), and given the tuple \( (g, g^a, g^b, g^c) \) for randomly chosen \( a, b \in \mathbb{Z}_n \), it is computationally infeasible to determine whether \( c \) is equal to \( a \times b \) modulo \( n \). In other words, it is hard to distinguish the tuple \( (g, g^a, g^b, g^{ab}) \) from a random tuple \( (g, g^a, g^b, g^c) \) where \( c \) is chosen uniformly at random from \( \mathbb{Z}_n \).

It is formalized in the file `DDH.v`.

### Mathematical Formulation

Given:
- A cyclic group \( G \) of order \( n \).
- A generator \( g \) of \( G \).
- Elements \( g^a \) and \( g^b \) in \( G \), where \( a \) and \( b \) are randomly chosen integers from \( \mathbb{Z}_n \).
- An element \( g^c \) in \( G \).

Determine:
- Whether \( c \equiv a \times b \pmod{n} \).

In other words, distinguish between the following two distributions:
1. \( (g, g^a, g^b, g^{ab}) \)
2. \( (g, g^a, g^b, g^c) \), where \( c \) is chosen uniformly at random from \( \mathbb{Z}_n \).

<a id="t-SDH-assumption"></a>
## t-Strong Diffie Hellmann (t-SDH)

### Overview

The t-Strong Diffie-Hellman assumption posits that given a randomly chosen \( α \in \mathbb{Z}_p^*\) 
and a \((t + 1)\)-tuple \((g, g^α, g^{α^2}, ..., g^{α^t})\in \mathbb{G}^{t+1} \), it is computationally infeasible for an adversary to find a \( c \in \mathbb{Z}_p - \{-α \}\) such that \( g^{1/(α + c)}\).

### Mathematical Formulation

Given:
-  A cyclic group \(G\).
- An element \( α \in \mathbb{Z}_p^*\).
- A \((t + 1)\)-tuple \((g, g^α, g^{α^2}, ..., g^{α^t})\in \mathbb{G}^{t+1} \).

Find:
- A \( c \in \mathbb{Z}_p - \{-α \}\) such that \( g^{1/(α + c)}\).

### References

- [Diffie, W., & Hellman, M. E. (1976). New Directions in Cryptography. IEEE Transactions on Information Theory, 22(6), 644-654.](https://doi.org/10.1109/TIT.1976.1055638)
- [McCurley, K. (1990). The Discrete Logarithm Problem. In Proceedings of the International Congress of Mathematicians (Vol. 1, pp. 667-678).](https://doi.org/10.1007/BF01180563)
- [Dan Boneh and Xavier Boyen. Short signatures without random oracles. In Christian Cachin and Jan Camenisch, editors, EUROCRYPT.](https://crypto.stanford.edu/~xb/eurocrypt04a/bbsigs.pdf)
