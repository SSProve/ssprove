# SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq

This complementary material corresponds to the Coq formalisation of the results
mentioned in the paper.
This README serves as guide to installing this project and finding
correspondence between the claims in the paper and their formal proofs in Coq,
as well as listing the assumptions that the formalisation makes.

## Prerequisites

- Ocaml
- Coq `8.12.0`
- Equations `1.2.3+8.12`
- Mathcomp analysis `0.3.2`
- Coq Extructures `0.2.2`

To build the dependency graph, you can optionally install `graphviz`. On macOS,
`gsed` is additionally required for this.

You can get them from the `opam` package manager for `ocaml`:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.12.0 coq-equations.1.2.3+8.12 coq-mathcomp-analysis.0.3.2 coq-extructures.0.2.2
```

## Step-by-step compilation guide

Run `make` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings.

Run `make graph` to build a graph of dependencies between sources.

## Organisation of the directories

| Directory             | Description                                          |
|-----------------------|------------------------------------------------------|
| `theories/`           | Root of all the Coq files                            |
| `theories/Mon`        | External development coming from "Dijkstra Monads For All" |
| `theories/Relational` | External development coming from "The Next 700 Relational Program |Logics"
| `theories/Crypt`      | This paper                                           |

## Mapping between paper and formalisation

### Package definition and laws

The formalisation of packages can be found in the directory
`theories/Crypt/package`.

The definition of packages can be found in `pkg_core_definition.v`. Note that
the definition is slightly different from the paper, but the differences are
only in naming. `raw_code` is referred to as `raw_program` and similarly
`code` is called `program`. The final version of `SSProve` will account for
this renaming.
Herein, `package I E` is the type of packages with import interface `I` and export
interface `E`.

Package laws, as introduced in the paper, are all stated and proven in
`pkg_composition.v`:


#### Sequential composition

In Coq, we call `link p1 p2` the sequential composition of `p1` and `p2`:
`p1 ∘ p2`.

```coq
Definition link {I M E} (p1 : package M E) (p2 : package I M) : package I E.
```

Associativity is state as follows:

```coq
Lemma link_assoc :
  ∀ {E M1 M2 I}
    (p1 : package M1 E) (p2 : package M2 M1) (p3 : package I M2),
    link p1 (link p2 p3) = link (link p1 p2) p3.
```

#### Parallel composition

In Coq, we write `par p1 p2` for the parallel composition of `p1` and `p2`:
`p1 || p2`.

```coq
Definition par {I1 I2 E1 E2} (p1 : package I1 E1) (p2 : package I2 E2)
  (h : parable E1 E2) : package (I1 :|: I2) (E1 :|: E2).
```
The `parable` condition checks that the export interfaces are indeed disjoint.

We have commutativity as follows:
```coq
Lemma par_commut :
  ∀ {I1 I2 E1 E2} (p1 : package I1 E1) (p2 : package I2 E2) (h : parable E1 E2),
    par p1 p2 h =
    package_transport (fsetUC I2 I1) (fsetUC E2 E1) (par p2 p1 (parable_sym h)).
```
While heavy this lemma can be read as `p1 || p2 = p2 || p1`, unfortunately,
these two packages do not have strictly equal interfaces (`E1 :|: E2` versus
`E2 :|: E1`, where `:|:` represents union of sets) and thus `package_transport`
allows us to use the fact the interfaces can be proven equal to satisfy the
type checker.

The very same problem is even more apparent in the associativity lemma,
stated as follows:
```coq
Lemma par_assoc :
  ∀ {I1 I2 I3 E1 E2 E3}
    (p1 : package I1 E1) (p2 : package I2 E2) (p3 : package I3 E3)
    (h12 : parable E1 E2) (h23 : parable E2 E3) (h13 : parable E1 E3),
    package_transport (fsetUA I1 I2 I3) (fsetUA E1 E2 E3)
                      (par p1 (par p2 p3 h23) (parable_union h12 h13)) =
    par (par p1 p2 h12) p3 (parable_sym (parable_union (parable_sym h13) (parable_sym h23))).
```
It can be read as `p1 || (p2 || p3) = (p1 || p2) || p3`).

#### Identity package

The identity package is called `ID` in Coq and has the following type:
```coq
Definition ID (I : Interface) (h : flat I) : package I I.
```
Note the extra `flat I` condition on the interface which essentially forbids
overloading: there cannot be two procedures in `I` that share the same name.
While our interfaces could in theory allow such procedures in general, the
way we build packages forbid us from ever implementing them, hence the
restriction.

The two identity laws are as follows:
```coq
Lemma link_id :
  ∀ I E (p : package I E) h,
    link p (ID I h) = ptrim p.
```

```coq
Lemma id_link :
  ∀ I E (p : package I E) h,
    link (ID E h) p = ptrim p.
```

Once again, we differ from the paper by the usage of `ptrim`. This operations
*trims* a package to match its export interface. Indeed, we allow a package
to define more than it actually exports and these *extra* procedures are
thrown away at linking.
On packages that are *fit*, i.e. that do not implement more than they export,
the equality becomes again `ID E ∘ p = p = p ∘ ID I`.

#### Interchange between sequential and parallel composition

Finally we prove a law involving sequential and parallel composition
stating how we can interchange them:
```coq
Lemma interchange :
  ∀ A B C D E F c1 c2
    (p1 : package B A)
    (p2 : package E D)
    (p3 : package C B)
    (p4 : package F E),
    par (link p1 p3) (link p2 p4) c1 =
    link (par p1 p2 c1) (par p3 p4 c2).
```
which can be read as
`(p1 ∘ p3) || (p2 ∘ p4) = (p1 || p2) ∘ (p3 || p4)`.

### Examples

The PRF example is developed in `theories/Crypt/examples/PRF.v`.
The security theorem is the following:

```coq
Theorem security_based_on_prf (Hprf : PRF_security) :
  ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords × chWords ]
    (Hdisjoint_extra : fdisjoint A.π1 EVAL_location_ff) Hdisjoint1 Hdisjoint2,
    @Advantage _ IND_CPA A Hdisjoint1 Hdisjoint2 <=
    prf_epsilon (link A (MOD_CPA_ff_pkg)) + @statistical_gap A +
    prf_epsilon (link A (MOD_CPA_tt_pkg)).
```

As we claim in the paper, it bounds the advantage of any adversary to the
game pair `IND_CPA` by the sum of the statistical gap and the advantages against
`MOD_CPA`.

Note that we require here some disjointness of state hypotheses as these are
not enforced by our package definitions and laws.


The ElGamal example is developed in `theories/Crypt/examples/Elgamal.v`
The security theorem is the following:

```coq
Theorem ElGamal_OT (dh_secure : DH_security) : OT_rnd_cipher.
```

`OT_rnd_cipher` is defined in `theories/Crypt/examples/AsymScheme.v`:

 ```coq
Definition OT_rnd_cipher :=
  ∀ A H1 H2, @Advantage _ ots_real_vs_rnd A H1 H2 = 0.
```

Note that the theorem relies on `dh_secure` which corresponds to the DDH
assumption:

```coq
Definition DH_security :=
  ∀ A Hdisj1 Hdisj2,
    @AdvantageE _ DH_real DH_rnd A  Hdisj1 Hdisj2 = 0.
```


### Probabilistic relational program logic

TODO: I guess Lemma 1, 2 and Theorem 1 can go here besides Theorem 2.

Figure 13 presents a selection of rules for our probabilistic relational
program logic. Most of them can be found in
`theories/Crypt/package/pkg_rhl.v` which provides an interface for use of those
rules directly with `code`.

| Rule in paper | Rule in Coq           |
|---------------|-----------------------|
| reflexivity   | `rreflexivity_rule`   |
| seq           | `rbind_rule`          |
| swap          | `rswap_rule`          |
| eqDistrL      | `rrewrite_eqDistrL`   |
| symmetry      | `rsymmetry`           |

Some rules are for now only proven in the logic but have not been lifted
to packages, they can be found in `theories/Crypt/rules/UniformStateProb.v`:

| Rule in paper | Rule in Coq             |
|---------------|-------------------------|
| uniform       | `bounded_do_while_rule` |
| asrt          | `assert_rule`           |
| asrtL         | `assert_rule_left`      |

Finally the "bwhile" rule is proven as `bounded_do_while_rule` in
`theories/Crypt/rules/RulesStateProb.v`.

### Semantic model and soundness of rules

This part of the mapping corresponds to section 5.

#### 5.1 Relational effect observation

Start by reading the two following files.

Appearing abstract notions in the first
file: Categories, functors, relative monads, 
lax morphisms of relative monads,
isomorphisms of functors. All order-enriched.
The second files instantiate all of those abstract notions.
`theories/Relational/OrderEnrichedCategory.v`
`theories/Relational/OrderEnrichedCategory.v`


Free monads are defined here:
`theories/Crypt/rhl_semantics/free_monad/FreeProbProg.v`

The category of choiceTypes is introduced here:
`theories/Crypt/rhl_semantics/ChoiceAsOrd.v`
choiceType's are only useful to subdistributions.
They one of the reason why our monads are always relative. 

More basic categories (less relevant to read):
`theories/Crypt/rhl_semantics/more_categories/RelativeMonadMorph_prod.v`
`theories/Crypt/rhl_semantics/more_categories/LaxComp.v`
`theories/Crypt/rhl_semantics/more_categories/LaxFunctorsAndTransf.v`
`theories/Crypt/rhl_semantics/more_categories/InitialRelativeMonad.v`


#### 5.2 The probabilistic relational effect observation


`theories/Crypt/rhl_semantics/only_prob/Couplings.v`
`theories/Crypt/rhl_semantics/only_prob/Theta_dens.v`
`(theories/Crypt/rhl_semantics/only_prob/Theta_exCP.v)`
`theories/Crypt/rhl_semantics/only_prob/ThetaDex.v`


#### 5.3 The stateful and probabilistic relational effect observation

Abstract:
`theories/Crypt/rhl_semantics/more_categories/OrderEnrichedRelativeAdjunctions.v`
`theories/Crypt/rhl_semantics/more_categories/LaxMorphismOfRelAdjunctions.v`
`theories/Crypt/rhl_semantics/more_categories/TransformingLaxMorph.v`

Instances:
`theories/Crypt/rhl_semantics/state_prob/OrderEnrichedRelativeAdjunctionsExamples.v`
`theories/Crypt/rhl_semantics/state_prob/StateTransformingLaxMorph.v`
`theories/Crypt/rhl_semantics/state_prob/StateTransfThetaDens.v`
`theories/Crypt/rhl_semantics/state_prob/LiftStateful.v`


## Axioms and assumptions

### Axioms

Throughout the development we rely on the axioms of functional extensionality,
proof irrelevance, as well as propositional extensionality as listed below:

```coq
ax_proof_irrel : ClassicalFacts.proof_irrelevance
propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
      (∀ x : A, f x = g x) → f = g
```

We further rely on the existence of a type of real numbers as used in the
`mathcomp` library.

```coq
R : realType
```

By using `mathcomp-analysis` we also inherit one of the admitted lemmata they
have:

```coq
interchange_psum :
  ∀ (R : realType) (T U : choiceType) (S : T → U → R),
    (∀ x : T, summable (T:=U) (R:=R) (S x)) →
    summable (T:=T) (R:=R) (λ x : T, psum (λ y : U, S x y)) →
    psum (λ x : T, psum (λ y : U, S x y)) =
    psum (λ y : U, psum (λ x : T, S x y))
```

### Admitted lemmata

Our development curreently still contains unproven results. We will list
them in this section.

- Two rules used in the examples are still not proven: `rsamplerC` and
`rsamplerC'` which correspond to commutation laws for sampling.

```coq
rsamplerC :
  ∀ (A : ord_choiceType) (L : {fset Location}) (o : Op)
    (c : program L Game_import A),
    ⊨ ⦃ λ '(h1, h2), h1 = h2
    ⦄ repr (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r))
    ≈ repr (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r)) ⦃ eq ⦄

rsamplerC' :
  ∀ (A : ord_choiceType) (L : {fset Location}) (o : Op)
    (c : program L Game_import A),
    ⊨ ⦃ λ '(h1, h2), h1 = h2
    ⦄ repr (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (r, a))
    ≈ repr (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (r, a)) ⦃ eq ⦄
```
We believe that the rule rsampleC can be given a proof in two steps
(1) interpret the code fragment (a ← c ;; r ← sample o ;; ret (a, r))
(the other one too) as some function S -> SDistr( A x R x S )
for S a set of global states
(this kind of interpretation is discussed in 3.2 in the paper).
This amounts to an evaluation of the first 3 passes of our theta mapping (see 5.4).
(2) If the two code fragments are equal in the latter monad then we win.
It then remains to prove that pure (lifted) subdistributions always
commute with any other stateful function, a fact that should be
entailed by the commutativity of the subdistribution monad.


- The security proof for ElGamal also relies on unproven properties
`pkch_i` and `ch2c_c2ch` stated in `theories/Crypt/examples/Elgamal.v`
saying that the mapping `pk2ch` (respectively `c2ch`) is a bijection between
the group of public keys `PubKey` (respectively `Cipher`) and the ordinal
corresponding to its cardinal `'I_#(PubKey)` (respectively `'I_#(Cipher)`).

- Additionally, the proof for ElGamal relies on `group_OTP` and `group_OTP_math`
also stated in `theories/Crypt/examples/Elgamal.v` saying that for a plaintext
`m` (and `g` the generator of the group),
`C <$ uniform Cipher ;; return c` is equivalent to
`b <$ unifrom {0,.. q-1} ;; c <$ unifrom {0,.. q-1} ;; return (g^+b, m * g^+c)`.
This condition was already proven in the literature.

### Methodology for finding axioms

Our methodology to find such dependencies is to use the `Print Assumptions`
command of Coq which lists axioms a definition depends on.
For instance
```coq
Print Assumptions par_commut.
```
will yield
```coq
Axioms:
π.rel_choiceTypes : Type
boolp.propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
π.probE : Type → Type
boolp.functional_extensionality_dep
  : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
	  (∀ x : A, f x = g x) → f = g
π.chEmb : π.rel_choiceTypes → choiceType
```

Note that `π.rel_choiceTypes`, `π.probE` and `π.chEmb` are not actually axioms
but instead parameters of the `Package` module, which are listed nonetheless.

### TODO Check for other parts of the development
