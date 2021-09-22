![SSProve](https://user-images.githubusercontent.com/5850655/111436014-c6811f00-8701-11eb-9363-3f2a1b9e9da1.png)

This repository contains the Coq formalisation of the paper:
- **[SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq](https://www.computer.org/csdl/proceedings-article/csf/2021/760700a608/1uvIdwNa5Ne).**
  Carmine Abate, Philipp G. Haselwarter, Exequiel Rivas, Antoine Van Muylder,
  Théo Winterhalter, Cătălin Hrițcu, Kenji Maillard, and Bas Spitters.
  CSF 2021 **distinguished paper**.
- [content-identical preprint without publisher paywall](https://eprint.iacr.org/2021/397)

This README serves as a guide to running verification and finding the
correspondence between the claims in the paper and the formal proofs in Coq, as
well as listing the small set of axioms on which the formalisation relies
(either entirely standard ones or transitive ones from `mathcomp-analysis`).

## Documentation

A documentation is available in [DOC.md].

## Additional material

- [CSF'21](https://youtu.be/MlwQ7CfNH5Q): Video accompanying the publication introducing the general framework (speaker: Philipp Haselwarter)
- [TYPES'21](https://youtu.be/FdMRB1mnyUA): Video focused on semantics and programming logic (speaker: Antoine Van Muylder)
- [Coq Workshop '21](https://youtu.be/uYhItPhA-Y8): Video illustrating the formalisation (speaker: Théo Winterhalter)

## Installation

#### Prerequisites

- OCaml `>=4.05.0 & <4.12`
- Coq `8.13.1`
- Equations `1.2.4+8.13`
- Mathcomp analysis `0.3.10`
- Coq Extructures `0.2.2`

You can get them all from the `opam` package manager for OCaml:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.13.1 coq-equations.1.2.4+8.13 coq-mathcomp-analysis.0.3.10 coq-extructures.0.2.2
```

To build the dependency graph, you can optionally install `graphviz`.
On macOS, `gsed` is additionally required for this.

#### Running verification

Run `make` from this directory to verify all the Coq files.
This should succeed displaying only the list of axioms used for our listed
results.

Run `make graph` to build a graph of dependencies between sources.

## Directory organisation

| Directory             | Description                                          |
|-----------------------|------------------------------------------------------|
| [theories]           | Root of all the Coq files                            |
| [theories/Mon]        | External development coming from "Dijkstra Monads For All" |
| [theories/Relational] | External development coming from "The Next 700 Relational Program Logics"|
| [theories/Crypt]      | This paper                                           |

Unless specified with a full path, all files considered in this README can
safely be assumed to be in [theories/Crypt].

## Mapping between paper and formalisation

### Package definition and laws

The formalisation of packages can be found in the [package] directory.

The definition of packages can be found in [pkg_core_definition.v].
Herein, `package L I E` is the type of packages with set of locations `L`,
import interface `I` and export interface `E`.

Package laws, as introduced in the paper, are all stated and proven in
[pkg_composition.v] directly on raw packages.

#### Sequential composition

In Coq, we call `link p1 p2` the sequential composition of `p1` and `p2`
(written `p1 ∘ p2` in the paper, but also in Coq thanks to notations).

```coq
Definition link (p1 p2 : raw_package) : raw_package.
```

Linking is valid if the export and import match, and its set of locations
is the union of those from both packages (`:|:` denotes union of sets):
```coq
Lemma valid_link :
  ∀ L1 L2 I M E p1 p2,
    ValidPackage L1 M E p1 →
    ValidPackage L2 I M p2 →
    ValidPackage (L1 :|: L2) I E (link p1 p2).
```

Associativity is stated as follows:

```coq
Lemma link_assoc :
  ∀ p1 p2 p3,
    link p1 (link p2 p3) =
    link (link p1 p2) p3.
```
It holds directly on raw packages, even if they are ill-formed.

#### Parallel composition

In Coq, we write `par p1 p2` for the parallel composition of `p1` and `p2`
(written `p1 || p2` in the paper).

```coq
Definition par (p1 p2 : raw_package) : raw_package.
```

The validity of parallel composition can be proven with the following lemma:
```coq
Lemma valid_par :
  ∀ L1 L2 I1 I2 E1 E2 p1 p2,
    Parable p1 p2 →
    ValidPackage L1 I1 E1 p1 →
    ValidPackage L2 I2 E2 p2 →
    ValidPackage (L1 :|: L2) (I1 :|: I2) (E1 :|: E2) (par p1 p2).
```

The `Parable` condition checks that the export interfaces are indeed disjoint.

We have commutativity as follows:
```coq
Lemma par_commut :
  ∀ p1 p2,
    Parable p1 p2 →
    par p1 p2 = par p2 p1.
```
This lemma does not work on arbitrary raw packages, it requires that the
packages implement disjoint signatures.

Associativity on the other hand is free from this requirement:
```coq
Lemma par_assoc :
  ∀ p1 p2 p3,
    par p1 (par p2 p3) = par (par p1 p2) p3.
```

#### Identity package

The identity package is called `ID` in Coq and has the following type:
```coq
Definition ID (I : Interface) : raw_package.
```

Its validity is stated as
```coq
Lemma valid_ID :
  ∀ L I,
    flat I →
    ValidPackage L I I (ID I).
```

The extra `flat I` condition on the interface essentially forbids overloading:
there cannot be two procedures in `I` that share the same name, but have
different types. While our type of interface could in theory allow such
overloading, the way we build packages forbids us from ever implementing them,
hence the restriction.

The two identity laws are as follows:
```coq
Lemma link_id :
  ∀ L I E p,
    ValidPackage L I E p →
    flat I →
    trimmed E p →
    link p (ID I) = p.
```

```coq
Lemma id_link :
  ∀ L I E p,
    ValidPackage L I E p →
    trimmed E p →
    link (ID E) p = p.
```

In both cases, we ask that the package we link the identity package with is
`trimmed`, meaning that it implements *exactly* its export interface and nothing
more. Packages created through our operations always verify this property
(as such it can be checked automatically on those).

#### Interchange between sequential and parallel composition

Finally we prove a law involving sequential and parallel composition
stating how we can interchange them:
```coq
Lemma interchange :
  ∀ A B C D E F L1 L2 L3 L4 p1 p2 p3 p4,
    ValidPackage L1 B A p1 →
    ValidPackage L2 E D p2 →
    ValidPackage L3 C B p3 →
    ValidPackage L4 F E p4 →
    trimmed A p1 →
    trimmed D p2 →
    Parable p3 p4 →
    par (link p1 p3) (link p2 p4) = link (par p1 p2) (par p3 p4).
```
where the last line can be read as
`(p1 ∘ p3) || (p2 ∘ p4) = (p1 || p2) ∘ (p3 || p4)`.

It once again requires some validity and trimming properties.


### Examples

#### PRF

The PRF example is developed in [examples/PRF.v].
The security theorem is the following:

```coq
Theorem security_based_on_prf :
  ∀ LA A,
    ValidPackage LA
      [interface val #[i1] : 'word → 'word × 'word ] A_export A →
    fdisjoint LA (IND_CPA false).(locs) →
    fdisjoint LA (IND_CPA true).(locs) →
    Advantage IND_CPA A <=
    prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
    statistical_gap A +
    prf_epsilon (A ∘ MOD_CPA_tt_pkg).
```

As we claim in the paper, it bounds the advantage of any adversary to the
game pair `IND_CPA` by the sum of the statistical gap and the advantages against
`MOD_CPA`.

Note that we require some state separation hypotheses here, as such disjointness
of state is not required by our package definitions and laws.

#### ElGamal

The ElGamal example is developed in [examples/ElGamal.v].
The security theorem is the following:

```coq
Theorem ElGamal_OT :
  ∀ LA A,
    ValidPackage LA [interface val #[challenge_id'] : 'plain → 'cipher] A_export A →
    fdisjoint LA (ots_real_vs_rnd true).(locs) →
    fdisjoint LA (ots_real_vs_rnd false).(locs) →
    Advantage ots_real_vs_rnd A <= AdvantageE DH_rnd DH_real (A ∘ Aux).
```

#### KEM-DEM

The KEM-DEM case-study can be found in [examples/KEMDEM.v].

The single key lemma is identified by `single_key_a` and `single_key_b`,
corresponding to the two inequalities of the paper. Their statements are
really verbose because of a lot of side-conditions pertaining to the validity
of the composed packages so we refer the user to the file.

The invariant used to prove perfect indistinguishability is given by
```coq
Notation inv := (
  heap_ignore KEY_loc ⋊
  triple_rhs pk_loc k_loc ek_loc PKE_inv ⋊
  couple_lhs pk_loc sk_loc (sameSomeRel PkeyPair)
).
```
We one again refer the use to the commented file for details.
Said perfect indistinguishability is stated as
```coq
Lemma PKE_CCA_perf :
  ∀ b, (PKE_CCA KEM_DEM b) ≈₀ Aux b.
```
while the final security theorem is the following:
```coq
Theorem PKE_security :
  ∀ LA A,
    ValidPackage LA PKE_CCA_out A_export A →
    fdisjoint LA PKE_CCA_loc →
    fdisjoint LA Aux_loc →
    Advantage (PKE_CCA KEM_DEM) A <=
    Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM true)) +
    Advantage DEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (KEM false) (ID DEM_out)) +
    Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM false)).
```

#### Σ-protocols

The Σ-protocols case-study is divided over three files:
[examples/RandomOracle.v], [examples/SigmaProtocol.v] and [examples/Schnorr.v].


### Probabilistic relational program logic

Figure 13 presents a selection of rules for our probabilistic relational
program logic. Most of them can be found in
[package/pkg_rhl.v] which provides an interface for using these
rules directly with `code`.

| Rule in paper | Rule in Coq           |
|---------------|-----------------------|
| reflexivity   | `rreflexivity_rule`   |
| seq           | `rbind_rule`          |
| swap          | `rswap_rule`          |
| eqDistrL      | `rrewrite_eqDistrL`   |
| symmetry      | `rsymmetry`           |
| for-loop      | `for_loop_rule`       |
| uniform       | `r_uniform_bij`       |
| asrt          | `r_assert'`           |
| asrtL         | `r_assertL`           |

Finally the "bwhile" rule is proven as `bounded_do_while_rule` in
[rules/RulesStateProb.v].

### Lemmas 1 & 2 and Theorems 1 & 2 from the paper

We now list the lemmas and theorems about packages from the paper and in the
case of Theorems 1 & 2 proven using our probabilistic relational program
logic. The first two can be found in [package/pkg_advantage.v],
the other two in [package/pkg_rhl.v].

**Lemma 1 (Triangle Inequality)**
```coq
Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
```

**Lemma 2 (Reduction)**
```coq
Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
```

**Theorem 1**
```coq
Lemma eq_upto_inv_perf_ind :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV' L₀ L₁ I →
    I (empty_heap, empty_heap) →
    fdisjoint LA L₀ →
    fdisjoint LA L₁ →
    eq_up_to_inv E I p₀ p₁ →
    AdvantageE p₀ p₁ A = 0.
```

**Theorem 2**
```coq
Lemma Pr_eq_empty :
  ∀ {X Y : ord_choiceType}
    {A : pred (X * heap_choiceType)} {B : pred (Y * heap_choiceType)}
    Ψ ϕ
    (c1 : FrStP heap_choiceType X) (c2 : FrStP heap_choiceType Y)
    ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄ →
    Ψ (empty_heap, empty_heap) →
    (∀ x y,  ϕ x y → (A x) ↔ (B y)) →
    \P_[ θ_dens (θ0 c1 empty_heap) ] A =
    \P_[ θ_dens (θ0 c2 empty_heap) ] B.
```

### Semantic model and soundness of rules

This part of the mapping corresponds to section 5.

#### 5.1 Relational effect observation

In [theories/Relational/OrderEnrichedCategory.v] we introduce some abstract
notions such as categories, functors, relative monads, lax morphisms of relative
monads and isomorphisms of functors, all of which are order-enriched.
The file [theories/Relational/OrderEnrichedCategory.v] instantiates all of these
abstract notions.

Free monads are defined in
[rhl_semantics/free_monad/FreeProbProg.v].

In [rhl_semantics/ChoiceAsOrd.v] we introduce the category of
choice types (`choiceType`) which are useful for sub-distributions:
they are basically the types from which we can sample.
They are one of the reasons why our monads are always relative.

More basic categories can be found in the directory
[rhl_semantics/more_categories/], namely in the files
[RelativeMonadMorph_prod.v], [LaxComp.v], [LaxFunctorsAndTransf.v] and
[InitialRelativeMonad.v].


#### 5.2 The probabilistic relational effect observation

The theory for §5.2 is developed in the following files:
[rhl_semantics/only_prob/Couplings.v],
[rhl_semantics/only_prob/Theta_dens.v],
([rhl_semantics/only_prob/Theta_exCP.v]),
[rhl_semantics/only_prob/ThetaDex.v].


#### 5.3 The stateful and probabilistic relational effect observation

The theory for §5.3 is developed in the following files, divided in two
lists, one for abstract results, and one for the instances we use.

Abstract (in [rhl_semantics/more_categories/]):
[OrderEnrichedRelativeAdjunctions.v],
[LaxMorphismOfRelAdjunctions.v],
[TransformingLaxMorph.v].

Instances (in [rhl_semantics/state_prob/]):
[OrderEnrichedRelativeAdjunctionsExamples.v],
[StateTransformingLaxMorph.v],
[StateTransfThetaDens.v],
[LiftStateful.v].


## Axioms

### List of axioms

In our development we rely on the following standard axioms: functional
extensionality, proof irrelevance, and propositional extensionality, as listed
below.

```coq
ax_proof_irrel : ClassicalFacts.proof_irrelevance
propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
      (∀ x : A, f x = g x) → f = g
```

We also rely on the constructive indefinite description axiom, whose use
we inherit transitively from the `mathcomp-analysis` library.

```coq
boolp.constructive_indefinite_description :
  ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
```

The `mathcomp-analysis` library also uses an axiom to abstract away from any
specific construction of the reals:

```coq
R : realType
```
One could plug in any real number construction: Cauchy, Dedekind, ...
In `mathcomp`s ` Rstruct.v` an instance is built from any instance of the
abstract `stdlib` reals.  An instance of the latter is built from the
(constructive) Cauchy reals in `Coq.Reals.ClassicalConstructiveReals`.

Finally, by using `mathcomp-analysis` we also inherit an admitted lemma they have:

```coq
interchange_psum :
  ∀ (R : realType) (T U : choiceType) (S : T → U → R),
    (∀ x : T, summable (T:=U) (R:=R) (S x)) →
    summable (T:=T) (R:=R) (λ x : T, psum (λ y : U, S x y)) →
    psum (λ x : T, psum (λ y : U, S x y)) =
    psum (λ y : U, psum (λ x : T, S x y))
```

### Other admits not used by results from the paper

Our development also contains a few new work-in-progress results that are
admitted, but none of them is used to show the results from the paper above.

### How to find axioms/admits

We use the `Print Assumptions`command of Coq to list the axioms/admits on which
a definition, lemma, or theorem depends. In [Main.v] we run this
command on all the results above at once:
```coq
Print Assumptions results_from_the_paper.
```
which yields
```coq
Axioms:
boolp.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
realsum.interchange_psum
  : forall (R : reals.Real.type) (T U : choice.Choice.type)
      (S : choice.Choice.sort T -> choice.Choice.sort U -> reals.Real.sort R),
    (forall x : choice.Choice.sort T, realsum.summable (T:=U) (R:=R) (S x)) ->
    realsum.summable (T:=T) (R:=R)
      (fun x : choice.Choice.sort T =>
       realsum.psum (fun y : choice.Choice.sort U => S x y)) ->
    realsum.psum
      (fun x : choice.Choice.sort T =>
       realsum.psum (fun y : choice.Choice.sort U => S x y)) =
    realsum.psum
      (fun y : choice.Choice.sort U =>
       realsum.psum (fun x : choice.Choice.sort T => S x y))
boolp.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
boolp.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
SPropBase.ax_proof_irrel : ClassicalFacts.proof_irrelevance
Axioms.R : reals.Real.type
```

The ElGamal example is parametrized by a cyclic group using a Coq functor.
To print its axioms we have to provide an instance of this functor, and for
simplicity we chose to use ℤ₃ as an instance even if it is not realistic.
The axioms we use do not depend on the instance itself.




[theories]: theories
[theories/Mon]: theories/Mon
[theories/Relational]: theories/Relational
[theories/Crypt]: theories/Crypt
[package]: theories/Crypt/package
[pkg_core_definition.v]: theories/Crypt/package/pkg_core_definition.v
[pkg_composition.v]: theories/Crypt/package/pkg_composition.v
[examples/PRF.v]: theories/Crypt/examples/PRF.v
[examples/ElGamal.v]: theories/Crypt/examples/ElGamal.v
[examples/KEMDEM.v]: theories/Crypt/examples/KEMDEM.v
[examples/RandomOracle.v]: theories/Crypt/examples/RandomOracle.v
[examples/SigmaProtocol.v]: theories/Crypt/examples/SigmaProtocol.v
[examples/Schnorr.v]: theories/Crypt/examples/Schnorr.v
[package/pkg_rhl.v]: theories/Crypt/package/pkg_rhl.v
[rules/RulesStateProb.v]: theories/Crypt/rules/RulesStateProb.v
[package/pkg_advantage.v]: theories/Crypt/package/pkg_advantage.v
[theories/Relational/OrderEnrichedCategory.v]: theories/Relational/OrderEnrichedCategory.v
[rhl_semantics/free_monad/FreeProbProg.v]: theories/Crypt/rhl_semantics/free_monad/FreeProbProg.v
[rhl_semantics/ChoiceAsOrd.v]: theories/Crypt/rhl_semantics/ChoiceAsOrd.v
[rhl_semantics/more_categories/]: theories/Crypt/rhl_semantics/more_categories/
[RelativeMonadMorph_prod.v]: theories/Crypt/rhl_semantics/more_categories/RelativeMonadMorph_prod.v
[LaxComp.v]: theories/Crypt/rhl_semantics/more_categories/LaxComp.v
[LaxFunctorsAndTransf.v]: theories/Crypt/rhl_semantics/more_categories/LaxFunctorsAndTransf.v
[InitialRelativeMonad.v]: theories/Crypt/rhl_semantics/more_categories/InitialRelativeMonad.v
[rhl_semantics/only_prob/Couplings.v]: theories/Crypt/rhl_semantics/only_prob/Couplings.v
[rhl_semantics/only_prob/Theta_dens.v]: theories/Crypt/rhl_semantics/only_prob/Theta_dens.v
[rhl_semantics/only_prob/Theta_exCP.v]: theories/Crypt/rhl_semantics/only_prob/Theta_exCP.v
[rhl_semantics/only_prob/ThetaDex.v]: theories/Crypt/rhl_semantics/only_prob/ThetaDex.v
[OrderEnrichedRelativeAdjunctions.v]: theories/Crypt/rhl_semantics/more_categories/OrderEnrichedRelativeAdjunctions.v
[LaxMorphismOfRelAdjunctions.v]: theories/Crypt/rhl_semantics/more_categories/LaxMorphismOfRelAdjunctions.v
[TransformingLaxMorph.v]: theories/Crypt/rhl_semantics/more_categories/TransformingLaxMorph.v
[rhl_semantics/state_prob/]: theories/Crypt/rhl_semantics/state_prob/
[OrderEnrichedRelativeAdjunctionsExamples.v]: theories/Crypt/rhl_semantics/state_prob/OrderEnrichedRelativeAdjunctionsExamples.v
[StateTransformingLaxMorph.v]: theories/Crypt/rhl_semantics/state_prob/StateTransformingLaxMorph.v
[StateTransfThetaDens.v]: theories/Crypt/rhl_semantics/state_prob/StateTransfThetaDens.v
[LiftStateful.v]: theories/Crypt/rhl_semantics/state_prob/LiftStateful.v
[Main.v]: theories/Crypt/Main.v
[DOC.md]: ./DOC.md
