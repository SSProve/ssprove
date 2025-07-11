![SSProve](https://user-images.githubusercontent.com/5850655/111436014-c6811f00-8701-11eb-9363-3f2a1b9e9da1.png)

This repository contains the Coq formalisation of the paper:\
**SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq**
- Extended journal version published at TOPLAS ([DOI](https://dl.acm.org/doi/10.1145/3594735)).
  Philipp G. Haselwarter, Exequiel Rivas, Antoine Van Muylder, Théo Winterhalter,
  Carmine Abate, Nikolaj Sidorenco, Cătălin Hrițcu, Kenji Maillard, and
  Bas Spitters. ([eprint](https://eprint.iacr.org/2021/397))
- Conference version published at CSF 2021 (**distinguished paper award**).
  Carmine Abate, Philipp G. Haselwarter, Exequiel Rivas, Antoine Van Muylder,
  Théo Winterhalter, Cătălin Hrițcu, Kenji Maillard, and Bas Spitters.
  ([ieee](https://www.computer.org/csdl/proceedings-article/csf/2021/760700a608/1uvIdwNa5Ne),
   [eprint](https://eprint.iacr.org/2021/397/20210526:113037))

Secondary literature:
* **The Last Yard: Foundational End-to-End Verification of High-Speed Cryptography** at CPP'24.
Philipp G. Haselwarter, Benjamin Salling Hvass, Lasse Letager Hansen, Théo Winterhalter, Cătălin Hriţcu, and Bas Spitters. ([DOI](https://doi.org/10.1145/3636501.3636961))

This README serves as a guide to running verification and finding the
correspondence between the claims in the paper and the formal proofs in Coq, as
well as listing the small set of axioms on which the formalisation relies
(either entirely standard ones or transitive ones from `mathcomp-analysis`).

## Documentation

* A documentation is available in [DOC.md].
* Code documentation is available [coqdoc documentation](https://SSProve.github.io/ssprove/index.html).
* [Dependency graph](https://SSProve.github.io/ssprove/dependencies.svg)


## Additional material

- [CSF'21](https://youtu.be/MlwQ7CfNH5Q): Video accompanying the publication introducing the general framework (speaker: Philipp Haselwarter)
- [TYPES'21](https://youtu.be/FdMRB1mnyUA): Video focused on semantics and programming logic (speaker: Antoine Van Muylder)
- [Coq Workshop '21](https://youtu.be/uYhItPhA-Y8): Video illustrating the formalisation (speaker: Théo Winterhalter)

## Installation

There are two installation options:
- via `opam`
- via `nix`

#### Prerequisites

- OCaml
- Coq
- Equations
- Mathcomp
- Mathcomp analysis
- Mathcomp word
- Coq Extructures
- Coq Deriving


### OPAM-based installation


You can get all dependencies and install SSProve from the `opam` package manager for OCaml:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-ssprove
```

To build the dependency graph, you can optionally install `graphviz`.
On macOS, `gsed` is additionally required for this.

### Nix-based installation

`ssprove` is available on `nixpkgs`, e.g., `coqPackages_8_19.ssprove`.
The following flake-based templates for your new SSProve project are available:
- [SSProve latest](.nix/flake.nix.template_latest) -- provides a project setup
with the latest SSProve development readily installed.
- [SSProve versioned](.nix/flake.nix.template_versioned) -- provides
a Nix flake that loads a dedicated version (that you may change).

#### Quick start guide

##### Nix installation
This is performed only once.
1. [Install Nix](https://nix.dev/install-nix.html) with `curl -L https://nixos.org/nix/install | sh -s -- --daemon`
2. Enable [flake support](https://nixos.wiki/wiki/Flakes) with `mkdir -p ~/.config/nix && echo -e "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf`
All set.

##### Project setup
1. Create a new project folder and `cd` into it.
2. Copy one of the above templates into it (removing the `.template*` suffix).
3. And finally run `nix develop` which throws you into a shell where SSProve is already installed. (`From SSProve.Crypt Require Import ...`)

You may need to initialize the project as a Git repository and add the `flake.nix` to it.
The generated `flake.lock` pins the versions and hence also needs to be added to this new project repo.

In the `flake.nix`, you can add [more Coq packages from the Nix repository](https://github.com/NixOS/nixpkgs/blob/a194f9d0654e368fb900830a19396f9d7792647a/pkgs/top-level/coq-packages.nix#L20).

## Build instructions

#### Running verification

Run `make` from this directory to verify all the Coq files.
This should succeed displaying only the list of axioms used for our listed
results.

Run `make graph` to build a graph of dependencies between sources.

## Directory organisation

| Directory                 | Description                                                               |
|---------------------------|---------------------------------------------------------------------------|
| [theories]                | Root of all the Coq files                                                 |
| [theories/Mon]            | External development coming from "Dijkstra Monads For All"                |
| [theories/Relational]     | External development coming from "The Next 700 Relational Program Logics" |
| [theories/Crypt]          | This paper                                                                |
| [theories/Crypt/examples] | Implementations and proofs of cryptographic protocols                     |

Unless specified with a full path, all files considered in this README can
safely be assumed to be in [theories/Crypt].

## Mapping between paper and formalisation

### Package definition and laws

The formalisation of packages can be found in the [package] directory.

The definition of packages can be found in [pkg_core_definition.v].
Herein, `package I E` is the type of packages with import interface `I`
and export interface `E`. It is defined on top of `raw_package` which does
not contain the information about its interfaces and the locations it uses.

Package laws, as introduced in the paper, are all stated and proven in
[pkg_composition.v] directly on raw packages. This technical detail is not
mentioned in the paper, but we are nonetheless only interested in these
laws over proper packages whose interfaces match.

#### Sequential composition

In Coq, we call `link p1 p2` the sequential composition of `p1` and `p2`
(written `p1 ∘ p2` in the paper, but also in Coq thanks to notations).

```coq
Definition link (p1 p2 : raw_package) : raw_package.
```

Linking is valid if the export and import match, and its set of locations
is the union of those from both packages (`unionm` denotes union of `fmap`s):
```coq
Lemma valid_link :
  ∀ L1 L2 I M E p1 p2,
    ValidPackage L1 M E p1 →
    ValidPackage L2 I M p2 →
    fcompat L1 L2 →
    ValidPackage (unionm L1 L2) I E (link p1 p2).
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
    ValidPackage L1 I1 E1 p1 →
    ValidPackage L2 I2 E2 p2 →
    fseparate p1 p2 →
    fcompat L1 L2 →
    fcompat I1 I2 →
    ValidPackage (L1 :|: L2) (I1 :|: I2) (E1 :|: E2) (par p1 p2).
```

The `fseparate` condition checks that the export interfaces are indeed disjoint.
The `fcompat conditions check that the locations and imports are compatible i.e.
that if they define the same key it also has the same value.

We have commutativity as follows:
```coq
Lemma par_commut :
  ∀ p1 p2,
    fseparate p1 p2 →
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
  ∀ L I, ValidPackage L I I (ID I).
```

The two identity laws are as follows:
```coq
Lemma link_id :
  ∀ L I E p,
    ValidPackage L I E p →
    link p (ID I) = p.
```

```coq
Lemma id_link :
  ∀ L I E p,
    ValidPackage L I E p →
    link (ID E) p = p.
```

In both cases, the package is required to be a valid on specific
interfaces that match with the interface argument for ID.

#### Interchange between sequential and parallel composition

Finally, we prove a law involving sequential and parallel composition
stating how we can interchange them:
```coq
Lemma interchange :
  ∀ A B C D E F L1 L2 L3 L4 p1 p2 p3 p4,
    ValidPackage L1 B A p1 →
    ValidPackage L2 E D p2 →
    ValidPackage L3 C B p3 →
    ValidPackage L4 F E p4 →
    fseparate p3 p4 →
    par (link p1 p3) (link p2 p4) = link (par p1 p2) (par p3 p4).
```
where the last line can be read as
`(p1 ∘ p3) || (p2 ∘ p4) = (p1 || p2) ∘ (p3 || p4)`.

It once again requires some validity and separation properties.


### Examples

#### PRF

The PRF example is developed in [examples/PRF.v].
The security theorem is the following:

```coq
Theorem security_based_on_prf :
  ∀ LA A,
    ValidPackage LA
      [interface val #[i1] : 'word → 'word × 'word ] A_export A →
    fseparate LA (IND_CPA false).(locs) →
    fseparate LA (IND_CPA true).(locs) →
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
    fseparate LA (ots_real_vs_rnd true).(locs) →
    fseparate LA (ots_real_vs_rnd false).(locs) →
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
    fseparate LA PKE_CCA_loc →
    fseparate LA Aux_loc →
    Advantage (PKE_CCA KEM_DEM) A <=
    Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM true)) +
    Advantage DEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (KEM false) (ID DEM_out)) +
    Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM false)).
```

#### Σ-protocols

The Σ-protocols case-study is divided over two files:
[examples/SigmaProtocol.v] and [examples/Schnorr.v].

The security theorem for hiding of commitment scheme from Σ-protocols is:

```coq
Theorem commitment_hiding :
  ∀ LA A eps,
    ValidPackage LA [interface
      val #[ HIDING ] : chInput → chMessage
    ] A_export A →
    (∀ B,
      ValidPackage (LA :|: Com_locs) [interface
        val #[ TRANSCRIPT ] : chInput → chTranscript
      ] A_export B →
      ɛ_SHVZK B <= eps
    ) →
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A <=
    (ɛ_hiding A) + eps + eps.
```

And the corresponding theorem for binding:

```coq
Theorem commitment_binding :
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface
      val #[ SOUNDNESS ] : chStatement → 'bool
    ] A_export A →
    ValidPackage LAdv [interface] [interface
      val #[ ADV ] : chStatement → chSoundness
    ] Adv →
    fseparate LA (Sigma_locs :|: LAdv) →
    AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <=
    ɛ_soundness A Adv.
```

Combining the above theorems with the instantiation of Schnorr's protocol we get a commitment scheme given by:

```coq
Theorem schnorr_com_hiding :
  ∀ LA A,
    ValidPackage LA [interface
      val #[ HIDING ] : chInput → chMessage
    ] A_export A →
    fseparate LA Com_locs →
    fseparate LA Sigma_locs →
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A <= 0.
```

and

```coq
Theorem schnorr_com_binding :
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface
      val #[ SOUNDNESS ] : chStatement → 'bool
    ] A_export A →
    ValidPackage LAdv [interface] [interface
      val #[ ADV ] : chStatement → chSoundness
    ] Adv →
    fseparate LA (Sigma_locs :|: LAdv) →
    AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <= 0.
```

#### Simple secret sharing

This 2-out-of-2 secret-sharing shceme can be found in the file
[examples/SecretSharing.v]. It formalizes the protocol presented in the chapter
3.2 of the book [The joy of cryptography](https://joyofcryptography.com/).

```coq
Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'seq 'word ]
    A_export A ->
  Advantage SHARE A = 0%R.
```
Which ensures that the scheme has perfect security, as both games defined in the
book are proved equivalent.

#### Shamir Secret Sharing

This formalises Theorem 3.13 from [The Joy of Cryptography](https://joyofcryptography.com/) (p. 60). It
formalises Shamir's Secret Sharing scheme and proves that it has perfect
security. It is a t-out-of-n secret sharing scheme over the field ['F_p]. This
case-study is contained in [examples/ShamirSecretSharing.v].

The main result is the following:

```coq
Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[shares]: ('word × 'word) × 'set 'party → 'seq 'share ]
    A_export A ->
  Advantage SHARE A = 0%R.
```

### Probabilistic relational program logic

The paper version (CSF: Figure 13, journal: section 4.1) introduces a selection
of rules for our probabilistic relational program logic.
Most of them can be found in [package/pkg_rhl.v] which provides an interface for
using these rules directly with `code`.
We separate by a slash (/) rule names that differ in the CSF (left) and journal
(right) version.

| Rule in paper     | Rule in Coq           |
|-------------------|-----------------------|
| reflexivity       | `rreflexivity_rule`   |
| seq               | `rbind_rule`          |
| swap              | `rswap_rule`          |
| eqDistrL          | `rrewrite_eqDistrL`   |
| symmetry          | `rsymmetry`           |
| for-loop          | `for_loop_rule`       |
| uniform           | `r_uniform_bij`       |
| dead-sample       | `r_dead_sample`       |
| sample-irrelevant | `r_const_sample`      |
| asrt / assert     | `r_assert'`           |
| asrtL / assertL   | `r_assertL`           |
| assertD           | `r_assertD`           |
| put-get           | `r_put_get`           |
| async-get-lhs     | `r_get_remember_lhs`  |
| async-get-lhs-rem | `r_get_remind_lhs`    |
| async-put-lhs     | `r_put_lhs`           |
| restore-pre-lhs   | `r_restore_lhs`       |

Finally, the "bwhile" / "do-while" rule is proven as
`bounded_do_while_rule` in [rules/RulesStateProb.v].

### More Lemmas and Theorems for packages

We now list the lemmas and theorems about packages from the paper.
Theorems 1 and 2 (CSF) / Theorems 2.4 and 4.1 (journal) were proven using our
probabilistic relational program logic. The first two lemmas below can be found in
[package/pkg_advantage.v], the other two in [package/pkg_rhl.v].

**Lemma 1 / 2.2 (Triangle Inequality)**
```coq
Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
```

**Lemma 2 / 2.3 (Reduction)**
```coq
Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
```

**Theorem 1 / 2.4**
```coq
Lemma eq_upto_inv_perf_ind :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV' L₀ L₁ I →
    I (empty_heap, empty_heap) →
    fseparate LA L₀ →
    fseparate LA L₁ →
    eq_up_to_inv E I p₀ p₁ →
    AdvantageE p₀ p₁ A = 0.
```

**Theorem 2 / 4.1**
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

This part of the mapping corresponds to section 5. Once again,
we refer to results in the paper like so: CSF numbering/journal version numbering.

#### 5.1 Relational effect observation

In our framework, a relational effect observation is defined
as some kind of *lax morphism between order-enriched relative monads*.
This general definition as well as the ingredients it requires are provided
in [theories/Relational/OrderEnrichedCategory.v]. There we introduce
categories, functors, relative monads, lax morphisms of relative
monads and isomorphisms of functors, all of which are order-enriched.

Relational effect observations are lax morphisms between
the following special cases of order-enriched relative monads:
1. A product of Type valued order-enriched relative monads,
   corresponding to pairs of effectful computations.
2. A relational specification monad

To build the above computation part (1) of an effect observation,
the file [theories/Relational/OrderEnrichedRelativeMonadExamples.v]
equips Type with a structure of order-enriched category.
Often we use free monads to package effectful computations.
Those are defined in [rhl_semantics/free_monad/].

Since a relational specification monad as in (2) is by definition
an order-enriched monad with codomain PreOrder, the latter
category has to be endowed with an order-enrichment. This
is done in [theories/Relational/OrderEnrichedRelativeMonadExamples.v].

More basic categories can be found in the directory
[rhl_semantics/more_categories/], namely in the files
[RelativeMonadMorph_prod.v], [LaxComp.v], [LaxFunctorsAndTransf.v] and
[InitialRelativeMonad.v].


#### 5.2 The probabilistic relational effect observation

The files of interest are mainly contained in the
[rhl_semantics/only_prob/] directory.

This relational effect observation is called
`thetaDex` in the development and is defined in the
file [rhl_semantics/only_prob/ThetaDex.v] as a composition:
FreeProb² ---`unary_theta_dens²`---> SDistr² ---`θ_morph`---> Wrelprop

The first part `unary_theta_dens²` consists in interpreting pairs
of probabilistic programs into pairs of actual subdistributions.
This unary semantics for probabilistic programs `unary_theta_dens`
is defined in [rhl_semantics/only_prob/Theta_dens.v].
It is defined by pattern matching on the given probabilistic program
(which can be viewed as a tree).
The free relative monad over a probabilistic signature is defined
in [rhl_semantics/free_monad/FreeProbProg.v].
The codomain of `unary_theta_dens` is defined in
[rhl_semantics/only_prob/SubDistr.v].
Since subdistributions `SDistr(A)` only make sense
when `A` is a `choiceType`, both the domain and codomain
of `unary_theta_dens` are relative monads over
appropriate inclusion functors `choiceType` -> `Type`.
The required order-enrichment for the category of choiceTypes
and this inclusion are defined in the file [rhl_semantics/ChoiceAsOrd.v].

The second part `θ_morph` is conceptually more important.
It is defined in the file [rhl_semantics/only_prob/Theta_exCP.v].
`θ_morph` is "really" lax: it satisfies the morphism laws only
up to inequalities.
The definition of `θ_morph` relies on the notion of couplings,
defined in this file [rhl_semantics/only_prob/Couplings.v].
The proof that it constitutes a lax morphism depends on lemmas
for couplings that can be found in the same file.


#### 5.3 The stateful and probabilistic relational effect observation

The important files are contained in this directory:
[rhl_semantics/state_prob/].


Again the effect observation is defined as a composition:
`thetaFstdex:` FrStP² → stT(Frp²) → stT(Wrel).
See file [StateTransformingLaxMorph.v].

The first part uses `unaryIntState:`  FrStP → stT(Frp)
from the same file which interprets state related instructions
as actual state manipulating functions S → Frp( - x S ).
Probabilistic instructions are left untouched by this morphism.

The more interesting part is the second one (same file)
`stT_thetaDex:` stT(Frp²) → stT(Wrel).
This morphism is obtained by state-transforming the
relational effect observation `thetaDex` from the previous section.

More details about the state transformer implementation are provided
in the next section.


#### CSF state transformer/ section 5.4 of journal version

For the definition of relative monad (Def 5.1 journal),
see section "5.1 Relational effect observation" of the present file.

The general definitions and theorems regarding the state transformer
can be found in [rhl_semantics/more_categories/]:
[OrderEnrichedRelativeAdjunctions.v],
[LaxMorphismOfRelAdjunctions.v],
[TransformingLaxMorph.v].

On the other hand our instances can be found in [rhl_semantics/state_prob/]:
[OrderEnrichedRelativeAdjunctionsExamples.v],
[StateTransformingLaxMorph.v],
[StateTransfThetaDens.v],
[LiftStateful.v].


##### The state transformer on relative monads (i.e. on objects)

The concerned file is [OrderEnrichedRelativeAdjunctions.v],
section `TransformationViaRelativeAdjunction`.
There we transform an arbitrary order-enriched relative monad
using a "transforming adjunction" (Thm 5.5 journal). The notion of transforming
adjunction (Def 5.4 journal) is a generalization of the notion of state adjunction.


State adjunctions for transforming computations/specifications
are built in [OrderEnrichedRelativeAdjunctionsExamples.v].

All of our adjunctions are left relative adjunctions (Def 5.2 journal).
This notion is defined and studied in
[OrderEnrichedRelativeAdjunctions.v] and this includes
Kleisli adjunctions of relative monads (Def 5.3 journal).

##### The state transformer for lax morphisms (i.e. on arrows)

See file [TransformingLaxMorph.v].
Given a lax morphism of relative monads θ : M1 → M2,
both M1 and M2 factor through their Kleisli and
give rise to Kleisli adjunctions. θ induces
a lax morphism Kl(θ) between those Kleisli adjunctions.
Kl(θ) is a lax morphism between left relative adjunctions,
(see [LaxMorphismOfRelAdjunctions.v]) and we can
transform such morphisms of adjunctions using
the theory developed in [TransformingLaxMorph.v].
Finally, out of this transformed morphism of adjunctions we can
extract a lax morphism between monads Tθ : T M1 → T M2, as expected.
This last step is also performed in [TransformingLaxMorph.v].


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
abstract `Coq` reals.  An instance of the latter is built from the
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
boolp.propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
boolp.functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
FunctionalExtensionality.functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
boolp.constructive_indefinite_description :
  ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
SPropBase.ax_proof_irrel : ClassicalFacts.proof_irrelevance
realsum.__admitted__interchange_psum :
  ∀ (R : reals.Real.type) (T U : choice.Choice.type)
    (S : choice.Choice.sort T → choice.Choice.sort U → reals.Real.sort R),
    (∀ x : choice.Choice.sort T, realsum.summable (T:=U) (R:=R) (S x))
    → realsum.summable (T:=T) (R:=R)
        (λ x : choice.Choice.sort T,
           realsum.psum (λ y : choice.Choice.sort U, S x y))
      → realsum.psum
          (λ x : choice.Choice.sort T,
             realsum.psum (λ y : choice.Choice.sort U, S x y)) =
        realsum.psum
          (λ y : choice.Choice.sort U,
             realsum.psum (λ x : choice.Choice.sort T, S x y))
Axioms.R : reals.Real.type
```

The ElGamal example is parametrized by a cyclic group using a Coq functor.
To print its axioms we have to provide an instance of this functor, and for
simplicity we chose to use ℤ₃ as an instance even if it is not realistic.
The axioms we use do not depend on the instance itself.
We do something similar for Schnorr's protocol.




[DOC.md]: ./DOC.md
[examples/ElGamal.v]: theories/Crypt/examples/ElGamal.v
[examples/KEMDEM.v]: theories/Crypt/examples/KEMDEM.v
[examples/PRF.v]: theories/Crypt/examples/PRF.v
[examples/Schnorr.v]: theories/Crypt/examples/Schnorr.v
[examples/SigmaProtocol.v]: theories/Crypt/examples/SigmaProtocol.v
[InitialRelativeMonad.v]: theories/Crypt/rhl_semantics/more_categories/InitialRelativeMonad.v
[LaxComp.v]: theories/Crypt/rhl_semantics/more_categories/LaxComp.v
[LaxFunctorsAndTransf.v]: theories/Crypt/rhl_semantics/more_categories/LaxFunctorsAndTransf.v
[LaxMorphismOfRelAdjunctions.v]: theories/Crypt/rhl_semantics/more_categories/LaxMorphismOfRelAdjunctions.v
[LiftStateful.v]: theories/Crypt/rhl_semantics/state_prob/LiftStateful.v
[Main.v]: theories/Crypt/Main.v
[OrderEnrichedRelativeAdjunctions.v]: theories/Crypt/rhl_semantics/more_categories/OrderEnrichedRelativeAdjunctions.v
[OrderEnrichedRelativeAdjunctionsExamples.v]: theories/Crypt/rhl_semantics/state_prob/OrderEnrichedRelativeAdjunctionsExamples.v
[package]: theories/Crypt/package
[package/pkg_advantage.v]: theories/Crypt/package/pkg_advantage.v
[package/pkg_rhl.v]: theories/Crypt/package/pkg_rhl.v
[pkg_composition.v]: theories/Crypt/package/pkg_composition.v
[pkg_core_definition.v]: theories/Crypt/package/pkg_core_definition.v
[RelativeMonadMorph_prod.v]: theories/Crypt/rhl_semantics/more_categories/RelativeMonadMorph_prod.v
[rhl_semantics/ChoiceAsOrd.v]: theories/Crypt/rhl_semantics/ChoiceAsOrd.v
[rhl_semantics/free_monad/]: theories/Crypt/rhl_semantics/free_monad/
[rhl_semantics/free_monad/FreeProbProg.v]: theories/Crypt/rhl_semantics/free_monad/FreeProbProg.v
[rhl_semantics/more_categories/]: theories/Crypt/rhl_semantics/more_categories/
[rhl_semantics/only_prob/]: theories/Crypt/rhl_semantics/only_prob/
[rhl_semantics/only_prob/Couplings.v]: theories/Crypt/rhl_semantics/only_prob/Couplings.v
[rhl_semantics/only_prob/SubDistr.v]: theories/Crypt/rhl_semantics/only_prob/SubDistr.v
[rhl_semantics/only_prob/Theta_dens.v]: theories/Crypt/rhl_semantics/only_prob/Theta_dens.v
[rhl_semantics/only_prob/Theta_exCP.v]: theories/Crypt/rhl_semantics/only_prob/Theta_exCP.v
[rhl_semantics/only_prob/ThetaDex.v]: theories/Crypt/rhl_semantics/only_prob/ThetaDex.v
[rhl_semantics/state_prob/]: theories/Crypt/rhl_semantics/state_prob/
[rhl_semantics/state_prob/]: theories/Crypt/rhl_semantics/state_prob/
[rules/RulesStateProb.v]: theories/Crypt/rules/RulesStateProb.v
[StateTransformingLaxMorph.v]: theories/Crypt/rhl_semantics/state_prob/StateTransformingLaxMorph.v
[StateTransfThetaDens.v]: theories/Crypt/rhl_semantics/state_prob/StateTransfThetaDens.v
[theories]: theories
[theories/Crypt]: theories/Crypt
[theories/Crypt/examples]: theories/Crypt/examples
[theories/Mon]: theories/Mon
[theories/Relational]: theories/Relational
[theories/Relational/OrderEnrichedCategory.v]: theories/Relational/OrderEnrichedCategory.v
[theories/Relational/OrderEnrichedRelativeMonadExamples.v]: theories/Relational/OrderEnrichedRelativeMonadExamples.v
[TransformingLaxMorph.v]: theories/Crypt/rhl_semantics/more_categories/TransformingLaxMorph.v
