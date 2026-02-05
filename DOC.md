# Getting started with SSProve

This document shall serve as a non-exhaustive guide to **SSProve**.

*This document assumes that you have Coq and SSProve installed and have already
some knowledge of Coq.*

🚧 This document tries to be as exhaustive as possible, but can still be
improved. If you find something missing or not clear enough, feel free to
[open an issue]. 🚧

## Overview

1. [Writing packages]
   1. [Raw code]
   1. [Specialised types]
   1. [Distributions]
   1. [Valid code]
   1. [Packages]
1. [High-level SSP proofs]
   1. [Package algebra]
   1. [Adversarial advantage]
1. [Probabilistic relational program logic]
   1. [Proving perfect indistinguishability]
   1. [Massaging relational judgments]
   1. [Proving relational judgments]
   1. [Crafting invariants]

## Writing packages

SSProve defines a language of *code* which can feature probabilistic sampling,
assertions, memory storing and accesses, but also external procedure import.
It is a *shallow embedding* meaning that one can inject any Coq/Gallina
expression into it by using the `ret` (standing for `return`) operation which we
will expose below.

### Raw code

The main notion of code is defined as the type `raw_code A` which represents
a program returning a value of type `A`. This type `A` is typically—but not
limited to—of type `choice_type`.


Before detailing how to construct them, here is a first example with no
particular meaning.

```coq
#import {sig #[0] : 'nat → 'bool × 'nat } as f ;;
#import {sig #[1] : 'bool → 'unit } as g ;;
'(b,k) ← f 0 ;;
if b then (
  g false ;;
  m ← sample uniform 2 ;;
  ret 0
)
else (
  o ← get ℓ ;;
  #assert (isSome o) as oSome ;;
  let n := getSome o oSome in
  put n := Some (2 + n) ;;
  ret n
)
```
where `ℓ` is defined as
```coq
Definition ℓ := mkloc 0 (None : option nat).
```

It first imports two procedures with respective identifiers `0` and `1` and
types `'nat → 'bool × 'bool` and `'bool → 'unit`, calling them `f` and `g`.
We take the result of `f` (the external procedure) applied to `0` as a pair
`(b,k)` and then do a case-analysis on `b`.
In the `else` branch, we read memory location `ℓ`, assert that it contains a
`Some`, reusing this fact (called `oSome`) to get the value itself.
We then increment this value twice and place it back in memory before
returning the original value.

#### Return constructor `ret`
```coq
ret : ∀ {A}, A → raw_code A
```
Injects any pure value into `raw_code`.

#### Memory access

A `Location` is a pair of a natural number representing an identifier
and an initial value in a `choice_type`, for instance
`mkloc 12 (0 : nat) : Location`. One can *read* memory as follows:
```coq
x ← get ℓ ;; k x
(* Or with pattern matching *)
'p ← get ℓ ;; k p
```
where `k` is a continuation, *i.e.* raw code which can depend on `x`.
One can *write* to a memory location as follows:
```coq
put ℓ := v ;; k
```
where `v` is a value of the right type and `k` a continuation, which this time
doesn't expect any value from the writing.

#### Probabilistic sampling
```coq
x ← sample op ;; k x
(* Or alternatively *)
x <$ op ;; k x
(* Or with pattern matching *)
'p ← sample op ;; k p
```
Here `op : Op` is a (sub-)distribution. See [Distributions].

#### Failure
```coq
fail : ∀ {A : choice_type}, raw_code A
```
Represents a failure in a program. It is obtained by sampling on the null
sub-distribution.

#### Assertion
```coq
#assert b as e ;; k e
(* Alternatively, if the continuation doesn't need the equality *)
#assert b ;; k
```
Assert that the boolean `b` is `true` and store an equality `e : b = true`
to be reused by the continuation.
`#assert true as e ;; k e` simplifies to `k erefl` while
`#assert false as e ;; k e` simplifies to `fail`.

#### Import
```coq
x ← op sig ⋅ arg ;; k x
```
Represents application of imported/assumed procedure of signature `sig : opsig`
to argument `arg`, calling the result `x` before passing it to continuation `k`.
See [Specialised types] for how to define `sig`.
A preferred alternative to writing imports it to use the following notation
```coq
#import sig as f ;; k' f
```
where `f` bound in the continuation is a function which can be applied via bind.
For instance if `sig` is `{sig #[n] : 'nat → 'bool × 'bool }` then
`f` has type `nat → raw_code (bool * bool)` and can be used as
```
x ← f arg ;; k x
```

#### Bind
`raw_code` is a monad and as such it supports a *bind* operator. With value
reuse it can be written as follows:
```coq
x ← v ;; k x
(* Or with pattern matching *)
'p ← v ;; k p
```
and without, as
```coq
v ;; k
```
This operation is not a primitive/constructor and will reduce to the above
constructions when `v` is concrete.

### Specialised types

We have a special type called `choice_type` which contains *codes* for specific
types that we use in our packages. These are the types used in `Location`
and in `opsig` or even in `Op`.

To differentiate them from actual types while retaining some familiarity
we usually style them with a quotation mark in front of the type they represent.
This is the case for instance of `'nat`, `'bool`, `'unit` and `'option` which
are self-explanatory.

We also provide `'fin n` which is the finite type of size `n`.

We also have the product type `chProd x y` which is interpreted to Coq's
product `prod`. For instance `chProd 'nat 'bool` corresponds to `nat * bool`.

Finally we have the type of finite maps `chMap x y` where `x` is the type of
keys, and `y` the type of values.

#### Further notation in specific settings

When defining signatures (`opsig`), interfaces (see [Valid code]), or packages
(see [Packages]), one can further use handy notations for `chProd` and
`chMap`, as exemplified below:

```coq
'nat × 'bool
{map 'nat → 'option 'nat }
```

#### Signatures

A signature (`opsig`) is given by an identifier (a natural number), an
argument type and a return type (both in `choice_type`).
Once can for instance write `(37, ('nat, chProd 'unit 'unit))`.

We provide the following nicer notation:
```coq
{sig #[37] : 'nat → 'unit × 'unit }
```

### Distributions

The user can sample using pretty much any distribution that can be expressed
in `mathcomp-analysis` provided that its support is in `choice_type`.
Writing them by hand might not be very convenient.

For the time being we provide `uniform n` which represents a uniform
distribution landing in `'fin n` as long as `0 < n`.

### Valid code

[Raw code] as described above is well-typed but does not have any guarantees
with respect to what it imports and which location it uses. We therefore
define a notion a validity with respect to an import interface and a set of
locations.

#### Set of locations

The set of locations is expected as type `Locations` using the finite maps
of the [extructures] library. For our purposes, it is advisable to write
them directly as list of locations using the following syntax:
```coq
[fmap ℓ₀ ; ℓ₁ ; ℓ₂ ]
```
An empty location map is written `emptym` and in some cases it might be
necessary to use the union (`unionm`) operator of [extructures].

#### Interfaces

An interface is a finite map (`fmap`) of signatures (`opsig`) corresponding
to the procedures that a piece of code *can* import and use.
Rather than writing them as `fmap` directly, we provide special convenient
notations, as well the type `Interface`.

Interfaces are wrapped in the `[interface]` container which behaves like lists.
They are of the form
```coq
[interface d₀ ; d₁ ; … ; dₙ ]
```
where the `dᵢ` are signatures, given using a special syntax:
```coq
val #[ id ] : src → tgt
```
where `id` is a natural number / identifier, and `src` and `tgt` are codes of
types in `choice_type` given using the special syntax (see [Specialised types]).

Here are examples of interfaces:
```coq
[interface]
```

```coq
[interface
  val #[ 0 ] : 'nat → 'nat ;
  val #[ 1 ] : 'option 'bool → 'unit × {map 'nat → 'bool }
]
```

#### Validity of code

Validity of code `c` with respect to set of locations `L` and import interface
`I` is denoted by the class `ValidCode L I c`.
We derive from it the type `code L I A` of valid code.

Raw code `c` can be cast to `code` by using the notation
```coq
{code c }
```

For instance, in the following, we declare a simple `code` by just giving
the `raw_code` and using the `{code}` notation:
```coq
Definition foo : code emptym [interface] bool :=
  {code ret true }.
```

The fact that this is a class means that in practice, the validity proof
should automatically be inferred by Coq.
In case where automation doesn't work, it is still possible to leverage it to
find which sub-goal it did not solve for you by using the `ssprove_valid`
tactic.

Here is an example using `Equations` that allows us to use the proof mode to
fill in the validity proof.
```coq
Obligation Tactic := idtac.

Definition ℓ : Location := mkloc 0 (0 : nat).

Equations? foo : code emptym [interface] 'nat :=
  foo := {code
    n ← get ℓ ;;
    ret n
  }.
Proof.
  ssprove_valid.
  (* We have to prove (fhas emptym ℓ.1) which does not hold. *)
Abort.
```
We can then see where the mistake was and change `emptym` to
something containing `ℓ` like `[fmap ℓ ]`.

Note that `ssprove_valid` and the inference for `ValidCode` can be extended
with hints. The former using the `ssprove_valid_db` database, the latter with the
`typeclass_instances` database.

**Note:** There is an implicit coercion from `code` to `raw_code`.

### Packages

#### Package construction

We have a notion of `raw_package` which is a collection of procedures of the
form `src → raw_code tgt` distinguished by their signatures. This notion of
`raw_package` will prove the most efficient when proving results about packages,
such as advantages.
However, we provide a syntax to define valid packages by construction, *i.e.*
of type `package I E` where each procedure must be `ValidCode L I tgt` for a
a chosen set of locations `L` and the lot of them must implement export interface `E`.

The syntax for valid packages is similar to that of interfaces. Better explained
on an example:

```coq
Definition test :
  package
    [interface
      val #[0] : 'nat → 'bool ;
      val #[1] : 'bool → 'unit
    ]
    [interface
      val #[2] : 'nat → 'nat ;
      val #[3] : 'bool × 'bool → 'bool
    ]
  :=
  [package emptym ;
    def #[2] (n : 'nat) : 'nat {
      #import {sig #[0] : 'nat → 'bool } as f ;;
      #import {sig #[1] : 'bool → 'unit } as g ;;
      b ← f n ;;
      if b then
        g false ;;
        ret 0
      else ret n
    } ;
    def #[3] ('(b₀,b₁) : 'bool × 'bool) : 'bool {
      ret b₀
    }
  ].
```

Packages are wrapped in the `[package]` container which behaves like lists.
They are of the form
```coq
[package L ; d₀ ; d₁ ; … ; dₙ ]
```
where `L` is the locations of the package` and `dᵢ` are declarations, given
using a special syntax:
```coq
def #[ id ] (x : src) : tgt { e }
```
where `id` is a natural number / identifier, and `src` and `tgt` are codes of
types in `choice_type` given using the special syntax (see [Specialised types]),
while `e` is a regular Coq expression corresponding to the body of the function,
with `x` bound inside it.
As seen in the example, `x` can be matched against in the declaration by using
the `'p` notation where `p` is a pattern.

Similarly to `ValidCode`, there is an underlying `ValidPackage` class and we can
call its best effort version with `ssprove_valid`, for instance using
`Equations` (see [Valid code]).

In the example above we also explicitly gave an export interface while the
information is already present in the declaration. As such in can be omitted
as on the simpler example below:
```coq
Definition test' : package [interface] _ :=
  [package emptym ;
    def #[ 0 ] (n : 'nat) : 'nat {
      ret (n + n)%N
    } ;
    def #[ 1 ] (b : 'bool) : 'nat {
      if b then ret 0 else ret 13
    }
  ].
```
The locations and import interface should however be given explicitly since
they are what the programs *can* use, not what they *exactly* use.

#### Composition of packages

One of the key points of SSP is its package algebra with sequential and parallel
composition as well as the identity package. All these operations are defined on
`raw_packages` directly but extend to `package` with the `{package}` notation.

Sequential composition is called `link` in SSProve and can be written
`p₀ ∘ p₁`. It represents `p₀` where all *imports* are replaced by the inlined
procedures of `p₁`. It is valid when the import interface of `p₀` is a subset
of the export interface of `p₁` and when the sets of locations are compatible
(given by `fcompat`, which is usually derived automatically).

Parallel composition of (raw) packages `p₀` and `p₁` is written `par p₀ p₁`.
It is valid if we have `fseparate p₀ p₁` and compatible sets of locations both
of which are usually automatic.

Finally, the identity package is defined as `ID I` where `I` is an interface.
It both imports and exports `I` by simply forwarding the calls and is valid
for any interface `I`.

As illustrated above, `{package p }` casts a raw package to some
`package I E`, trying to infer the proof.

**Note:** `package` has an implicit coercion to
`raw_package`. This means that, for instance, if `p₀` and `p₁` are both
`package` then, `{package p₀ ∘ p₁ }` is a valid expression, and will be complete
if the interfaces match.

**Note:** When using `Equations`, please `Set Equations Transparent` such
that code simplification in proofs via `ssprove_code_simpl` resolves properly.

## High-level SSP proofs

To reason at the high-level of state-separating proofs, we have two main
options.
The first one is the package algebra which involves laws on sequential and
parallel composition as well as on the identity package.
The second is when talking about advantage and corresponds mainly to the
triangle inequality and the reduction lemma.

Most of those apply to `raw_package` directly, but some will still have
some extra conditions which might be validity of some bits.

### Package algebra

The algebraic laws on packages are expressed as equalities (using Coq's equality
type `=`) on `raw_package`.

#### Associativity of sequential composition / linking

```coq
Lemma link_assoc :
  ∀ p₁ p₂ p₃,
    p₁ ∘ (p₂ ∘ p₃) = (p₁ ∘ p₂) ∘ p₃.
```

#### Commutativity of parallel composition

```coq
Lemma par_commut :
  ∀ p1 p2,
    fseparate p1 p2 →
    par p1 p2 = par p2 p1.
```

#### Associativity of parallel composition

```coq
Lemma par_assoc :
  ∀ p1 p2 p3,
    par p1 (par p2 p3) = par (par p1 p2) p3.
```

#### Identity law

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

#### Interchange between sequential and parallel composition

```coq
Lemma interchange :
  ∀ A B C D E F L₁ L₂ L₃ L₄ p₁ p₂ p₃ p₄,
    ValidPackage L₁ B A p₁ →
    ValidPackage L₂ E D p₂ →
    ValidPackage L₃ C B p₃ →
    ValidPackage L₄ F E p₄ →
    fseparate p₃ p₄ →
    par (p₁ ∘ p₃) (p₂ ∘ p₄) = (par p₁ p₂) ∘ (par p₃ p₄).
```
The last line can be read as
```
(p₁ ∘ p₃) || (p₂ ∘ p₄) = (p₁ || p₂) ∘ (p₃ || p₄)
```

### Adversarial advantage

Security theorems in SSP will often conclude on an inequality of advantages.
We offer several ways to reason about them, but first we will show how to even
state such theorems.

#### Advantage and games

The simplest notion of advantage we have is `AdvantageE` of the following type
```coq
AdvantageE (G₀ G₁ A : raw_package) : R
```
`G₀` and `G₁` are the packages compared by the distinguisher/adversary `A`.
The result is a real number, of type `R`.

We also have an alternative version simply style `Advantage` which takes in a
pair of games as a function `bool → raw_package`:

```coq
Advantage (G : bool → raw_package) (A : raw_package) : R
```

The two definitions are equivalent, as stated by the following. `AdvantageE`
should be preferred as it is slightly less constrained.
```coq
Lemma Advantage_E :
  ∀ (G : bool → raw_package) A,
    Advantage G A = AdvantageE (G false) (G true) A.
```

We have several useful lemmas on advantage. We will list the important ones
below.

```coq
Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
```
This one corresponds to the **reduction lemma** and is very useful.

```coq
Lemma Advantage_sym :
  ∀ P Q A,
    AdvantageE P Q A = AdvantageE Q P A.
```

```coq
Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
```
The **triangle inequality** is also very useful when reasoning about advantage.
As such we provide the user with an n-ary version of it which allows the user
to simulate game-hopping, in the form of a convenient tactic.

```coq
ssprove triangle p₀ [:: p₁ ; p₂ ; p₃ ] p₄ A as ineq.
```
will produce an inequality
```coq
ineq :
  AdvantageE p₀ p₄ A <= AdvantageE p₀ p₁ A +
                        AdvantageE p₁ p₂ A +
                        AdvantageE p₂ p₃ A +
                        AdvantageE p₃ p₄ A
```

#### Perfect indistinguishability

When the advantage of an adversary `A` (with disjoint state) against a game pair
`(G₀, G₁)` is `0`, we say that `G₀` and `G₁` are perfectly indistinguishable
and we write `G₀ ≈₀ G₁`.
Because this definition needs to talk about state, it can only apply to valid
packages. This notation indeed implicitly asks for the following:
```coq
ValidPackage L₀ Game_import E G₀
ValidPackage L₁ Game_import E G₁
```
for some `L₀`, `L₁` and `E`.
It is equivalent to the following:

```coq
∀ LA A,
  ValidPackage LA E A_export A →
  fseparate LA L₀ →
  fseparate LA L₁ →
  AdvantageE G₀ G₁ A = 0.
```
So one can use `G₀ ≈₀ G₁` to rewrite an advantage to `0`, typically after using
the triangle inequality, to eliminate some terms.
*Herein `A_export` is the export interface of an adversary, it contains a single
procedure `RUN` of type `'unit → 'bool`.*


## Probabilistic relational program logic

To prove perfect indistinguishability of two packages, we propose a low-level
probabilistic relational Hoare logic. We first show how to prove a statement
of the form `P ≈₀ Q` and then how to reason in this program logic.

### Proving perfect indistinguishability

The lemma of interest here is the following:
```coq
Lemma eq_rel_perf_ind :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package) (inv : precond)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    Invariant L₀ L₁ inv →
    eq_up_to_inv E inv p₀ p₁ →
    p₀ ≈₀ p₁.
```
Most conditions are for `p₀ ≈₀ p₁` to even make sense. The important part is
that to prove `p₀ ≈₀ p₁` it suffices to prove that their procedures are related
in our program logic, while preserving an invariant `inv`.
An invariant relates the two heaps (state) used by `p₀` and `p₁` respectively.
The simplest example of invariant simply state equality of the two:
```coq
λ '(s₀, s₁), s₀ = s₁
```
To use it, one case use the following special case.
```coq
Corollary eq_rel_perf_ind_eq :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    eq_up_to_inv E (λ '(h₀, h₁), h₀ = h₁) p₀ p₁ →
    p₀ ≈₀ p₁.
```
We will say more about invariants later in [[Crafting invariants]].

Once this lemma is applied, we need to simplify the `eq_up_to_inv` expression.
We have a set of tactics that help us achieve that automatically.

```coq
eapply eq_rel_perf_ind_eq.
simplify_eq_rel x. (* x is a name *)
all: ssprove_code_simpl.
```

`simplify_eq_rel x` will turn `eq_upto_inv` into one goal for each procedure,
`x` being the name for the argument in each case.
The goals it returns can be quite massive, with typically linking that is not
reduced (not inlined).
For each sub-goal (hence the goal selector `all:`), we apply the
`ssprove_code_simpl` tactic which we will describe in the next section.

### Massaging relational judgments

A relational goal obtained after `simplify_eq_rel` will be of the form
```coq
⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄
```
where `pre` is a precondition, `post` a postcondition, and `c₀` and `c₁` are
both raw code.
As stated above, the expressions `c₀` and `c₁` may not be in their best shape.
For instance, linking might be stuck because of a `match` expression.

**`ssprove_code_simpl`** will simplify such a goal by traversing both `c₀` and
`c₁` and performing simplifications such as commutation of linking with `match`,
or associativity of `bind`. In some rare cases, two applications of this tactic
might be necessary. While it performs most possible simplifications, it only
works syntactically.

**`ssprove_code_simpl_more`** on the other hand will operate semantically,
exploiting the fact that we are proving a relational judgment. One of the main
points of it is that it can deal with associativity of `#assert`.

`ssprove_code_simpl` is actually extensible by adding hints to the
`ssprove_code_simpl` database.
Consider for instance the following extension:
```coq
Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme
  : ssprove_code_simpl.
```
The hints must be able to solve goals where the left-hand side is an evar and
the right-hand side is the expression to simplify.
Here we state that whenever the expression to simplify is `code_link` we can
rewrite using `code_link_scheme` before continuing the simplification.

The lemma in question is
```coq
Lemma code_link_scheme :
  ∀ A c p,
    @ValidCode emptym [interface] A c →
    code_link c p = c.
```
stating that code which does not import anything (here we add the unnecessary
requirement that it must be state-less as well) remains unchanged after linking.

### Proving relational judgments

Now that our goal is pretty enough to read, we can try and prove it. For this
a lot of rules are introduced in the `pkg_rhl` module (which you import simply
by importing `Package`). Not all of them are useful for the user experience,
some are simply used to prove other ones.

We will present the most important ones as well as tactics that can help apply
certain rules.

#### Synchronous rules

The most basic tactic deals with judgment with the same first instruction on
both sides, for instance
```coq
⊢ ⦃ pre ⦄ x ← sample D ;; k₀ x ≈ x ← sample D ;; k₁ x ⦃ post ⦄
```
Applying the `ssprove_sync` tactic will reduce the goal to
```coq
∀ x, ⊢ ⦃ pre ⦄ k₀ x ≈ k₁ x ⦃ post ⦄
```

In the case of sampling there is no extra requirement, but when the first
operation is a `get` or a `put`, there is *a priori* no guarantee that the
precondition `pre` will be preserved. `ssprove_sync` will try to solve this
extra condition on its own but will ask the user for it if it doesn't manage.
To solve it, it calls the extensible `ssprove_invariant` tactic that we will
see in [[Crafting invariants]].

There is also a more specialised tactic **`ssprove_sync_eq`** which solves the
same problem when the precondition is equality: `λ '(s₀, s₁), s₀ = s₁`. This one
never generates extra conditions.

#### Bind

Sometimes, the head is not a command stem, but a `bind`. In this case we have
the `r_bind` rule. It is also more general than the above in that the two
head expression can differ, provided they are still related.
```coq
Lemma r_bind :
  ∀ {A₀ A₁ B₀ B₁ : ord_choiceType} m₀ m₁ f₀ f₁
    (pre : precond) (mid : postcond A₀ A₁) (post : postcond B₀ B₁),
    ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ mid ⦄ →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₀, s₁), mid (a₀, s₀) (a₁, s₁) ⦄ f₀ a₀ ≈ f₁ a₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ bind m₀ f₀ ≈ bind m₁ f₁ ⦃ post ⦄.
```

#### Return

The tactics above only apply when the code has a head command, this excludes
programs like `ret t`. To deal with them, we have the specialised `r_ret` rule.

```coq
Lemma r_ret :
  ∀ {A₀ A₁ : ord_choiceType} u₀ u₁ (pre : precond) (post : postcond A₀ A₁),
    (∀ s₀ s₁, pre (s₀, s₁) → post (u₀, s₀) (u₁, s₁)) →
    ⊢ ⦃ pre ⦄ ret u₀ ≈ ret u₁ ⦃ post ⦄.
```

#### Swapping

Sometimes, two expressions are similar but don't have the same head symbol.
In this case, it might prove useful to *swap* commands.
Say we have the following goal:
```coq
⊢ ⦃ pre ⦄ x ← sample D ;; y ← get ℓ ;; r₀ x y ≈ c₁ ⦃ post ⦄
```
then applying `ssprove_swap_lhs 0%N` will leave us to prove
```coq
⊢ ⦃ pre ⦄ y ← get ℓ ;; x ← sample D ;; r₀ x y ≈ c₁ ⦃ post ⦄
```
instead.

However, not any two commands are swappable. The tactic will try to infer the
swappability condition automatically, this is the case for sampling which can
always be swapped (if dependencies permit), or for `get`/`put` when they talk
about distinct locations. If automation proves insufficient, the user will have
to provide the proof themselves. There is also the option of enriching the
`ssprove_swap` database, as in the example below.

```coq
Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
  eapply r_swap_scheme_cmd ; ssprove_valid
  : ssprove_swap.
```
Here we provide a hint to swap a bind with a regular command (`get`, `sample`
or `put`), in the case where the program that we bind is a scheme, *i.e.* a
stateless, import-less program:
```coq
Lemma r_swap_scheme_cmd :
  ∀ {A B : choiceType} (s : raw_code A) (c : command B),
    ValidCode emptym [interface] s →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      x ← s ;; y ← cmd c ;; ret (x,y) ≈
      y ← cmd c ;; x ← s ;; ret (x,y)
    ⦃ eq ⦄.
```

The tactics we provide are
* `ssprove_swap_lhs n` for swapping in the left-hand side at depth `n`;
* `ssprove_swap_rhs n` for swapping in the right-hand side;
* `ssprove_swap_seq_lhs s` for swapping in the lhs using a sequence `s` of
swapping instructions given as a list of natural numbers;
* `ssprove_swap_seq_rhs s` for the same in the rhs.

#### Reflexivity rule

We have a very simple reflexivity rule in the case where the invariant is
equality:
```coq
Lemma rreflexivity_rule :
  ∀ {A : ord_choiceType} (c : raw_code A),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ eq ⦄.
```

In case the invariant is not equality, there is still a reflexivity rule, but
it is more constrained:
```coq
Lemma r_reflexivity_alt :
  ∀ {A : choiceType} {L} pre (c : raw_code A),
    ValidCode L [interface] c →
    (∀ ℓ, fhas L ℓ → get_pre_cond ℓ pre) →
    (∀ ℓ v, fhas L ℓ → put_pre_cond ℓ v pre) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      c ≈ c
    ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
```
Validity can be handled with `ssprove_valid` and the other `get_pre_cond`
and `put_pre_cond` are goals dealt with `ssprove_invariant`.

#### Dealing with memory

There are ways to deal with memory is an asynchronous way. We tried to make it
as idiomatic as possible.

#### Reading or writing twice

When faced with the goal
```coq
⊢ ⦃ pre ⦄ x ← get ℓ ;; r₀ x ≈ x ← get ℓ ;; r₁ x ⦃ post ⦄
```
one can use `ssprove_sync` to introduce the `x` and continue proving equivalence
between `r₀` and `r₁`. The information that `x` comes from location `ℓ` however
is lost.

The first solution to this problem comes from *contraction rules*, or rather
tactics.

**`ssprove_contract_get_lhs`** will take a goal of the form
```coq
⊢ ⦃ pre ⦄ x ← get ℓ ;; y ← get ℓ ;; r₀ x y ≈ c₁ ⦃ post ⦄
```
and turn it into
```coq
⊢ ⦃ pre ⦄ x ← get ℓ ;; r₀ x x ≈ c₁ ⦃ post ⦄
```


**`ssprove_contract_put_lhs`** will take a goal of the form
```coq
⊢ ⦃ pre ⦄ put ℓ := v ;; put ℓ := v' ;; c₀ ≈ c₁ ⦃ post ⦄
```
and turn it into
```coq
⊢ ⦃ pre ⦄ put ℓ := v' ;; c₀ ≈ c₁ ⦃ post ⦄
```


**`ssprove_contract_put_get_lhs`** will take a goal of the form
```coq
⊢ ⦃ pre ⦄ put ℓ := v ;; x ← get ℓ ;; r₀ x ≈ c₁ ⦃ post ⦄
```
and turn it into
```coq
⊢ ⦃ pre ⦄ put ℓ := v ;; r₀ v ≈ c₁ ⦃ post ⦄
```

**`ssprove_contract_get_rhs`**, **`ssprove_contract_put_rhs`** and
**`ssprove_contract_put_get_rhs`** are their right-hand side counterparts.

#### Remember after reading

Sometimes, swapping and contracting is not possible, even when the code makes
two reads to the same location. It can happen for instance if the value read
is branched upon before being read again.

For this we have several rules that will *remember* which location was read.
```coq
Lemma r_get_remember_lhs :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ x) (s₀, s₁) ⦄ r₀ x ≈ r₁ ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ x ← get ℓ ;; r₀ x ≈ r₁ ⦃ post ⦄.
```
It behaves like you would expect an asynchronous rule for `get` except that the
precondition gets extended with `rem_lhs ℓ x` stating that the location `ℓ`
contained value `x` on the left-hand side.
In this fashion we have `r_get_remember_rhs` which will add `rem_rhs ℓ x`
instead, but also synchronous rules that will also remember, for instance
```coq
Lemma r_get_vs_get_remember_lhs
  {A B : choiceType} {ℓ r₀ r₁} {pre : precond} {post : postcond A B}
    `{ht : ProvenBy (syncs ℓ) pre} :
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ x) (s₀, s₁) ⦄
        r₀ x ≈ r₁ x
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← get ℓ ;; r₀ x ≈
      x ← get ℓ ;; r₁ x
    ⦃ post ⦄.
```

Here we have an additional `ProvenBy (syncs ℓ) pre` condition which states that
`ℓ` should point to the same value on both sides (or more precisely that this
should be ensured by the precondition `pre`). `exact _` (type-class inference)
should deal with it.

We also have the right-hand side variant `r_get_vs_get_remember_rhs`
and the do-all rule `r_get_vs_get_remember` which remembers on both sides.

Now, that we have stored information in the precondition, we have several ways
of using it, or discarding it. Indeed, this precondition will not always be
preserved by rules, in particular writing memory (`put`) does not necessarily
preserve `rem_lhs`/`rem_rhs`. As such, one can call `ssprove_forget` to discard
the most recent *remember*, and `ssprove_forget_all` will discard all of them.

More importantly, one can make use of remembered values with, for instance,
the following rule
```coq
Lemma r_get_remind_lhs
  {A B : choiceType} {ℓ v r₀ r₁} {pre : precond} {post : postcond A B}
    `{hr : ProvenBy (rem_lhs ℓ v) pre} :
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ v ≈ r₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ x ← get ℓ ;; r₀ x ≈ r₁ ⦃ post ⦄.
```
Here `ProvenBy` is also a class that can be inferred using `exact _`.
It checks that `pre` contains `rem_lhs ℓ v` in any place.
The right-hand side counterpart is `r_get_remind_rhs`.
In some cases, one has remembered the value of something on the left, and needs
it on the right, in which case the following lemma is useful:
```coq
Lemma Remembers_syncs :
  ∀ s ℓ v pre,
    ProvenBy (rem_inv (other s) ℓ v) pre →
    ProvenBy (syncs ℓ) pre →
    ProvenBy (rem_inv s ℓ v) pre.
```
The lemma can switch between `rem_lhs` and `rem_rhs` given that the invariant
`pre` also guarantees that the specific location is `synced` i.e. that its
heap value is the same on both sides.

We will see later, in [[Crafting invariants]], how we can also leverage these
*remembered* values with invariants.

#### Invariant debts after writing

Dually to how we *remember* read values, we propose a way to write to a memory
location, even when it might temporarily break the invariant. As we will see in
[[Crafting invariants]], a lot of invariants will involve several locations at
once, meaning the most of the time, writing a value will break them.
Thus, our machinery to write to the memory freely and then, at the user's
command, to restore the invariant.

These debts to the precondition are incurred by using one of the following
rules.
```coq
Lemma r_put_lhs :
  ∀ {A B : choiceType} ℓ v r₀ r₁ (pre : precond) (post : postcond A B),
    ⊢ ⦃ λ '(s₀, s₁), (set_lhs ℓ v pre) (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ put ℓ := v ;; r₀ ≈ r₁ ⦃ post ⦄.
```
or its rhs counterpart `r_put_rhs`. We can deal with a `put` on both sides
with `r_put_vs_put`.

Now we either have `set_lhs` or `set_rhs` *around* our invariant. This means
that temporarily we cannot remember read values or use the invariant as it
might no longer hold. Once we believe that the invariant has been restored,
we can use one of the two tactics `ssprove_restore_pre` and
`ssprove_restore_mem`.

**`ssprove_restore_pre`** is the simplest and typically applies to a goal where
the precondition has been *hidden* by several `set_lhs`/`set_rhs`. Under the
hood it applies the rule
```coq
Lemma r_restore_pre :
  ∀ {A B : choiceType} l r₀ r₁ (pre : precond) (post : postcond A B),
    preserve_update_pre l pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), (update_pre l pre) (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄.
```
So it will restore `pre` as a precondition, assuming that the predicate
`preserve_update_pre` holds. Automation in this case is also performed with
`ssprove_invariant`. It might not solve all goals, but should generally give
you goals about the specific invariants that you used.

**Note** that if your precondition contains some `rem_lhs`/`rem_rhs`, you will
have to prove that those are preserved too. This will not be the case if you
have written to those very memory locations. In which case, it is recommended
to use the following tactic instead.

**`ssprove_restore_mem`** is similar but will also take into account the
remembered read values. Under the hood it applies the rule
```coq
Lemma r_restore_mem :
  ∀ {A B : choiceType} l m r₀ r₁ (pre : precond) (post : postcond A B),
    preserve_update_mem l m pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), (update_pre l (remember_pre m pre)) (s₀, s₁) ⦄
      r₀ ≈ r₁
    ⦃ post ⦄.
```
The predicate `preserve_update_mem` generalises the one above (in fact
`preserve_update_pre` is defined using the empty list for the remembered
values, this means that automation is shared between the two).
This can be very useful because it essentially means that you can use the
assumptions you have on initial memory to restore the invariant.

The predicate is defined as
```coq
Definition preserve_update_mem l m (pre : precond) :=
  ∀ s₀ s₁, (remember_pre m pre) (s₀, s₁) → pre (update_heaps l s₀ s₁).
```

Note that restoring the invariant with this method will forget all assumptions
you had on memory, only the proper invariant will remain.
Feel free to [open an issue] if you would need something stronger.

### Crafting invariants

#### Proper invariants

As already stated, the easiest to use invariant is equality of heaps. The fact
that it is an invariant is summarised in the lemma below:
```coq
Lemma Invariant_eq :
  ∀ L₀ L₁,
    Invariant L₀ L₁ (λ '(s₀, s₁), s₀ = s₁).
```
where `L₀` and `L₁` represent the sets of memory locations of both programs.
While it can be enough for a lot of examples (our own examples mostly use
equality as an invariant), it is not always sufficient.

Another invariant we propose is called `heap_ignore` and is defined as
```coq
Definition heap_ignore (L : Locations) :=
  λ '(h₀, h₁),
    ∀ (ℓ : Location), ℓ.1 \notin domm L → get_heap h₀ ℓ = get_heap h₁ ℓ.
```
It only states equality of heaps on locations that are not in `L`, the set of
*ignored* locations. It is a valid invariant as long as the ignored locations
are contained in the program location (in other words, one cannot ignore the
locations of the adversary).
```coq
Lemma Invariant_heap_ignore :
  ∀ L L₀ L₁,
    fsubmap L (unionm L₀ L₁) →
    Invariant L₀ L₁ (heap_ignore L).
```

The two above are considered proper invariants, or support of an invariant,
because they conclude on the whole heaps. However, invariants will often need
to conclude about specific locations, like saying that two locations store
values that are related in some way.
For this purpose, we define a notion of *semi-invariant* (short of a better
name) which do not conclude about the heaps globally but only about parts of it.
Proper invariants (like `heap_ignore`) can then be combined with semi-invariants
to produce new proper invariants; we do this with the notation `inv ⋊ sinv`
which is a sort of fancy notation for conjunction.
```coq
Lemma Invariant_inv_conj :
  ∀ L₀ L₁ inv sinv,
    Invariant L₀ L₁ inv →
    SemiInvariant L₀ L₁ sinv →
    Invariant L₀ L₁ (inv ⋊ sinv).
```
A semi-invariant isn't as restrictive as an invariant.
Note that we already used this notion in [[Proving relational judgments]]
when talking about `rem_lhs`/`rem_rhs` which are semi-invariants.

**Note:** Using `ssprove_invariant` is the recommended way for deriving
automatically these properties. This tactic can be extended by adding hints
to the `ssprove_invariant` database.

We will now review the already defined semi-invariants.

#### Location coupling

One semi-invariant that we provide is `couple_lhs`:
```coq
Definition couple_lhs ℓ ℓ' R : precond :=
  λ '(s₀, s₁), R (get_heap s₀ ℓ) (get_heap s₀ ℓ').
```
`couple_lhs ℓ ℓ' R` states that the values stored in locations `ℓ` and `ℓ'`
of the lhs are related by relation `R`. It is a semi-invariant when the
locations belong to the left-hand side package.

Now, to make use of this invariant, one can use the following tactic:
```coq
ssprove_rem_rel n
```
where `n` is the position of the coupling counted from the right/back of
the whole invariant. The tactic will utilize remembered and sycronized values
that are also part of the invariant. It gives you the same goal you had
with an additional hypothesis, which states that the relation holds for
the remembered values.

`couple_lhs` is just one of the semi-invariant provided. Others include:
* `single_lhs l`. A predicate about the value of `l` on the LHS.
* `single_rhs l`. A predicate about the value of `l` on the RHS.
* `couple_lhs l l'`. As explained.
* `couple_rhs l l'`. A relation about the values of `l` and `l'` on the RHS.
* `couple_cross l l'`. A relation about the values of `l` on the LHS and `l'`
    on the RHS.
* `triple_lhs l l' l''`. A relation about the values of `l`, `l'` and `l''`
    on the LHS.
* `triple_rhs l l' l''`. A relation about the values of `l`, `l'` and `l''`
    on the RHS.

It is also possible to define additional location couplings using any finite
combination of locations from either side with `rel_app`.


[Writing packages]: #writing-packages
[Raw code]: #raw-code
[Specialised types]: #specialised-types
[Distributions]: #distributions
[Valid code]: #valid-code
[Packages]: #packages
[High-level SSP proofs]: #high-level-ssp-proofs
[Package algebra]: #package-algebra
[Adversarial advantage]: #adversarial-advantage
[Probabilistic relational program logic]: #probabilistic-relational-program-logic
[Proving perfect indistinguishability]: #proving-perfect-indistinguishability
[Massaging relational judgments]: #massaging-relational-judgments
[Proving relational judgments]: #proving-relational-judgments
[Crafting invariants]: #crafting-invariants

[extructures]: https://github.com/arthuraa/extructures

[open an issue]: https://github.com/SSProve/ssprove/issues
