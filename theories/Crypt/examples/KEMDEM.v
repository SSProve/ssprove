(** KEM-DEM example

  In this example, we follow the original SSP paper available at:
  https://eprint.iacr.org/2018/306

  In this file we first define the KEY pacakges and prove the single key lemma
  of the SSP paper. We then proceed to define the KEM-DEM packages and proving
  its security relative to that of the KEM and the DEM.
*)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

Section KEMDEM.

  (** We open a section in order to make local changes to global settings
      in the unlikely event that this module is imported somewhere else.
  *)
  Set Equations Transparent.

  (** In the SSP paper, bitstrings are used for the different data types.
      Instead we go for a more abstract types.
      In the cases where we need to be able to sample on these data types,
      we will first assume we have a (lossless) sub-distribution, and then
      define the types as the domain of these sub-distributions.
  *)

  (** Symmetric key *)
  Context (keyD : Op).
  Definition chKey := keyD.π1.

  (** Public and secret key *)
  Context (chPKey chSKey : choice_type).

  (** Plain text *)
  Context (chPlain : choice_type).

  (** We additionally require a "zero" in chPlain.

    Note that we don't require any structure on chPlain so this "zero" is only
    a "zero" in name a priori. Can be thought of as the 0 bitstring.
  *)
  Context (nullPlain : chPlain).

  (** Encrypted key

    This corresponds to the type of symmetric keys once encrypted.
  *)
  Context (ekeyD : Op).
  Definition chEKey := ekeyD.π1.

  (** Cipher text *)
  Context (cipherD : Op).
  Definition chCipher := cipherD.π1.

  (** Type notations *)

  Notation "'key" := (chKey) (in custom pack_type at level 2).
  Notation "'key" := (chKey) (at level 2) : package_scope.

  Notation "'pkey" := (chPKey) (in custom pack_type at level 2).
  Notation "'pkey" := (chPKey) (at level 2) : package_scope.

  Notation "'skey" := (chSKey) (in custom pack_type at level 2).
  Notation "'skey" := (chSKey) (at level 2) : package_scope.

  Notation "'plain" := (chPlain) (in custom pack_type at level 2).
  Notation "'plain" := (chPlain) (at level 2) : package_scope.

  Notation "'ekey" := (chEKey) (in custom pack_type at level 2).
  Notation "'ekey" := (chEKey) (at level 2) : package_scope.

  Notation "'cipher" := (chCipher) (in custom pack_type at level 2).
  Notation "'cipher" := (chCipher) (at level 2) : package_scope.

  (** Procedure names

    Under the hood, procedures are identified by natural numbers so we abstract
    them away by using distrinct coq-level identifiers.
  *)

  (* KEY *)
  Definition GEN := 0%N.
  Definition SET := 1%N.
  Definition GET := 2%N.

  (* KEM-CCA *)
  Definition KEMGEN := 6%N.
  Definition ENCAP := 7%N.
  Definition DECAP := 8%N.

  (* DEM-CCA *)
  Definition ENC := 9%N.
  Definition DEC := 10%N.

  (* PKE-CCA / MOD-CCA *)
  Definition PKGEN := 3%N.
  Definition PKENC := 4%N.
  Definition PKDEC := 5%N.

  (** Memory locations *)
  Definition k_loc : Location := (0, 'option 'key).
  Definition pk_loc : Location := (1, 'option 'pkey).
  Definition sk_loc : Location := (2, 'option 'skey).
  Definition ek_loc : Location := (3, 'option 'ekey).
  Definition c_loc : Location := (4, 'option 'cipher).

  (** Some shorthands *)
  Definition IGEN := [interface #val #[ GEN ] : 'unit → 'unit ].
  Definition ISET := [interface #val #[ SET ] : 'key → 'unit ].
  Definition IGET := [interface #val #[ GET ] : 'unit → 'key ].

  (** PKE scheme

    A public-key encryption scheme comes with a key generation (a public and
    private key pair) and an encryption procedures (in the sense that they can
    use effects, typically sampling for the key generation procedure). It also
    comes with a pure (in particular deterministric) decryption function.
    The purity is denoted by the abscence of [code] in the return type.
  *)

  Record PKE_scheme := {
    PKE_kgen : code emptym [interface] (chProd 'pkey 'skey) ;
    PKE_enc : 'pkey → 'plain → code emptym [interface] (chProd 'ekey 'cipher) ;
    PKE_dec : 'skey → chProd 'ekey 'cipher → 'plain
  }.

  (** KEM scheme

    A key encapsulation mechanism comes with a key generation
    (public/private pair) and an encapsulation procedures as well as with a
    pure / deterministic decapsulation function.
  *)

  Record KEM_scheme := {
    KEM_kgen : code emptym [interface] (chProd 'pkey 'skey) ;
    KEM_encap : 'pkey → code emptym [interface] (chProd 'key 'ekey) ;
    KEM_decap : 'skey → 'ekey → 'key
  }.

  (** DEM scheme

    A data encapsulation mechanism comes with deterministric pure encryption
    and decryption functions. Both use a symmetric key.
  *)

  Record DEM_scheme := {
    DEM_enc : 'key → 'plain → 'cipher ;
    DEM_dec : 'key → 'cipher → 'plain
  }.

  (** We assume we are given a KEM and DEM schemes. *)
  Context (η : KEM_scheme).
  Context (θ : DEM_scheme).

  (** Specification of assumed schemes

    We assume the existence of a relation capturing which public key corresponds
    to which secret key. We furthermore require KEM_kgen to ensure that the
    keys it generates verify this relation.

    We use this relation to state the correctness of KEM_encap.

    The [⊢ₛ _ ⦃ _ ⦄] notation corresponds to unary specifications with only a
    post-condition on the result. They correspond to the diagonal of relational
    specifications, with the addition that state must be preserved.
  *)

  Context (pkey_pair : (chProd 'pkey 'skey) → Prop).
  Context (KEM_kgen_spec : ⊢ₛ η.(KEM_kgen) ⦃ pkey_pair ⦄).

  Definition encap_spec (pk : 'pkey) (kek : chProd 'key 'ekey) : Prop :=
    ∀ sk, pkey_pair (pk, sk) → η.(KEM_decap) sk kek.2 = kek.1.

  Context (KEM_encap_spec : ∀ pk, ⊢ₛ η.(KEM_encap) pk ⦃ encap_spec pk ⦄).

  (** KEY package *)

  (** The KEY package will only use one location: [k_loc] corresponding the
    stored key.
  *)
  Definition KEY_loc :=
    [fmap k_loc ].

  (** Similarly, we define the export / output interface of the KEY package.

    The KEY package can generate a key [GEN] and then store its result in the
    location [k_loc] or alternatively it can set [SET] a key provided by the
    caller, finally in can return the stored key using [GET].
  *)
  Definition KEY_out :=
    [interface
      #val #[ GEN ] : 'unit → 'unit ;
      #val #[ SET ] : 'key → 'unit ;
      #val #[ GET ] : 'unit → 'key
    ].

  (** Definition of the KEY package *)
  Definition KEY : package KEY_loc [interface] KEY_out :=
    [package
      #def #[ GEN ] (_ : 'unit) : 'unit {
        k ← get k_loc ;;
        #assert (k == None) ;;
        k ← sample keyD ;;
        #put k_loc := Some k ;;
        @ret 'unit Datatypes.tt
      } ;
      #def #[ SET ] (k : 'key) : 'unit {
        k' ← get k_loc ;;
        #assert (k' == None) ;;
        #put k_loc := Some k ;;
        @ret 'unit Datatypes.tt
      } ;
      #def #[ GET ] (_ : 'unit) : 'key {
        k ← get k_loc ;;
        #assert (isSome k) as kSome ;;
        @ret 'key (getSome k kSome)
      }
    ].

  (** KEM package *)

  (** The KEM pacakge can refer to locations corresponding to a public and
    private asymetric keys, and to an encrypted symmetric key.
  *)
  Definition KEM_loc := [fmap pk_loc ; sk_loc ; ek_loc ].

  (** The KEM packaee is parametrised by a boolean [b] depedning on which
    its import interface differs. If [b] is [true] it will be able to call
    the [SET] procedure, and if [b] is [false] it will be able to call the
    [GEN] one. In the paper [KEM true] corresponds to KEM⁰, while [KEM false]
    corresponds to KEM¹.
  *)
  Definition KEM_in b :=
    if b then ISET else IGEN.

  (** The KEM package will export a public and private key generation procedure
    [KEMGEM] that only returns the public one, an ecapsulation procedure [ENCAP]
    which will generate and encrypt a symmetric key, and a decpasulation
    procedure [DECAP] which returns a symmetric key given its encryption.
  *)
  Definition KEM_out :=
    [interface
      #val #[ KEMGEN ] : 'unit → 'pkey ;
      #val #[ ENCAP ] : 'unit → 'ekey ;
      #val #[ DECAP ] : 'ekey → 'key
    ].

  (** Here we add a hint to the [ssprove_valid_db] and [typeclass_instances]
    databases. The former database corresponds to what is used by the
    [ssprove_valid] tactic, while the latter corresponds to the built-in
    database used by type-class inference.
    This means that when Coq will have to prove the validity of a scheme, it
    will try to make use of the [valid_scheme] lemma that is a special case
    when the code does not import anything or use any state.
  *)
  Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
    eapply valid_scheme ; eapply c.(prog_valid)
    : typeclass_instances ssprove_valid_db.

  Definition KEM (b : bool) : package KEM_loc (KEM_in b) KEM_out :=
    [package
      #def #[ KEMGEN ] (_ : 'unit) : 'pkey {
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← η.(KEM_kgen) ;;
        #put pk_loc := Some pk ;;
        #put sk_loc := Some sk ;;
        @ret 'pkey pk
      } ;
      #def #[ ENCAP ] (_ : 'unit) : 'ekey {
        #import {sig #[ SET ] : 'key → 'unit } as SET ;;
        #import {sig #[ GEN ] : 'unit → 'unit } as GEN ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        '(k, ek) ← η.(KEM_encap) pk ;;
        #put ek_loc := Some ek ;;
        (if b then SET k else GEN Datatypes.tt) ;;
        ret ek
      } ;
      #def #[ DECAP ] (ek' : 'ekey) : 'key {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        #assert (ek != Some ek') ;;
        ret (η.(KEM_decap) sk ek')
      }
    ].

  (** KEM-CCA game

    The KEM-CCA game is obtained by composing the KEM and KEY packages, as well
    as the identity package. A game pair is described using a boolean-indexed
    function. Here, the only part that changes is the KEM package which is
    already indexed by a boolean.

    KEM-CCAᵇ = (KEMᵇ || ID) ∘ KEY
  *)

  Definition KEM_CCA_out :=
    [interface
      #val #[ KEMGEN ] : 'unit → 'pkey ;
      #val #[ ENCAP ] : 'unit → 'ekey ;
      #val #[ DECAP ] : 'ekey → 'key ;
      #val #[GET] : 'unit → 'key
    ].

  Definition KEM_CCA_loc :=
    unionm KEM_loc KEY_loc.

  (** Here we use Equations to generate a goal corresponding to the validity of
    the composed package as it is not inferred automatically.
    We call [ssprove_valid] which progresses as much as possible and then asks
    us to prove the remanining bits.

    Here and afterwards we use #[tactic=notac] to tell Equations not to
    preprocess the generated goals.
  *)
  #[tactic=ssprove_valid] Equations? KEM_CCA_pkg b :
    package KEM_CCA_loc [interface] KEM_CCA_out :=
    KEM_CCA_pkg b :=
    {package (par (KEM b) (ID IGET)) ∘ KEY }.  Proof.
    1,2: destruct b; fmap_solve.
  Qed.

  (** We finally package the above into a game pair. *)
  Definition KEM_CCA : loc_GamePair KEM_CCA_out :=
    λ b, {locpackage KEM_CCA_pkg b }.

  (** DEM package *)

  (** The DEM package only stores a cipher. *)
  Definition DEM_loc := [fmap c_loc ].

  (** The DEM package can refer to the [GET] procedure. *)
  Definition DEM_in := IGET.

  (** The DEM package, produced from the DEM scheme θ, exports an encryption
    and a decryption procedures.
  *)
  Definition DEM_out :=
    [interface
      #val #[ ENC ] : 'plain → 'cipher ;
      #val #[ DEC ] : 'cipher → 'plain
    ].

  Definition DEM (b : bool) : package DEM_loc DEM_in DEM_out :=
    [package
      #def #[ ENC ] (m : 'plain) : 'cipher {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get c_loc ;;
        #assert (c == None) ;;
        k ← GET Datatypes.tt ;;
        let c := θ.(DEM_enc) k (if b then m else nullPlain) in
        #put c_loc := Some c ;;
        ret c
      } ;
      #def #[ DEC ] (c' : 'cipher) : 'plain {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get c_loc ;;
        #assert (c != Some c') ;;
        k ← GET Datatypes.tt ;;
        ret (θ.(DEM_dec) k c')
      }
    ].

  (** DEM-CCA game

    The DEM-CCA game is obtained by composing the DEM and KEY packages, as
    well as the indentity package.

    DEM-CCAᵇ = (DEMᵇ || ID) ∘ KEY
  *)

  Definition DEM_CCA_out :=
    [interface
      #val #[ GEN ] : 'unit → 'unit ;
      #val #[ ENC ] : 'plain → 'cipher ;
      #val #[ DEC ] : 'cipher → 'plain
    ].

  Definition DEM_CCA_loc :=
    unionm DEM_loc KEY_loc.

  #[tactic=ssprove_valid] Equations DEM_CCA_pkg (b : bool) :
    package DEM_CCA_loc [interface] DEM_CCA_out :=
    DEM_CCA_pkg b :=
    {package (par (DEM b) (ID IGEN)) ∘ KEY }.

  Definition DEM_CCA : loc_GamePair DEM_CCA_out :=
    λ b, {locpackage DEM_CCA_pkg b }.

  (** PKE-CCA *)

  Definition PKE_CCA_loc := [fmap pk_loc ; sk_loc ; c_loc ; ek_loc ].

  Definition PKE_CCA_out :=
    [interface
      #val #[ PKGEN ] : 'unit → 'pkey ;
      #val #[ PKENC ] : 'plain → 'ekey × 'cipher ;
      #val #[ PKDEC ] : 'ekey × 'cipher → 'plain
    ].

  Definition PKE_CCA_pkg (ζ : PKE_scheme) b :
    package PKE_CCA_loc [interface] PKE_CCA_out :=
    [package
      #def #[ PKGEN ] (_ : 'unit) : 'pkey {
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← ζ.(PKE_kgen) ;;
        #put pk_loc := Some pk ;;
        #put sk_loc := Some sk ;;
        @ret 'pkey pk
      } ;
      #def #[ PKENC ] (m : 'plain) : 'ekey × 'cipher {
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        c ← get c_loc ;;
        #assert (c == None) ;;
        '(ek, c) ← ζ.(PKE_enc) pk (if b then m else nullPlain) ;;
        #put ek_loc := Some ek ;;
        #put c_loc := Some c ;;
        @ret (chProd 'ekey 'cipher) (ek, c)
      } ;
      #def #[ PKDEC ] (c' : 'ekey × 'cipher) : 'plain {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        c ← get c_loc ;;
        #assert ((ek, c) != (Some c'.1, Some c'.2)) ;;
        ret (ζ.(PKE_dec) sk c')
      }
    ].

  Definition PKE_CCA (ζ : PKE_scheme) : loc_GamePair PKE_CCA_out :=
    λ b, {locpackage PKE_CCA_pkg ζ b }.

  (** MOD-CCA *)

  Definition MOD_CCA_loc :=
    [fmap pk_loc ; c_loc ; ek_loc ].

  Definition MOD_CCA_in :=
    [interface
      #val #[ KEMGEN ] : 'unit → 'pkey ;
      #val #[ ENCAP ] : 'unit → 'ekey ;
      #val #[ DECAP ] : 'ekey → 'key ;
      #val #[ ENC ] : 'plain → 'cipher ;
      #val #[ DEC ] : 'cipher → 'plain
    ].

  Definition MOD_CCA_out :=
    PKE_CCA_out.

  Definition MOD_CCA (ζ : PKE_scheme) :
    package MOD_CCA_loc MOD_CCA_in MOD_CCA_out :=
    [package
      #def #[ PKGEN ] (_ : 'unit) : 'pkey {
        #import {sig #[ KEMGEN ] : 'unit → 'pkey } as KEMGEN ;;
        pk ← get pk_loc ;;
        #assert (pk == None) ;;
        KEMGEN Datatypes.tt
      } ;
      #def #[ PKENC ] (m : 'plain) : 'ekey × 'cipher {
        #import {sig #[ ENCAP ] : 'unit → 'ekey } as ENCAP ;;
        #import {sig #[ ENC ] : 'plain → 'cipher } as ENC ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        c ← get c_loc ;;
        #assert (c ==  None) ;;
        ek ← ENCAP Datatypes.tt ;;
        #put ek_loc := Some ek ;;
        c ← ENC m ;;
        #put c_loc := Some c ;;
        @ret (chProd 'ekey 'cipher) (ek, c)
      } ;
      #def #[ PKDEC ] ('(ek', c') : 'ekey × 'cipher) : 'plain {
        #import {sig #[ DECAP ] : 'ekey → 'key } as DECAP ;;
        #import {sig #[ DEC ] : 'cipher → 'plain } as DEC ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_loc ;;
        c ← get c_loc ;;
        #assert ((ek, c) != (Some ek', Some c')) ;;
        if ek == Some ek'
        then (
          DEC c'
        )
        else (
          k' ← DECAP ek' ;;
          ret (θ.(DEM_dec) k' c')
        )
      }
    ].

  (** PKE scheme instance *)
  Definition KEM_DEM : PKE_scheme := {|
    PKE_kgen := η.(KEM_kgen) ;
    PKE_enc := λ pk m, {code
      '(k, ek) ← η.(KEM_encap) pk ;;
      let c := θ.(DEM_enc) k m in
      ret (ek, c)
    } ;
    PKE_dec := λ sk c,
      let '(ek, c) := c in
      let k := η.(KEM_decap) sk ek in
      θ.(DEM_dec) k c
  |}.

  (** Single key lemma *)

  (** Corresponds to Lemma 19.a in the SSP paper *)
  Lemma single_key_a :
    ∀ LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID IGET)) ∘ KEY in
      let K₁ := (par CK₁ (ID IGET)) ∘ KEY in
      let D₀ := (par (ID IGEN) CD₀) ∘ KEY in
      let D₁ := (par (ID IGEN) CD₁) ∘ KEY in
      Parable CK₀ (ID IGET) →
      Parable CK₁ (ID IGET) →
      Parable (ID IGEN) CD₀ →
      Parable (ID IGEN) CD₁ →
      ValidPackage LD₀ IGET ED CD₀ →
      ValidPackage LD₀ IGET ED CD₁ →
      trimmed ED CD₀ →
      trimmed ED CD₁ →
      ValidPackage LK₀ ISET EK CK₀ →
      ValidPackage LK₀ IGEN EK CK₁ →
      trimmed EK CK₀ →
      trimmed EK CK₁ →
      AdvantageE ((par CK₀ CD₀) ∘ KEY) ((par CK₁ CD₁) ∘ KEY) A <=
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₀)) +
      AdvantageE D₀ D₁ (A ∘ (par CK₁ (ID ED))).
  Proof.
    intros LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A K₀ K₁ D₀ D₁.
    intros pCK₀ pCK₁ pCD₀ pCD₁ hCD₀ hCD₁ tCD₀ tCD₁ hCK₀ hCK₁ tCK₀ tCK₁.
    ssprove triangle (par CK₀ CD₀ ∘ KEY) [::
      par CK₁ CD₀ ∘ KEY
    ] (par CK₁ CD₁ ∘ KEY) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    eapply lerD.
    (* Idealising the core keying package *)
    - replace (par CK₀ CD₀) with ((par (ID EK) CD₀) ∘ (par CK₀ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      replace (par CK₁ CD₀) with ((par (ID EK) CD₀) ∘ (par CK₁ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      rewrite Advantage_link.
      unfold K₀, K₁.
      rewrite !link_assoc.
      apply lexx.
    (* Idealising the core keyed package *)
    - replace (par CK₁ CD₀) with ((par CK₁ (ID ED)) ∘ (par (ID IGEN) CD₀)).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      replace (par CK₁ CD₁) with ((par CK₁ (ID ED)) ∘ (par (ID IGEN) CD₁)).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      rewrite Advantage_link.
      unfold D₀, D₁.
      rewrite !link_assoc.
      apply lexx.
  Qed.

  (** Corresponds to Lemma 19.b in the SSP paper *)
  Lemma single_key_b :
    ∀ LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID IGET)) ∘ KEY in
      let K₁ := (par CK₁ (ID IGET)) ∘ KEY in
      let D₀ := (par (ID IGEN) CD₀) ∘ KEY in
      let D₁ := (par (ID IGEN) CD₁) ∘ KEY in
      Parable CK₀ (ID IGET) →
      Parable CK₁ (ID IGET) →
      Parable (ID IGEN) CD₀ →
      Parable (ID IGEN) CD₁ →
      ValidPackage LD₀ IGET ED CD₀ →
      ValidPackage LD₀ IGET ED CD₁ →
      trimmed ED CD₀ →
      trimmed ED CD₁ →
      ValidPackage LK₀ ISET EK CK₀ →
      ValidPackage LK₀ IGEN EK CK₁ →
      trimmed EK CK₀ →
      trimmed EK CK₁ →
      AdvantageE ((par CK₀ CD₀) ∘ KEY) ((par CK₀ CD₁) ∘ KEY) A <=
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₀)) +
      AdvantageE D₀ D₁ (A ∘ (par CK₁ (ID ED))) +
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₁)).
  Proof.
    intros LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A K₀ K₁ D₀ D₁.
    intros pCK₀ pCK₁ pCD₀ pCD₁ hCD₀ hCD₁ tCD₀ tCD₁ hCK₀ hCK₁ tCK₀ tCK₁.
    ssprove triangle (par CK₀ CD₀ ∘ KEY) [::
      par CK₁ CD₁ ∘ KEY
    ] (par CK₀ CD₁ ∘ KEY) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    eapply lerD.
    - eapply single_key_a. all: eauto.
    (* De-idealising the core keying package *)
    - replace (par CK₀ CD₁) with ((par (ID EK) CD₁) ∘ (par CK₀ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      replace (par CK₁ CD₁) with ((par (ID EK) CD₁) ∘ (par CK₁ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: ssprove_valid.
        2: apply trimmed_ID.
        rewrite link_id. all: eauto.
        rewrite id_link. all: eauto.
      }
      rewrite Advantage_link.
      unfold K₀, K₁.
      rewrite !link_assoc.
      rewrite Advantage_sym.
      apply lexx.
  Qed.

  (** Perfect indistinguishability with PKE-CCA

    We show that the package given by
    MOD_CCA KEM_DEM ∘ (KEM⁰ || DEMᵇ) ∘ KEY
    and which we call [Aux b], is perfectly indistinguishable from
    [PKE_CCA KEM_DEM b], which is the PKE-CCA game instantiated with the
    KEM-DEM instance we have.
  *)

  Definition Aux_loc :=
    unionm MOD_CCA_loc (unionm KEM_loc (unionm DEM_loc KEY_loc)).

  #[tactic=ssprove_valid] Equations Aux (b : bool)
    : package Aux_loc [interface] PKE_CCA_out :=
    Aux b :=
    {package (MOD_CCA KEM_DEM ∘ par (KEM true) (DEM b) ∘ KEY) }.

  (** We extend ssprove_code_simpl to use code_link_scheme.
    It says that linking a scheme with anything results in the scheme itself
    as a scheme does not import anything.
  *)
  Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  (** We extend swapping to schemes.
    This means that the ssprove_swap tactic will be able to swap any command
    with a scheme without asking a proof from the user.
  *)
  Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
    eapply r_swap_scheme_cmd ; ssprove_valid
    : ssprove_swap.

  (** Program equivalences

    In order to prove these equivalences, we will use an invariant that
    dismisses any changes made to the symmetric key location as it is only
    modified in one of the packages. This will be the [heap_ignore KEY_loc] bit
    in the following [inv] invariant.
    We need to extend this invariant with knowlegde about how the contents of
    some locations are related.
    With [triple_rhs pk_loc k_loc ek_loc PKE_inv] we say that the values
    corresponding to the public key, symmetric key and the encrypted symmetric
    key are always related by [PKE_inv] (described below).
    Similarly, [couple_lhs pk_loc sk_loc (sameSomeRel PkeyPair)] relates the
    public and secret keys by the relation [sameSomeRel PkeyPair]. It states
    that both must be [None], or both must be [Some pk] and [Some sk] such
    that [pk] and [sk] are related by [PkeyPair pk sk].
  *)

  (** This rephrasing of [pkey_pair] simply states that the stored public
    and private keys are indeed part of the same key pair, according to the
    specification of the KEM.
  *)
  Definition PkeyPair :=
    λ (pk : 'pkey) (sk : 'skey), pkey_pair (pk, sk).

  (** This states two things:
    - [k] and [ek] must both be set ([Some]) or unset ([None]);
    - whenever they are set, then the public key [pk] must as well and the three
    should be related by the functional specification [encap_spec] stating that
    [ek] is indeed the encryption of [k] using public key [pk].
  *)
  Definition PKE_inv (pk : 'option 'pkey) (k : 'option 'key) (ek : 'option 'ekey) :=
    match pk, k, ek with
    | Some pk, Some k, Some ek => encap_spec pk (k, ek)
    | Some pk, None, None => True
    | None, None, None => True
    | _, _, _ => False
    end.

  Notation inv := (
    heap_ignore KEY_loc ⋊
    triple_rhs pk_loc k_loc ek_loc PKE_inv ⋊
    couple_lhs pk_loc sk_loc (sameSomeRel PkeyPair)
  ).

  (** We have to show that [inv] is a valid invariant and while the
    [ssprove_invariant] does most of the work for us we still have some
    properties regarding the sets involved to prove
    (otherwise type inference would have solved it).
  *)
  Instance Invariant_inv : Invariant PKE_CCA_loc Aux_loc inv.
  Proof.
    ssprove_invariant.
    all: try fmap_solve.
    1,2: simpl; auto.
  Qed.

  (** We show perfect equivalence in the general case where [b] stay abstract.
    This spares us the burden of proving roughly the same equivalence twice.
  *)
  Lemma PKE_CCA_perf :
    ∀ b, (PKE_CCA KEM_DEM b) ≈₀ Aux b.
  Proof.
    intro b.
    unfold Aux.
    (* We go to the relational logic with our invariant. *)
    eapply eq_rel_perf_ind with (inv := inv). 1: exact _.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    (* We are now in the realm of program logic *)
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro sk.
      ssprove_sync. intro skNone.
      eapply r_get_remember_rhs. intro pk.
      eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
      1:{ eapply Remembers_lhs_from_tracked_rhs. all: ssprove_invariant. }
      intro eps. destruct sk. 1: discriminate.
      destruct pk. 1: contradiction. simpl.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk' sk'] pps.
      eapply r_put_vs_put.
      eapply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        - intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
          destruct hh as [[[hi ?] ?] e]. simpl in *.
          rewrite e in hi. get_heap_simpl.
          destruct (get_heap s₁ k_loc), (get_heap s₁ ek_loc).
          all: try contradiction.
          auto.
        - auto.
      }
      apply r_ret. auto.
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro pk.
      ssprove_sync. intro pkSome.
      destruct pk as [pk|]. 2: discriminate.
      simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro ek.
      ssprove_sync. intro ekNone.
      rewrite ekNone. simpl.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
      ssprove_sync. intro cNone.
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_remind_rhs. 1: exact _.
      rewrite cNone. simpl. ssprove_forget.
      ssprove_swap_seq_rhs [:: 0 ]%N.
      eapply r_get_remember_rhs. intros k.
      eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
      destruct ek. 1: discriminate.
      destruct k. 1: contradiction.
      simpl.
      ssprove_swap_seq_rhs [:: 0 ; 1 ]%N.
      ssprove_contract_put_get_rhs. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_swap_seq_lhs [:: 0 ]%N.
      ssprove_sync.
      apply r_put_rhs.
      apply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
        destruct hh as [[[[[hi ?] epk] ?] ?] ?]. simpl in *.
        get_heap_simpl.
        rewrite epk. simpl. auto.
      }
      apply r_ret. auto.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intros ek.
      destruct (ek == Some ek') eqn:eek.
      + rewrite eek.
        ssprove_code_simpl_more. ssprove_code_simpl. ssprove_code_simpl_more.
        eapply r_get_remember_rhs. intro pk.
        eapply r_get_remember_lhs. intro sk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          eapply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        eapply sameSomeRel_sameSome in eps as eps'. rewrite eps'.
        ssprove_sync. intro skSome.
        ssprove_swap_seq_rhs [:: 1 ]%N.
        ssprove_contract_get_rhs.
        ssprove_sync. intro c.
        ssprove_sync. intro neq.
        move: neq => /eqP neq.
        move: eek => /eqP eek. subst ek.
        destruct (c != Some c') eqn:e.
        2:{ move: e => /eqP e. subst. contradiction. }
        rewrite e. simpl.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
        destruct sk as [sk|]. 2: discriminate.
        destruct pk as [pk|]. 2: contradiction.
        destruct k as [k|]. 2: contradiction.
        simpl. simpl in hpke. simpl in eps. unfold PkeyPair in eps.
        eapply hpke in eps as h. simpl in h. subst.
        ssprove_forget_all.
        apply r_ret. auto.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        eapply r_get_remind_rhs. 1: exact _.
        ssprove_forget.
        ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
        apply r_get_vs_get_remember. 1: ssprove_invariant. intros sk.
        apply r_get_remember_rhs. intro pk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{ apply Remembers_lhs_from_tracked_rhs. all: ssprove_invariant. }
        intro eps. eapply sameSomeRel_sameSome in eps as eps'. rewrite eps'.
        ssprove_forget_all.
        ssprove_sync. intro skSome.
        ssprove_sync. intro c.
        ssprove_sync. intro ee.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        rewrite eek. simpl.
        apply r_ret. auto.
  Qed.

  Corollary PKE_CCA_perf_true :
    (Aux true) ≈₀ (PKE_CCA KEM_DEM true).
  Proof.
    apply adv_equiv_sym. apply PKE_CCA_perf.
  Qed.

  (** Security theorem *)

  Theorem PKE_security :
    ∀ LA A,
      ValidPackage LA PKE_CCA_out A_export A →
      domm LA :#: domm PKE_CCA_loc →
      domm LA :#: domm Aux_loc → (* Do we really need this? *)
      Advantage (PKE_CCA KEM_DEM) A <=
      Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM true)) +
      Advantage DEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (KEM false) (ID DEM_out)) +
      Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM false)).
  Proof.
    intros LA A hA hA' hd.
    rewrite Advantage_E.
    ssprove triangle (PKE_CCA KEM_DEM false) [::
      (MOD_CCA KEM_DEM) ∘ par (KEM true) (DEM false) ∘ KEY ;
      (MOD_CCA KEM_DEM) ∘ par (KEM true) (DEM true) ∘ KEY
    ] (PKE_CCA KEM_DEM true) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    rewrite PKE_CCA_perf. 2,3: auto.
    rewrite PKE_CCA_perf_true. 2,3: auto.
    rewrite GRing.addr0. rewrite GRing.add0r.
    (* Now we massage the expression to apply the single key lemma *)
    eapply le_trans.
    - rewrite Advantage_sym.
      rewrite -Advantage_link.
      eapply single_key_b with (CK₁ := (KEM false).(pack)).
      all: ssprove_valid.
      1-4: repeat apply trimmed_package_cons.
      1-4: apply trimmed_empty_package.
    - rewrite !Advantage_E.
      unfold KEM_CCA. unfold KEM_CCA_pkg.
      unfold DEM_CCA. unfold DEM_CCA_pkg.
      change ({locpackage ?p }.(pack)) with p.
      change ({package ?p }.(pack)) with p.
      apply eq_ler. rewrite !link_assoc. f_equal.
      all: rewrite Advantage_sym. 2: reflexivity.
      f_equal. rewrite Advantage_sym.
      f_equal. all: f_equal.
      all: apply par_commut.
      all: rewrite /Parable domm_ID.
      1,2: fmap_solve.
  Qed.

End KEMDEM.
