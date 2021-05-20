(** KEM-DEM example

  From the original SSP paper https://eprint.iacr.org/2018/306*

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
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
Import mc_1_10.Num.Theory.

Import PackageNotation.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

(* TODO MOVE *)
Lemma eq_ler :
  ∀ (x y : R),
    x = y →
    x <= y.
Proof.
  intros x y e. subst. apply lerr.
Qed.

Section KEMDEM.

  (** As we are in a section, we can safely kill the obligation tactic.
      It will restored after we leave the section.
  *)
  Obligation Tactic := idtac.
  Set Equations Transparent.

  (** In the SSP paper, bitstrings are used.
      Instead we go for a more abstract types.
      In the cases where we need to be able to sample on these data types,
      we will instead assume we have a lossless distribution, as they come
      with their domain.
  *)

  (** Symmetric key *)
  Context keyD `{LosslessOp keyD}.
  Definition chKey := keyD.π1.

  (** Public and secret key  *)
  Context (chPKey chSKey : chUniverse).

  (** Plain text *)
  Context (chPlain : chUniverse).

  (** We additionally require a "zero" in chPlain *)
  Context (nullPlain : chPlain).

  (** Ecrypted key *)
  Context (ekeyD : Op).
  Definition chEKey := ekeyD.π1.

  (** Cipher text *)
  Context (cipherD : Op).
  Definition chCipher := cipherD.π1.

  (** Types *)
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

  (** Procedure names *)

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
  Definition k_loc : Location := ('option 'key ; 0%N).
  Definition pk_loc : Location := ('option 'pkey ; 1%N).
  Definition sk_loc : Location := ('option 'skey ; 2%N).
  Definition ek_loc : Location := ('option 'ekey ; 3%N).
  Definition c_loc : Location := ('option 'cipher ; 4%N).

  (** Some shorthands *)
  Definition IGEN := [interface val #[ GEN ] : 'unit → 'unit ].
  Definition ISET := [interface val #[ SET ] : 'key → 'unit ].
  Definition IGET := [interface val #[GET] : 'unit → 'key ].

  (** PKE scheme *)

  Record PKE_scheme := {
    PKE_kgen : code fset0 [interface] (chProd 'pkey 'skey) ;
    PKE_enc : 'pkey → 'plain → code fset0 [interface] (chProd 'ekey 'cipher) ;
    PKE_dec : 'skey → chProd 'ekey 'cipher → code fset0 [interface] 'plain (* det if KEM_decap and DEM_dec *)
  }.

  (** KEM scheme *)

  Record KEM_scheme := {
    KEM_kgen : code fset0 [interface] (chProd 'pkey 'skey) ;
    KEM_encap : 'pkey → code fset0 [interface] (chProd 'key 'ekey) ;
    KEM_decap : 'skey → 'ekey → 'key
  }.

  (** DEM scheme *)

  Record DEM_scheme := {
    DEM_enc : 'key → 'plain → code fset0 [interface] 'cipher ; (* det *)
    DEM_dec : 'key → 'cipher → code fset0 [interface] 'plain (* det? *)
  }.

  Context (η : KEM_scheme).
  Context (θ : DEM_scheme).

  (** Specification of assumed schemes

    We assume the existence of a relation capturing which public key correspond
    to which secret key. We furthermore require KEM_kgen to ensure that the
    keys it generates verify this relation.

    We use this relation to state the correctness of KEM_encap.

  *)

  Context (pkey_pair : (chProd 'pkey 'skey) → Prop).
  Context (KEM_kgen_spec : ⊢ₛ η.(KEM_kgen) ⦃ pkey_pair ⦄).

  Definition encap_spec (pk : 'pkey) (kek : chProd 'key 'ekey) : Prop :=
    ∀ sk, pkey_pair (pk, sk) → η.(KEM_decap) sk kek.2 = kek.1.

  Context (KEM_encap_spec : ∀ pk, ⊢ₛ η.(KEM_encap) pk ⦃ encap_spec pk ⦄).

  (** KEY package *)

  Definition KEY_loc :=
    fset [:: k_loc ].

  Definition KEY_out :=
    [interface
      val #[ GEN ] : 'unit → 'unit ;
      val #[ SET ] : 'key → 'unit ;
      val #[ GET ] : 'unit → 'key
    ].

  Definition KEY : package KEY_loc [interface] KEY_out :=
    [package
      def #[ GEN ] (_ : 'unit) : 'unit {
        k ← get k_loc ;;
        #assert (k == None) ;;
        k ← sample keyD ;;
        put k_loc := Some k ;;
        @ret 'unit Datatypes.tt
      } ;
      def #[ SET ] (k : 'key) : 'unit {
        k' ← get k_loc ;;
        #assert (k' == None) ;;
        put k_loc := Some k ;;
        @ret 'unit Datatypes.tt
      } ;
      def #[ GET ] (_ : 'unit) : 'key {
        k ← get k_loc ;;
        #assert (isSome k) as kSome ;;
        @ret 'key (getSome k kSome)
      }
    ].

  (** KEM package *)

  Definition KEM_loc := fset [:: pk_loc ; sk_loc ; ek_loc ].

  Definition KEM_in b :=
    if b then ISET else IGEN.

  Definition KEM_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'pkey ;
      val #[ ENCAP ] : 'unit → 'ekey ;
      val #[ DECAP ] : 'ekey → 'key
    ].

  Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
    eapply valid_scheme ; eapply c.(prog_valid)
    : typeclass_instances packages.

  Definition KEM (b : bool) : package KEM_loc (KEM_in b) KEM_out :=
    [package
      def #[ KEMGEN ] (_ : 'unit) : 'pkey {
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← η.(KEM_kgen) ;;
        put pk_loc := Some pk ;;
        put sk_loc := Some sk ;;
        @ret 'pkey pk
      } ;
      def #[ ENCAP ] (_ : 'unit) : 'ekey {
        #import {sig #[ SET ] : 'key → 'unit } as SET ;;
        #import {sig #[ GEN ] : 'unit → 'unit } as GEN ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        '(k, ek) ← η.(KEM_encap) pk ;;
        put ek_loc := Some ek ;;
        (if b then SET k else GEN Datatypes.tt) ;;
        ret ek
      } ;
      def #[ DECAP ] (ek' : 'ekey) : 'key {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        #assert (isSome ek) as ekSome ;;
        let ek := getSome ek ekSome in
        #assert (ek != ek') ;;
        ret (η.(KEM_decap) sk ek')
      }
    ].

  (** KEM-CCA game *)

  Definition KEM_CCA_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'pkey ;
      val #[ ENCAP ] : 'unit → 'ekey ;
      val #[ DECAP ] : 'ekey → 'key ;
      val #[GET] : 'unit → 'key
    ].

  (* Maybe inline? *)
  Definition KEM_CCA_loc :=
    KEM_loc :|: KEY_loc.

  Equations? KEM_CCA_pkg b :
    package KEM_CCA_loc [interface] KEM_CCA_out :=
    KEM_CCA_pkg b :=
    {package (par (KEM b) (ID IGET)) ∘ KEY }.
  Proof.
    ssprove_valid.
    - (* Maybe we can automate this better *)
      apply/fdisjointP.
      intros n h.
      rewrite domm_mkfmap in h. simpl in h.
      rewrite domm_ID_fset. rewrite in_fset. simpl.
      invert_in_seq h.
      all: reflexivity.
    - erewrite fsetU0. apply fsubsetxx.
    - destruct b.
      all: unfold KEM_in.
      all: unfold ISET, IGET.
      all: rewrite -fset_cat. all: simpl.
      + apply /fsubsetP. simpl.
        intros n h. rewrite in_fset. rewrite in_fset in h.
        invert_in_seq h.
        * rewrite in_cons. apply/orP. right. rewrite in_cons.
          apply/orP. left. apply eqxx.
        * rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. right.
          rewrite mem_seq1. apply eqxx.
      + apply /fsubsetP. simpl.
        intros n h. rewrite in_fset. rewrite in_fset in h.
        invert_in_seq h.
        * rewrite in_cons. apply/orP. left. apply eqxx.
        * rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. right.
          rewrite mem_seq1. apply eqxx.
    - unfold KEM_CCA_out. rewrite -fset_cat. simpl.
      apply fsubsetxx.
    - apply fsubsetUl.
    - apply fsubsetUr.
  Qed.

  Definition KEM_CCA : loc_GamePair KEM_CCA_out :=
    λ b, {locpackage KEM_CCA_pkg b }.

  (** DEM package *)

  Definition DEM_loc := fset [:: c_loc ].

  Definition DEM_in := IGET.

  Definition DEM_out :=
    [interface
      val #[ ENC ] : 'plain → 'cipher ;
      val #[ DEC ] : 'cipher → 'plain
    ].

  Definition DEM (b : bool) : package DEM_loc DEM_in DEM_out :=
    [package
      def #[ ENC ] (m : 'plain) : 'cipher {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get c_loc ;;
        #assert (c == None) ;;
        k ← GET Datatypes.tt ;;
        c ← θ.(DEM_enc) k (if b then m else nullPlain) ;;
        put c_loc := Some c ;;
        ret c
      } ;
      def #[ DEC ] (c' : 'cipher) : 'plain {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get c_loc ;;
        #assert (isSome c) as cSome ;;
        let c := getSome c cSome in
        #assert (c != c') ;;
        k ← GET Datatypes.tt ;;
        θ.(DEM_dec) k c'
      }
    ].

  (** DEM-CCA game *)

  Definition DEM_CCA_out :=
    [interface
      val #[ GEN ] : 'unit → 'unit ;
      val #[ ENC ] : 'plain → 'cipher ;
      val #[ DEC ] : 'cipher → 'plain
    ].

  (* Maybe inline? *)
  Definition DEM_CCA_loc :=
    DEM_loc :|: KEY_loc.

  Equations? DEM_CCA_pkg b :
    package DEM_CCA_loc [interface] DEM_CCA_out :=
    DEM_CCA_pkg b :=
    {package (par (DEM b) (ID IGEN)) ∘ KEY }.
  Proof.
    ssprove_valid.
    - (* Maybe we can automate this better *)
      apply/fdisjointP.
      intros n h.
      rewrite domm_mkfmap in h. simpl in h.
      rewrite domm_ID_fset. rewrite in_fset. simpl.
      invert_in_seq h.
      all: reflexivity.
    - erewrite fsetU0. apply fsubsetxx.
    - apply/fsubsetP.
      rewrite -fset_cat. simpl.
      unfold KEY_out.
      intros n h. rewrite in_fset. rewrite in_fset in h.
      invert_in_seq h.
      + rewrite in_cons. apply/orP. right.
        rewrite in_cons. apply/orP. right.
        rewrite in_cons. apply/orP. left.
        apply eqxx.
      + rewrite in_cons. apply/orP. left.
        apply eqxx.
    - unfold DEM_CCA_out, IGEN.
      rewrite fsetUC.
      rewrite -fset_cat. simpl.
      apply fsubsetxx.
    - apply fsubsetUl.
    - apply fsubsetUr.
  Qed.

  Definition DEM_CCA : loc_GamePair DEM_CCA_out :=
    λ b, {locpackage DEM_CCA_pkg b }.

  (** PKE-CCA *)

  Definition PKE_CCA_loc := fset [:: pk_loc ; sk_loc ; c_loc ; ek_loc ].

  Definition PKE_CCA_out :=
    [interface
      val #[ PKGEN ] : 'unit → 'pkey ;
      val #[ PKENC ] : 'plain → 'ekey × 'cipher ;
      val #[ PKDEC ] : 'ekey × 'cipher → 'plain
    ].

  Definition PKE_CCA_pkg (ζ : PKE_scheme) b :
    package PKE_CCA_loc [interface] PKE_CCA_out :=
    [package
      def #[ PKGEN ] (_ : 'unit) : 'pkey {
        (** In the original SSP paper, there is only a check that the location
            sk_loc is empty, for simplicity, we check also that pk_loc is empty.
            TODO: Prove it since we have an invariant for this.
        *)
        pk ← get pk_loc ;;
        #assert (pk == None) ;;
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← ζ.(PKE_kgen) ;;
        put pk_loc := Some pk ;;
        put sk_loc := Some sk ;;
        @ret 'pkey pk
      } ;
      def #[ PKENC ] (m : 'plain) : 'ekey × 'cipher {
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        c ← get c_loc ;;
        #assert (c == None) ;;
        '(ek, c) ← ζ.(PKE_enc) pk (if b then m else nullPlain) ;;
        put ek_loc := Some ek ;;
        put c_loc := Some c ;;
        @ret (chProd 'ekey 'cipher) (ek, c)
      } ;
      def #[ PKDEC ] (c' : 'ekey × 'cipher) : 'plain {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        #assert (isSome ek) as ekSome ;;
        let ek := getSome ek ekSome in
        c ← get c_loc ;;
        #assert (isSome c) as cSome ;;
        let c := getSome c cSome in
        #assert ((ek, c) != c') ;;
        ζ.(PKE_dec) sk c'
      }
    ].

  Definition PKE_CCA (ζ : PKE_scheme) : loc_GamePair PKE_CCA_out :=
    λ b, {locpackage PKE_CCA_pkg ζ b }.

  (** MOD-CCA *)

  Definition MOD_CCA_loc :=
    fset [:: pk_loc ; c_loc ; ek_loc ].

  Definition MOD_CCA_in :=
    [interface
      val #[ KEMGEN ] : 'unit → 'pkey ;
      val #[ ENCAP ] : 'unit → 'ekey ;
      val #[ DECAP ] : 'ekey → 'key ;
      val #[ ENC ] : 'plain → 'cipher ;
      val #[ DEC ] : 'cipher → 'plain
    ].

  Definition MOD_CCA_out :=
    PKE_CCA_out.

  Definition MOD_CCA (ζ : PKE_scheme) :
    package MOD_CCA_loc MOD_CCA_in MOD_CCA_out :=
    [package
      def #[ PKGEN ] (_ : 'unit) : 'pkey {
        #import {sig #[ KEMGEN ] : 'unit → 'pkey } as KEMGEN ;;
        pk ← get pk_loc ;;
        #assert (pk == None) ;;
        KEMGEN Datatypes.tt
      } ;
      def #[ PKENC ] (m : 'plain) : 'ekey × 'cipher {
        #import {sig #[ ENCAP ] : 'unit → 'ekey } as ENCAP ;;
        #import {sig #[ ENC ] : 'plain → 'cipher } as ENC ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        c ← get c_loc ;;
        #assert (c ==  None) ;;
        ek ← ENCAP Datatypes.tt ;;
        put ek_loc := Some ek ;;
        c ← ENC m ;;
        put c_loc := Some c ;;
        @ret (chProd 'ekey 'cipher) (ek, c)
      } ;
      def #[ PKDEC ] ('(ek', c') : 'ekey × 'cipher) : 'plain {
        #import {sig #[ DECAP ] : 'ekey → 'key } as DECAP ;;
        #import {sig #[ DEC ] : 'cipher → 'plain } as DEC ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_loc ;;
        #assert (isSome ek) as ekSome ;;
        let ek := getSome ek ekSome in
        c ← get c_loc ;;
        #assert (isSome c) as cSome ;;
        let c := getSome c cSome in
        #assert ((ek, c) != (ek', c')) ;;
        if ek == ek'
        then (
          DEC c'
        )
        else (
          k' ← DECAP ek' ;;
          θ.(DEM_dec) k' c'
        )
      }
    ].

  (** PKE scheme instance *)
  Definition KEM_DEM : PKE_scheme := {|
    PKE_kgen := η.(KEM_kgen) ;
    PKE_enc := λ pk m, {code
      '(k, ek) ← η.(KEM_encap) pk ;;
      c ← θ.(DEM_enc) k m ;;
      ret (ek, c)
    } ;
    PKE_dec := λ sk c, {code
      let '(ek, c) := c in
      let k := η.(KEM_decap) sk ek in
      θ.(DEM_dec) k c
    }
  |}.

  (** Single key lemma *)

  (* Corresponds to Lemma 19.a in the SSP paper *)
  Lemma single_key_a :
    ∀ LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID IGET)) ∘ KEY in
      let K₁ := (par CK₁ (ID IGET)) ∘ KEY in
      let D₀ := (par (ID IGEN) CD₀) ∘ KEY in
      let D₁ := (par (ID IGEN) CD₁) ∘ KEY in
      flat EK →
      flat ED →
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
    intros fEK fED pCK₀ pCK₁ pCD₀ pCD₁ hCD₀ hCD₁ tCD₀ tCD₁ hCK₀ hCK₁ tCK₀ tCK₁.
    ssprove triangle (par CK₀ CD₀ ∘ KEY) [::
      par CK₁ CD₀ ∘ KEY
    ] (par CK₁ CD₁ ∘ KEY) A
    as ineq.
    eapply ler_trans. 1: exact ineq.
    clear ineq.
    eapply ler_add.
    (* Idealising the core keying package *)
    - replace (par CK₀ CD₀) with ((par (ID EK) CD₀) ∘ (par CK₀ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      replace (par CK₁ CD₀) with ((par (ID EK) CD₀) ∘ (par CK₁ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      rewrite Advantage_link.
      unfold K₀, K₁.
      rewrite !link_assoc.
      apply lerr.
    (* Idealising the core keyed package *)
    - replace (par CK₁ CD₀) with ((par CK₁ (ID ED)) ∘ (par (ID IGEN) CD₀)).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      replace (par CK₁ CD₁) with ((par CK₁ (ID ED)) ∘ (par (ID IGEN) CD₁)).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      rewrite Advantage_link.
      unfold D₀, D₁.
      rewrite !link_assoc.
      apply lerr.
    Unshelve. all: exact fset0.
  Qed.

  (* Corresponds to Lemma 19.b in the SSP paper *)
  Lemma single_key_b :
    ∀ LD₀ LK₀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID IGET)) ∘ KEY in
      let K₁ := (par CK₁ (ID IGET)) ∘ KEY in
      let D₀ := (par (ID IGEN) CD₀) ∘ KEY in
      let D₁ := (par (ID IGEN) CD₁) ∘ KEY in
      flat EK →
      flat ED →
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
    intros fEK fED pCK₀ pCK₁ pCD₀ pCD₁ hCD₀ hCD₁ tCD₀ tCD₁ hCK₀ hCK₁ tCK₀ tCK₁.
    ssprove triangle (par CK₀ CD₀ ∘ KEY) [::
      par CK₁ CD₁ ∘ KEY
    ] (par CK₀ CD₁ ∘ KEY) A
    as ineq.
    eapply ler_trans. 1: exact ineq.
    clear ineq.
    eapply ler_add.
    - eapply single_key_a. all: eauto.
    (* De-idealising the core keying package *)
    - replace (par CK₀ CD₁) with ((par (ID EK) CD₁) ∘ (par CK₀ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      replace (par CK₁ CD₁) with ((par (ID EK) CD₁) ∘ (par CK₁ (ID IGET))).
      2:{
        erewrite <- interchange.
        all: eauto.
        2-3: ssprove_valid.
        2: apply trimmed_ID.
        erewrite link_id. all: eauto.
        2: ssprove_valid.
        erewrite id_link.
        all: eauto.
      }
      rewrite Advantage_link.
      unfold K₀, K₁.
      rewrite !link_assoc.
      rewrite Advantage_sym.
      apply lerr.
    Unshelve. all: exact fset0.
  Qed.

  (** Perfect indistinguishability with PKE-CCA *)

  Definition Aux_loc :=
    MOD_CCA_loc :|: KEM_loc :|: DEM_loc :|: KEY_loc.

  Equations? Aux b : package Aux_loc [interface] PKE_CCA_out :=
    Aux b :=
    {package (MOD_CCA KEM_DEM ∘ par (KEM true) (DEM b) ∘ KEY) }.
  Proof.
    ssprove_valid.
    - (* Maybe we can automate this better *)
      apply/fdisjointP.
      intros n h.
      rewrite domm_mkfmap in h. simpl in h.
      rewrite domm_mkfmap. simpl.
      invert_in_seq h.
      all: reflexivity.
    - apply fsubsetxx.
    - unfold KEM_in, DEM_in, KEY_out.
      unfold ISET, IGET.
      rewrite -fset_cat. simpl.
      apply/fsubsetP. intros n hn.
      rewrite in_fset. rewrite in_fset in hn.
      invert_in_seq hn.
      + rewrite in_cons. apply/orP. right.
        rewrite in_cons. apply/orP. left.
        apply eqxx.
      + rewrite in_cons. apply/orP. right.
        rewrite in_cons. apply/orP. right.
        rewrite in_cons. apply/orP. left.
        apply eqxx.
    - unfold MOD_CCA_in, KEM_out, DEM_out.
      rewrite -fset_cat. simpl.
      apply fsubsetxx.
    - instantiate (1 := Aux_loc).
      unfold Aux_loc.
      eapply fsubset_trans. 1: eapply fsubsetUr.
      eapply fsubset_trans. 1: eapply fsubsetUl.
      rewrite !fsetUA. apply fsubsetxx.
    - unfold Aux_loc.
      eapply fsubset_trans. 1: eapply fsubsetUr.
      apply fsubsetxx.
    - unfold Aux_loc.
      rewrite -!fsetUA.
      eapply fsubsetUl.
    - apply fsubsetxx.
  Qed.

  (* We extend ssprove_code_simpl to use code_link_scheme *)
  Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  (* We extend swapping to schemes *)
  Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
    eapply r_swap_scheme_cmd ; ssprove_valid
    : ssprove_swap.

  (** Program equivalences

    In order to prove these equivalences, we will use an invariant that
    dismisses any changes made to the symmetric key location as it is only
    modified in one of the packages.
  *)

  Definition PkeyPair :=
    λ (pk : 'pkey) (sk : 'skey), pkey_pair (pk, sk).

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

  Instance Invariant_inv : Invariant PKE_CCA_loc Aux_loc inv.
  Proof.
    ssprove_invariant.
    - eapply fsubset_trans. 2: eapply fsubsetUr.
      unfold Aux_loc. eapply fsubsetUr.
    - rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - rewrite in_fsetU. apply /orP. right.
      unfold Aux_loc. rewrite in_fsetU. apply /orP. right.
      auto_in_fset.
    - rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - simpl. auto.
    - rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - simpl. auto.
  Qed.

  Lemma PKE_CCA_perf_false :
    (PKE_CCA KEM_DEM false) ≈₀ Aux false.
  Proof.
    unfold Aux.
    (* We go to the relation logic ignoring KEY_loc. *)
    eapply eq_rel_perf_ind with (inv := inv). 1: exact _.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    (* We are now in the realm of program logic *)
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro pk.
      ssprove_same_head_alt_r. intro pkNone.
      ssprove_same_head_alt_r. intro sk.
      ssprove_same_head_alt_r. intro skNone.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk' sk'] pps.
      eapply r_put_vs_put.
      eapply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        1,3: eapply preserve_update_pre_mem ; ssprove_invariant.
        - auto.
        - intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
          destruct hh as [[hi e1] e2]. simpl in *.
          (* TODO Some get_heap_simpl? *)
          rewrite get_set_heap_neq. 2: neq_loc_auto.
          rewrite get_set_heap_eq.
          rewrite !get_set_heap_neq. 2-5: neq_loc_auto.
          move: pkNone => /eqP pkNone.
          rewrite pkNone in e2. rewrite e2 in hi.
          set (x := get_heap s₁ k_loc) in *.
          set (y := get_heap s₁ ek_loc) in *.
          clearbody x y.
          destruct x, y. all: try contradiction.
          simpl. auto.
      }
      apply r_ret. auto.
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro pk.
      ssprove_same_head_alt_r. intro pkSome.
      destruct pk as [pk|]. 2: discriminate.
      simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro ek.
      ssprove_same_head_alt_r. intro ekNone.
      rewrite ekNone. simpl.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
      ssprove_same_head_alt_r. intro cNone.
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_remind_rhs. 1: exact _.
      rewrite cNone. simpl.
      ssprove_swap_seq_rhs [:: 0 ]%N.
      eapply r_get_remember_rhs. intros k.
      eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
      destruct ek. 1: discriminate.
      destruct k. 1: contradiction.
      simpl.
      ssprove_swap_seq_rhs [:: 0 ; 1 ]%N.
      ssprove_contract_put_get_rhs. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      eapply @rsame_head_alt with (L := fset [::]).
      1: ssprove_valid.
      1:{ intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      1:{ intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      intro c'.
      ssprove_swap_seq_lhs [:: 0 ]%N.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      (* TODO Maybe we can make something like this, but otherwise we can
        simply remember
      *)
      (* ssprove_same_head_alt_r. intros _. *)
      eapply r_put_vs_put.
      apply r_put_rhs.
      apply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        1,3: eapply preserve_update_pre_mem ; ssprove_invariant.
        intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
        destruct hh as [[[[[[hi ?] epk] ?] ?] ?] ?]. simpl in *.
        rewrite -> 2!get_set_heap_neq. 2,3: neq_loc_auto.
        rewrite  get_set_heap_neq. 2: neq_loc_auto.
        rewrite get_set_heap_eq.
        rewrite get_set_heap_neq. 2: neq_loc_auto.
        rewrite get_set_heap_eq.
        rewrite epk. simpl. auto.
      }
      apply r_ret. auto.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intros ek.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intro ekSome.
      destruct ek as [ek|]. 2: discriminate.
      simpl. destruct (ek == ek') eqn:eek.
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
        ssprove_same_head_alt_r. intro skSome.
        ssprove_swap_seq_rhs [:: 2 ; 1 ; 0 ]%N.
        ssprove_contract_get_rhs.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        destruct c as [c|]. 2: discriminate.
        simpl.
        ssprove_same_head_alt_r. intro ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek. subst ek'.
        destruct (c != c') eqn:e.
        2:{ move: e => /eqP e. subst. contradiction. }
        rewrite e. simpl.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
        destruct sk as [sk|]. 2: discriminate.
        destruct pk as [pk|]. 2: contradiction.
        destruct k as [k|]. 2: contradiction.
        simpl. simpl in hpke. simpl in eps. unfold PkeyPair in eps.
        eapply hpke in eps as h. simpl in h. subst.
        rewrite bind_ret.
        ssprove_forget_all.
        eapply @r_reflexivity_alt with (L := fset0).
        * ssprove_valid.
        * intros ℓ h. eapply fromEmpty. eauto.
        * intros ℓ v h. eapply fromEmpty. eauto.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_swap_seq_rhs [:: 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        eapply r_get_remind_rhs. 1: exact _.
        simpl.
        ssprove_forget.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        apply r_get_vs_get_remember. 1: ssprove_invariant. intros sk.
        apply r_get_remember_rhs. intro pk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          apply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        eapply sameSomeRel_sameSome in eps as eps'. rewrite eps'.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        ssprove_same_head_alt_r. intro ee.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        destruct c as [c|]. 2: discriminate.
        simpl in ee.
        rewrite eek. simpl.
        eapply @r_reflexivity_alt with (L := fset0).
        * ssprove_valid.
        * intros ℓ hℓ. eapply fromEmpty. eauto.
        * intros ℓ v hℓ. eapply fromEmpty. eauto.
    (* These remaining opsig are quite odd *)
    Unshelve. all: exact ({sig #[ 0%N ] : 'unit → 'unit }).
  Qed.

  Lemma PKE_CCA_perf_true :
    (Aux true) ≈₀ (PKE_CCA KEM_DEM true).
  Proof.
    apply adv_equiv_sym.
    unfold Aux.
    (* We go to the relation logic ignoring KEY_loc. *)
    eapply eq_rel_perf_ind with (inv := inv). 1: exact _.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    (* We are now in the realm of program logic *)
    (* TODO Below is a exactly the same prove as the false case, would be good
      to factorise.
    *)
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro pk.
      ssprove_same_head_alt_r. intro pkNone.
      ssprove_same_head_alt_r. intro sk.
      ssprove_same_head_alt_r. intro skNone.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk' sk'] pps.
      eapply r_put_vs_put.
      eapply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        1,3: eapply preserve_update_pre_mem ; ssprove_invariant.
        - auto.
        - intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
          destruct hh as [[hi e1] e2]. simpl in *.
          (* TODO Some get_heap_simpl? *)
          rewrite get_set_heap_neq. 2: neq_loc_auto.
          rewrite get_set_heap_eq.
          rewrite !get_set_heap_neq. 2-5: neq_loc_auto.
          move: pkNone => /eqP pkNone.
          rewrite pkNone in e2. rewrite e2 in hi.
          set (x := get_heap s₁ k_loc) in *.
          set (y := get_heap s₁ ek_loc) in *.
          clearbody x y.
          destruct x, y. all: try contradiction.
          simpl. auto.
      }
      apply r_ret. auto.
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro pk.
      ssprove_same_head_alt_r. intro pkSome.
      destruct pk as [pk|]. 2: discriminate.
      simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      eapply r_get_vs_get_remember. 1: ssprove_invariant. intro ek.
      ssprove_same_head_alt_r. intro ekNone.
      rewrite ekNone. simpl.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
      ssprove_same_head_alt_r. intro cNone.
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_remind_rhs. 1: exact _.
      rewrite cNone. simpl.
      ssprove_swap_seq_rhs [:: 0 ]%N.
      eapply r_get_remember_rhs. intros k.
      eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
      destruct ek. 1: discriminate.
      destruct k. 1: contradiction.
      simpl.
      ssprove_swap_seq_rhs [:: 0 ; 1 ]%N.
      ssprove_contract_put_get_rhs. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      eapply @rsame_head_alt with (L := fset [::]).
      1: ssprove_valid.
      1:{ intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      1:{ intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      intro c'.
      ssprove_swap_seq_lhs [:: 0 ]%N.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      (* TODO Maybe we can make something like this, but otherwise we can
        simply remember
      *)
      (* ssprove_same_head_alt_r. intros _. *)
      eapply r_put_vs_put.
      apply r_put_rhs.
      apply r_put_vs_put.
      ssprove_restore_mem.
      1:{
        ssprove_invariant.
        1,3: eapply preserve_update_pre_mem ; ssprove_invariant.
        intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
        destruct hh as [[[[[[hi ?] epk] ?] ?] ?] ?]. simpl in *.
        rewrite -> 2!get_set_heap_neq. 2,3: neq_loc_auto.
        rewrite  get_set_heap_neq. 2: neq_loc_auto.
        rewrite get_set_heap_eq.
        rewrite get_set_heap_neq. 2: neq_loc_auto.
        rewrite get_set_heap_eq.
        rewrite epk. simpl. auto.
      }
      apply r_ret. auto.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intros ek.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intro ekSome.
      destruct ek as [ek|]. 2: discriminate.
      simpl. destruct (ek == ek') eqn:eek.
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
        ssprove_same_head_alt_r. intro skSome.
        ssprove_swap_seq_rhs [:: 2 ; 1 ; 0 ]%N.
        ssprove_contract_get_rhs.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        destruct c as [c|]. 2: discriminate.
        simpl.
        ssprove_same_head_alt_r. intro ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek. subst ek'.
        destruct (c != c') eqn:e.
        2:{ move: e => /eqP e. subst. contradiction. }
        rewrite e. simpl.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_triple_rhs pk_loc k_loc ek_loc). 1-4: exact _. intro hpke.
        destruct sk as [sk|]. 2: discriminate.
        destruct pk as [pk|]. 2: contradiction.
        destruct k as [k|]. 2: contradiction.
        simpl. simpl in hpke. simpl in eps. unfold PkeyPair in eps.
        eapply hpke in eps as h. simpl in h. subst.
        rewrite bind_ret.
        ssprove_forget_all.
        eapply @r_reflexivity_alt with (L := fset0).
        * ssprove_valid.
        * intros ℓ h. eapply fromEmpty. eauto.
        * intros ℓ v h. eapply fromEmpty. eauto.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_swap_seq_rhs [:: 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        eapply r_get_remind_rhs. 1: exact _.
        simpl.
        ssprove_forget.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        apply r_get_vs_get_remember. 1: ssprove_invariant. intros sk.
        apply r_get_remember_rhs. intro pk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          apply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        eapply sameSomeRel_sameSome in eps as eps'. rewrite eps'.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        ssprove_same_head_alt_r. intro ee.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        destruct c as [c|]. 2: discriminate.
        simpl in ee.
        rewrite eek. simpl.
        eapply @r_reflexivity_alt with (L := fset0).
        * ssprove_valid.
        * intros ℓ hℓ. eapply fromEmpty. eauto.
        * intros ℓ v hℓ. eapply fromEmpty. eauto.
    (* These remaining opsig are quite odd *)
    Unshelve. all: exact ({sig #[ 0%N ] : 'unit → 'unit }).
  Qed.

  (** Security theorem *)

  Theorem PKE_security :
    ∀ LA A,
      ValidPackage LA PKE_CCA_out A_export A →
      fdisjoint LA PKE_CCA_loc →
      fdisjoint LA Aux_loc → (* Do we really need this? *)
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
    eapply ler_trans. 1: exact ineq.
    clear ineq.
    rewrite PKE_CCA_perf_false. 2,3: auto.
    rewrite PKE_CCA_perf_true. 2,3: auto.
    rewrite GRing.addr0. rewrite GRing.add0r.
    (* Now we massage the expression to apply the single key lemma *)
    eapply ler_trans.
    - rewrite Advantage_sym.
      rewrite -Advantage_link.
      eapply single_key_b with (CK₁ := (KEM false).(pack)).
      7,8: ssprove_valid.
      9,10: ssprove_valid.
      1-2: ssprove_valid.
      (* Sad we have to do this before. *)
      5-8: unfold KEM, DEM.
      5-8: cbn - [mkdef mkfmap].
      5-8: ssprove_valid.
      all: unfold Parable.
      all: rewrite domm_ID_fset.
      3,4: rewrite fdisjointC.
      all:
        eapply fdisjoint_trans ; [
          eapply domm_trimmed ; unfold KEM, DEM ;
          cbn - [mkdef mkfmap] ; ssprove_valid
        |].
      all: simpl.
      all: unfold idents, KEM_out, DEM_out.
      all: rewrite imfset_fset.
      all: simpl.
      (* TODO Can we do better than what follows? *)
      all: rewrite fdisjointC.
      all: apply/fdisjointP.
      all: intros x hx.
      all: rewrite in_fset in hx.
      all: rewrite in_fset.
      all: invert_in_seq hx.
      all: reflexivity.
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
      (* TODO Can we do better than what follows? *)
      all: unfold Parable.
      all: rewrite domm_ID_fset.
      all: rewrite fdisjointC.
      all:
        eapply fdisjoint_trans ; [
          eapply domm_trimmed ; unfold KEM, DEM ; cbn - [mkdef mkfmap] ; ssprove_valid
        |].
      all: simpl.
      all: unfold idents, DEM_out.
      all: rewrite imfset_fset.
      all: simpl.
      all: rewrite fdisjointC.
      all: apply/fdisjointP.
      all: intros x hx.
      all: rewrite in_fset in hx.
      all: rewrite in_fset.
      all: invert_in_seq hx.
      all: reflexivity.
  Qed.

End KEMDEM.