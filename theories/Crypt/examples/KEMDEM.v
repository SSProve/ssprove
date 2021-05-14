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

  (** In the SSP paper, we have λ.
      key_length would 2^λ because we do not use bitstrings.
      This also applies for things like cipher and encapsulation lengths.
      Instead we will have dedicated types for objects.
      We still use cardinals when we need them to be finite types for
      uniform sampling.
  *)

  (** Symmetric key length *)
  Context (key_length : nat) `{Positive key_length}.

  (** Public and secret key lengths  *)
  Context (pkey_length : nat) `{Positive pkey_length}.
  Context (skey_length : nat) `{Positive skey_length}.

  (** Plain text *)
  Context (chPlain : chUniverse).

  (** Ecrypted key *)
  Context (ekey_length : nat) `{Positive ekey_length}.

  (** Cipher text *)
  Context (cipher_length : nat) `{Positive cipher_length}.

  (** Types *)
  Notation "'key" := ('fin key_length) (in custom pack_type at level 2).
  Notation "'key" := ('fin key_length) (at level 2) : package_scope.

  Notation "'pkey" := ('fin pkey_length) (in custom pack_type at level 2).
  Notation "'pkey" := ('fin pkey_length) (at level 2) : package_scope.

  Notation "'skey" := ('fin skey_length) (in custom pack_type at level 2).
  Notation "'skey" := ('fin skey_length) (at level 2) : package_scope.

  Notation "'plain" := (chPlain) (in custom pack_type at level 2).
  Notation "'plain" := (chPlain) (at level 2) : package_scope.

  Notation "'ekey" := ('fin ekey_length) (in custom pack_type at level 2).
  Notation "'ekey" := ('fin ekey_length) (at level 2) : package_scope.

  Notation "'cipher" := ('fin cipher_length) (in custom pack_type at level 2).
  Notation "'cipher" := ('fin cipher_length) (at level 2) : package_scope.

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

  (** Uniform distributions *)
  Definition i_key := key_length.
  Definition i_pk := pkey_length.
  Definition i_sk := skey_length.
  Definition i_ek := ekey_length.
  Definition i_c := cipher_length.

  (** Some shorthands *)
  Definition IGEN := [interface val #[ GEN ] : 'unit → 'unit ].
  Definition ISET := [interface val #[ SET ] : 'key → 'unit ].
  Definition IGET := [interface val #[GET] : 'unit → 'key ].

  (** PKE scheme *)

  Record PKE_scheme := {
    PKE_kgen : code fset0 [interface] (chProd 'pkey 'skey) ;
    PKE_enc : 'pkey → 'plain → code fset0 [interface] (chProd 'ekey 'cipher) ;
    PKE_dec : 'skey → chProd 'ekey 'cipher → code fset0 [interface] 'plain
  }.

  (** KEM scheme *)

  Record KEM_scheme := {
    KEM_kgen : code fset0 [interface] (chProd 'pkey 'skey) ;
    KEM_encap : 'pkey → code fset0 [interface] (chProd 'key 'ekey) ;
    KEM_decap : 'skey → 'ekey → code fset0 [interface] 'key
  }.

  (** DEM scheme *)

  Record DEM_scheme := {
    DEM_enc : 'key → 'plain → code fset0 [interface] 'cipher ;
    DEM_dec : 'key → 'cipher → code fset0 [interface] 'plain
  }.

  Context (η : KEM_scheme).
  Context (θ : DEM_scheme).

  (** KEY Package *)

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
        k ← sample uniform i_key ;;
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
        if b return raw_code 'ekey
        then (
          '(k, ek) ← η.(KEM_encap) pk ;;
          put ek_loc := Some ek ;;
          SET k ;;
          ret ek
        )
        else (
          ek ← sample uniform i_ek ;;
          put ek_loc := Some ek ;;
          GEN Datatypes.tt ;;
          ret ek
        )
      } ;
      def #[ DECAP ] (ek' : 'ekey) : 'key {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        #assert (isSome ek) as ekSome ;;
        let ek := getSome ek ekSome in
        #assert (ek != ek') ;;
        η.(KEM_decap) sk ek'
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
    λ b,
      if b
      then {locpackage KEM_CCA_pkg true }
      else {locpackage KEM_CCA_pkg false }.

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
        if b
        then (
          c ← θ.(DEM_enc) k m ;;
          put c_loc := Some c ;;
          ret c
        )
        else (
          c ← sample uniform i_c ;;
          put c_loc := Some c ;;
          ret c
        )
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
    λ b,
      if b
      then {locpackage DEM_CCA_pkg true }
      else {locpackage DEM_CCA_pkg false }.

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
            In the future, we can probably ensure that pk_loc is empty iff
            sk_loc is empty, by using a stronger invariant.
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
        '(ek, c) ← (
          if b return raw_code (chProd 'ekey 'cipher)
          then ζ.(PKE_enc) pk m
          else (
            ek ← sample uniform i_ek ;;
            c ← sample uniform i_c ;;
            ret (ek, c)
          )
        ) ;;
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
    λ b,
      if b
      then {locpackage PKE_CCA_pkg ζ true }
      else {locpackage PKE_CCA_pkg ζ false }.

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
      k ← η.(KEM_decap) sk ek ;;
      θ.(DEM_dec) k c
    }
  |}.

  (** Single key lemma *)

  (* Corresponds to Lemma 19.a in the SSP paper *)
  Lemma single_key :
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

  (** Perfect indistinguishability with PKE-CCA *)

  Definition Aux_loc :=
    MOD_CCA_loc :|: KEM_loc :|: DEM_loc :|: KEY_loc.

  Equations? Aux b : package Aux_loc [interface] PKE_CCA_out :=
    Aux b :=
    {package (MOD_CCA KEM_DEM ∘ par (KEM b) (DEM b) ∘ KEY) }.
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
    - destruct b.
      all: unfold KEM_in, DEM_in, KEY_out.
      all: unfold ISET, IGET, IGEN.
      all: rewrite -fset_cat. all: simpl.
      + apply/fsubsetP. intros n hn.
        rewrite in_fset. rewrite in_fset in hn.
        invert_in_seq hn.
        * rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. left.
          apply eqxx.
        * rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. left.
          apply eqxx.
      + apply/fsubsetP. intros n hn.
        rewrite in_fset. rewrite in_fset in hn.
        invert_in_seq hn.
        * rewrite in_cons. apply/orP. left.
          apply eqxx.
        * rewrite in_cons. apply/orP. right.
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

  (** Program equivalences

    In order to prove these equivalences, we will use an invariant that
    dismisses any changes made to the symmetric key location as it is only
    modified in one of the packages.
  *)

  Notation inv :=
    (heap_ignore KEY_loc ⋊
    couple_rhs c_loc k_loc sameSome ⋊
    couple_lhs pk_loc sk_loc sameSome).

  Instance Invariant_inv : Invariant PKE_CCA_loc Aux_loc inv.
  Proof.
    ssprove_invariant.
    - simpl.
      eapply fsubset_trans. 2: eapply fsubsetUr.
      unfold Aux_loc. eapply fsubsetUr.
    - simpl. rewrite in_fsetU. apply /orP. left.
      unfold PKE_CCA_loc. auto_in_fset.
    - simpl. rewrite in_fsetU. apply /orP. right.
      unfold Aux_loc. rewrite in_fsetU. apply /orP. right.
      auto_in_fset.
    - reflexivity.
    - simpl. rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - simpl. rewrite in_fsetU. apply /orP. left.
      auto_in_fset.
    - reflexivity.
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
      ssprove_same_head_alt_r. intro pk.
      ssprove_same_head_alt_r. intro pkNone.
      ssprove_same_head_alt_r. intro sk.
      ssprove_same_head_alt_r. intro skNone.
      eapply r_bind.
      { eapply @r_reflexivity_alt with (L := fset [::]).
        - ssprove_valid.
        - intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
        - intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
      }
      intros [] [].
      eapply rpre_hypothesis_rule. intros s₀ s₁ [e ?].
      noconf e.
      eapply rpre_weaken_rule.
      1: eapply r_put_put.
      + ssprove_invariant.
        * apply preserve_set_set_couple_rhs_neq. all: neq_loc_auto.
        * apply preserve_set_set_couple_lhs_eq.
          -- neq_loc_auto.
          -- reflexivity.
      + apply r_ret. auto.
      + simpl. intuition subst. auto.
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      (* That was a lot of simpl. Would be good to have it all sorted out
        as one thing.
      *)
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_same_head_alt_r. intro pk.
      ssprove_same_head_alt_r. intro pkSome.
      rewrite pkSome. simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_same_head_alt_r. intro ek.
      ssprove_same_head_alt_r. intro ekNone.
      rewrite ekNone. simpl.
      ssprove_swap_seq_rhs [:: 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
      eapply r_get_remember_rhs. intro k.
      eapply (r_rem_couple_rhs c_loc k_loc). 1-3: exact _. intro eck.
      ssprove_forget_all.
      ssprove_same_head_alt_r. intro cNone.
      rewrite cNone. simpl.
      eapply sameSome_None_l in cNone as kNone. 2: eauto.
      rewrite kNone. simpl.
      ssprove_same_head_alt_r. intro ek'.
      ssprove_swap_lhs 0%N.
      ssprove_swap_seq_rhs [:: 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_same_head_alt_r. intros _.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intros c'.
      eapply r_const_sample_R with (op := uniform _). 1: exact _. intro k'.
      ssprove_contract_put_get_rhs. simpl.
      ssprove_swap_seq_rhs [:: 0 ; 1 ]%N.
      ssprove_contract_put_rhs.
      eapply r_put_putR. 1:{
        ssprove_invariant.
        - (* TODO ADD to ssprove_invariant *) auto_in_fset.
        - eapply preserve_set_setR_couple_rhs_eq.
          + neq_loc_auto.
          + reflexivity.
        - eapply preserve_set_setR_couple_lhs_neq. all: neq_loc_auto.
      }
      apply r_ret. auto.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant.
      intros ek.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intro ekSome.
      destruct ek as [ek|]. 2: discriminate.
      simpl. destruct (ek == ek') eqn:eek.
      + rewrite eek.
        ssprove_code_simpl_more. ssprove_code_simpl. ssprove_code_simpl_more.
        ssprove_forget.
        eapply r_get_remember_rhs. intro pk.
        eapply r_get_remember_lhs. intro sk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          eapply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        rewrite eps.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_swap_seq_rhs [:: 2 ; 1 ; 0 ]%N.
        ssprove_contract_get_rhs.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ]%N.
        eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_couple_rhs c_loc k_loc). 1-3: exact _. intro eck.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro cSome.
        destruct c as [c|]. 2: discriminate.
        destruct k as [k|]. 2: discriminate.
        simpl.
        ssprove_same_head_alt_r. intro ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek. subst.
        destruct (c != c') eqn: e.
        2:{ move: e => /eqP e. subst. exfalso. apply ee. reflexivity. }
        rewrite e. simpl.
        rewrite bind_ret.
        (* TODO This bit is actually explained in the SSP paper
          Now, we have to see how to actually exploit it. It seems
          to involve correctness of the KEM, so we might need to do
          something about that.

          We have ek = ek' (now subst).
          We should use this information to conclude that ek decrypted to k
          probably.

          The idea is to remember that ek is obtained from
          encap and thus that decap on it will be the identity.
          Don't we have a problem when they are randomly generated
          (the present case)?
          ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
            '(k, ek) ← KEM_encap pk ;;
            KEM_decap sk ek
            ≈
            '(k, ek) ← KEM_encap pk ;;
            ret k
          ⦃ eq ⦄

          The problem is that this information is not available in this branch
          anyway because the boolean is false and ek is obtained at random.
        *)
        admit.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_swap_seq_rhs [:: 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        eapply r_get_remind_rhs. 1: exact _.
        simpl.
        ssprove_forget.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        apply r_get_vs_get_remember. 1: ssprove_invariant.
        intros sk.
        apply r_get_remember_rhs. intro pk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          apply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        rewrite eps.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        ssprove_same_head_alt_r. intro ee.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        destruct c as [c|]. 2: discriminate.
        simpl.
        simpl in ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek.
        destruct (ek != ek') eqn:e.
        2:{ move: e => /eqP e. subst. exfalso. eapply eek. reflexivity. }
        rewrite e. simpl.
        eapply @r_reflexivity_alt with (L := fset [::]).
        * ssprove_valid.
        * intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
        * intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
  Admitted.

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
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_same_head_alt_r. intro pk.
      ssprove_same_head_alt_r. intro pkNone.
      ssprove_same_head_alt_r. intro sk.
      ssprove_same_head_alt_r. intro skNone.
      eapply r_bind.
      { eapply @r_reflexivity_alt with (L := fset [::]).
        - ssprove_valid.
        - intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
        - intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
      }
      intros [] [].
      eapply rpre_hypothesis_rule. intros s₀ s₁ [e ?].
      noconf e.
      eapply rpre_weaken_rule.
      1: eapply r_put_put.
      + ssprove_invariant.
        * apply preserve_set_set_couple_rhs_neq. all: neq_loc_auto.
        * apply preserve_set_set_couple_lhs_eq.
          -- neq_loc_auto.
          -- reflexivity.
      + apply r_ret. auto.
      + simpl. intuition subst. auto.
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_same_head_alt_r. intro pk.
      ssprove_same_head_alt_r. intro pkSome.
      destruct pk as [pk|]. 2: discriminate.
      simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_same_head_alt_r. intro ek.
      ssprove_same_head_alt_r. intro ekNone.
      rewrite ekNone. simpl.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
      ssprove_same_head_alt_r. intro cNone.
      (** For some reason the following masks the chUniverses
          I would still like to use that, rather than what we currently use.
      *)
      (* eapply @rsame_head_alt with (L := fset [::]).
      1: ssprove_valid.
      1:{ intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      1:{ intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto. }
      intros [k' ek']. *)
      (* *** *)
      eapply r_bind.
      { eapply @r_reflexivity_alt with (L := fset [::]).
        - ssprove_valid.
        - intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
        - intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
      }
      intros [k₀ ek₀] [k₁ ek₁].
      eapply rpre_hypothesis_rule. intros s₀ s₁ [e hpre]. noconf e.
      eapply rpre_weaken_rule
      with (pre := λ '(s₀, s₁), (inv ⋊ rem_rhs c_loc c) (s₀, s₁)).
      2:{ simpl. intuition subst. auto. }
      clear s₀ s₁ hpre.
      (* * *)
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_remind_rhs. 1: exact _.
      ssprove_swap_seq_rhs [:: 0 ]%N.
      eapply r_get_remember_rhs. intros k.
      eapply (r_rem_couple_rhs c_loc k_loc). 1-3: exact _. intro eck.
      eapply sameSome_None_l in cNone as kNone. 2: eauto.
      rewrite cNone. rewrite kNone. simpl.
      ssprove_swap_seq_rhs [:: 0 ; 1 ]%N.
      ssprove_contract_put_get_rhs. simpl.
      ssprove_forget_all.
      (* TODO r_put_rhs, but we don't want to use it, we want r_put_put here
        to preserve the invariant with c.
        Rather a variant of r_put_put with only one put on one side.
      *)
      (* TODO Add ways to swap schemes
        Might be good to be able to extend the swap commands.
        Maybe I should have a treatment of goals to make the head into a cmd?
        In order to factorise a bit. We'll still have to deal with
        cmd vs bind, assert vs bind and symmetric.
      *)
      (* Once this is done, the goal is ok! *)
      admit.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant.
      intros ek.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intro ekSome.
      destruct ek as [ek|]. 2: discriminate.
      simpl. destruct (ek == ek') eqn:eek.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_code_simpl. ssprove_code_simpl_more.
        ssprove_forget.
        eapply r_get_remember_rhs. intro pk.
        eapply r_get_remember_lhs. intro sk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          eapply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        rewrite eps.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_swap_seq_rhs [:: 2 ; 1 ; 0 ]%N.
        ssprove_contract_get_rhs.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ]%N.
        eapply r_get_vs_get_remember_rhs. 1: ssprove_invariant. intro c.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_couple_rhs c_loc k_loc). 1-3: exact _. intro eck.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro cSome.
        destruct c as [c|]. 2: discriminate.
        destruct k as [k|]. 2: discriminate.
        simpl.
        ssprove_same_head_alt_r. intro ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek. subst.
        destruct (c != c') eqn: e.
        2:{ move: e => /eqP e. subst. exfalso. apply ee. reflexivity. }
        rewrite e. simpl.
        rewrite bind_ret.
        (* Here we probably need validity, but as long as the other one
          isn't solved, it's not clear it's worth it.
        *)
        admit.
      + rewrite eek. ssprove_code_simpl_more.
        ssprove_swap_seq_rhs [:: 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        eapply r_get_remind_rhs. 1: exact _.
        simpl.
        ssprove_forget.
        ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ; 0 ]%N.
        apply r_get_vs_get_remember. 1: ssprove_invariant.
        intros sk.
        apply r_get_remember_rhs. intro pk.
        eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
        1:{
          apply Remembers_lhs_from_tracked_rhs.
          - exact _.
          - ssprove_invariant.
        }
        intro eps.
        rewrite eps.
        ssprove_forget_all.
        ssprove_same_head_alt_r. intro skSome.
        ssprove_same_head_alt_r. intro c.
        ssprove_same_head_alt_r. intro cSome.
        ssprove_same_head_alt_r. intro ee.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        destruct c as [c|]. 2: discriminate.
        simpl in ee.
        move: ee => /eqP ee.
        move: eek => /eqP eek.
        destruct (ek != ek') eqn:e.
        2:{ move: e => /eqP e. subst. exfalso. eapply eek. reflexivity. }
        rewrite e. simpl.
        eapply @r_reflexivity_alt with (L := fset [::]).
        * ssprove_valid.
        * intros ℓ hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
        * intros ℓ v hℓ. rewrite -fset0E in hℓ. eapply fromEmpty. eauto.
  Admitted.

  (** Security theorem *)

  Theorem PKE_security :
    ∀ LA A,
      ValidPackage LA PKE_CCA_out A_export A →
      fdisjoint LA PKE_CCA_loc →
      fdisjoint LA Aux_loc → (* Do we really need this? *)
      Advantage (PKE_CCA KEM_DEM) A <=
      Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM true)) +
      Advantage DEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (KEM false) (ID DEM_out)).
  Proof.
    intros LA A hA hA' hd.
    rewrite Advantage_E.
    ssprove triangle (PKE_CCA KEM_DEM false) [::
      (MOD_CCA KEM_DEM) ∘ par (KEM false) (DEM false) ∘ KEY ;
      (MOD_CCA KEM_DEM) ∘ par (KEM true) (DEM true) ∘ KEY
    ] (PKE_CCA KEM_DEM true) A
    as ineq.
    eapply ler_trans. 1: exact ineq.
    clear ineq.
    (* Aux_loc is problematic here, can I make it equal to PKE_CCA_loc? *)
    rewrite PKE_CCA_perf_false. 2,3: auto.
    rewrite PKE_CCA_perf_true. 2,3: auto.
    rewrite GRing.addr0. rewrite GRing.add0r.
    (* Now we massage the expression to apply the single key lemma *)
    eapply ler_trans.
    - rewrite Advantage_sym.
      rewrite -Advantage_link.
      eapply single_key.
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
          eapply domm_trimmed ; unfold KEM, DEM ; cbn - [mkdef mkfmap] ; ssprove_valid
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
      all: rewrite Advantage_sym. 1: reflexivity.
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