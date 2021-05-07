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
        k ← η.(KEM_decap) sk ek' ;;
        ret k
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
        m ← θ.(DEM_dec) k c' ;;
        ret m
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
        m ← ζ.(PKE_dec) sk c' ;;
        ret m
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
        pk ← KEMGEN Datatypes.tt ;;
        ret pk
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
          m ← DEC c' ;;
          ret m
        )
        else (
          k' ← DECAP ek' ;;
          m ← θ.(DEM_dec) k' c' ;;
          ret m
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
      m ← θ.(DEM_dec) k c ;;
      ret m
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
    pose proof (
      Advantage_triangle_chain (par CK₀ CD₀ ∘ KEY) [::
        par CK₁ CD₀ ∘ KEY
      ] (par CK₁ CD₁ ∘ KEY) A
    ) as ineq.
    advantage_sum simpl in ineq.
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

  (* TODO MOVE *)
  Definition sameSome {A B} (x : option A) (y : option B) :=
    isSome x = isSome y.

  Lemma PKE_CCA_perf_false :
    (PKE_CCA KEM_DEM false) ≈₀ Aux false.
    (* (MOD_CCA KEM_DEM ∘ par (KEM false) (DEM false) ∘ KEY). *)
  Proof.
    unfold Aux.
    (* We go to the relation logic ignoring KEY_loc. *)
    eapply eq_rel_perf_ind
    with (inv := heap_ignore KEY_loc ⋊ couple_rhs c_loc k_loc sameSome).
    1:{
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
    }
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    (* We are now in the realm of program logic *)
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      (* TODO ssprove_reflexivity tactic

      OLD:
        Proabbly a general one which requires the preserve_eq like same_head
        because that's the proof basically is, meaning we can leverage
        the same automation for both!
      *)
      eapply @r_reflexivity_alt with (L := fset [:: pk_loc ; sk_loc]).
      + ssprove_valid.
      + (* Here it would be nice to have some automation! *)
        intros ℓ hℓ.
        (* We should have lemmata on get_pre_cond instead of preserve stuff *)
        admit.
      + (* Automate as well! Probably in the style of ssprove_invariant/valid *)
        admit.
      (* eapply r_reflexivity_heap_ignore with (L := fset [:: pk_loc ; sk_loc]).
      + apply /fdisjointP. simpl. intros ? h.
        rewrite in_fset in h.
        invert_in_seq h.
        all: notin_fset_auto.
      + ssprove_valid. *)
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
      (* Maybe we want to specialised the lemma to use λ '(s₀, s₁) so that
        we have a neater goal.
      *)
      ssprove_same_head_alt_r. 1:admit. intro pk.
      ssprove_same_head_alt_r. intro pkSome.
      rewrite pkSome. simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_same_head_alt_r. 1:admit. intro ek.
      ssprove_same_head_alt_r. intro ekNone.
      rewrite ekNone. simpl.
      ssprove_swap_seq_rhs [:: 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_get_rhs.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      (* Just a sanity check below
        We wouldn't need to do it now, and we would need to contract the two
        put c_loc.
      *)
      (* ssprove_swap_seq_rhs [:: 11 ; 10 ; 9 ; 8 ; 7 ]%N.
      ssprove_swap_seq_rhs [:: 12 ; 11 ; 10 ; 9 ]%N. *)

      (* Old version below *)
      (* ssprove_same_head_alt_r. intro c.
      ssprove_same_head_alt_r. intro cNone.
      rewrite cNone. simpl.
      ssprove_same_head_alt_r. intro ek'.
      ssprove_swap_lhs 0%N.
      ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ]%N.
      ssprove_contract_put_rhs.
      ssprove_same_head_alt_r. intros _.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
      ssprove_same_head_alt_r. intros c'. *)

      (* Maybe what I should do first is try to get into a state where
        the get for c_loc (or ek_loc) and k_loc are next to one another
        to see whether we can conjure an extra invariant binding the two
        locations together.
        Then have this invariant and have rule for get/get and put/put.
        Would then need to deal with conjunctions of invariants or at least
        combinations of them.

        We could also make do with breaking the invariant and restoring it
        as we go. Probably more involved in terms of dealing with the invariant.

        Doing the first one would help with pk/sk business as well.

        Maybe we can deal with invariants with a class Invariant
        (with INV' but also the empty_heap assumption).
        This way things like same_head are user extensible.
        We can see if we can do the same for precond preservation.

        We should also make have rules saying we can ignore put/get
        on heap_ignored locations.
        We won't be using those anyway because we would have to maintain
        the other invariant.
        It might actually make more sense to have some invariant that
        combines the two information since we want to ingnore the get/put
        on k_loc, but not the one c/ek_loc.
        It sounds difficult to have something generic here.
        Maybe we'll have to craft our own tailored invariant, in which case
        it's a good idea to have the tactics user-extensible.

        What we can do is probably have some predicates/classes on preconditions
        such as [ignores pre ℓ] or [couples_left h pre ℓ ℓ'] and then have
        conditional rules that don't force the precondition into a certain
        shape, but only to have certain properties.
        Not very clear how it would work for [ignores] because we might have
        [heap_ignore L ∧ eq] which would not work. Again, maybe a best-effort
        will work in most cases. Proving ignores on conj would be fine and
        we can show ingores (coouples_left) for instance.
      *)
      admit.
    - (* ssprove_code_simpl. *)
      (* It seems the simplifications tactics did something weird to the let *)
      (* In the SSP paper proof, there is pk on the lhs instead of sk.
        but changing it in the rhs means changing the locations of MOD-CCA to
        add some sk which is never set, doesn't make much sense,
        and if we change it to pk in the lhs we don't have the info needed
        to actually read sk...
      *)
      destruct m as [ek' c']. simpl.
      admit.
  Admitted.

  Lemma PKE_CCA_perf_true :
    (Aux true) ≈₀ (PKE_CCA KEM_DEM true).
  Proof.
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
    pose proof (
      Advantage_triangle_chain (PKE_CCA KEM_DEM false) [::
        (MOD_CCA KEM_DEM) ∘ par (KEM false) (DEM false) ∘ KEY ;
        (MOD_CCA KEM_DEM) ∘ par (KEM true) (DEM true) ∘ KEY
      ] (PKE_CCA KEM_DEM true) A
    ) as ineq.
    advantage_sum simpl in ineq.
    rewrite !GRing.addrA in ineq.
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