(** KEM-DEM example *)

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

  (** In the SSP paper, we have λ.
      key_length would 2^λ because we do not use bitstrings.
  *)
  Context (key_length : nat) `{Positive key_length}.

  Context (plain_length : nat) `{Positive plain_length}.

  (** In the paper, the following are functions of |m|, here we assume |m|
      is constant: plain_length.
  *)
  Context (clen : nat) `{Positive clen}.
  Context (elen : nat) `{Positive elen}.

  (** Types *)
  Notation "'key" := ('fin key_length) (in custom pack_type at level 2).
  Notation "'key" := ('fin key_length) (at level 2) : package_scope.

  Notation "'plain" := ('fin plain_length) (in custom pack_type at level 2).
  Notation "'plain" := ('fin plain_length) (at level 2) : package_scope.

  Notation "'clen" := ('fin clen) (in custom pack_type at level 2).
  Notation "'clen" := ('fin clen) (at level 2) : package_scope.

  Notation "'elen" := ('fin elen) (in custom pack_type at level 2).
  Notation "'elen" := ('fin elen) (at level 2) : package_scope.

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
  Definition key : Location := ('option 'key ; 0%N).
  Definition pk_loc : Location := ('option 'key ; 1%N).
  Definition sk_loc : Location := ('option 'key ; 2%N).
  Definition c_loc : Location := ('option ('elen × 'clen) ; 3%N).
  Definition ce_loc : Location := ('option 'elen ; 4%N).
  Definition cc_loc : Location := ('option 'clen ; 5%N).

  (** Uniform distributions *)
  Definition i_key := key_length.
  Definition i_clen := clen.
  Definition i_elen := elen.

  (** Some shorthands *)
  Definition IGEN := [interface val #[ GEN ] : 'unit → 'unit ].
  Definition ISET := [interface val #[ SET ] : 'key → 'unit ].
  Definition IGET := [interface val #[GET] : 'unit → 'key ].

  (** PKE scheme *)

  Record PKE_scheme := {
    PKE_kgen : code fset0 [interface] (chProd 'key 'key) ;
    PKE_enc : 'key → 'plain → code fset0 [interface] (chProd 'elen 'clen) ;
    (* clen is global *)
    PKE_dec : 'key → chProd 'elen 'clen → code fset0 [interface] 'plain
  }.

  (** KEM scheme *)

  Record KEM_scheme := {
    KEM_kgen : code fset0 [interface] (chProd 'key 'key) ;
    KEM_encap : 'key → code fset0 [interface] (chProd 'key 'elen) ;
    KEM_decap : 'key → 'elen → code fset0 [interface] 'key
  }.

  (** DEM scheme *)

  Record DEM_scheme := {
    DEM_enc : 'key → 'plain → code fset0 [interface] 'clen ;
    DEM_dec : 'key → 'clen → code fset0 [interface] 'plain
  }.

  Context (η : KEM_scheme).
  Context (θ : DEM_scheme).

  (** KEY Package *)

  Definition KEY_loc :=
    fset [:: key ].

  Definition KEY_out :=
    [interface
      val #[ GEN ] : 'unit → 'unit ;
      val #[ SET ] : 'key → 'unit ;
      val #[ GET ] : 'unit → 'key
    ].

  Definition KEY : package KEY_loc [interface] KEY_out :=
    [package
      def #[ GEN ] (_ : 'unit) : 'unit {
        k ← get key ;;
        assert (k == None) ;;
        k ← sample uniform i_key ;;
        put key := Some k ;;
        ret Datatypes.tt
      } ;
      def #[ SET ] (k : 'key) : 'unit {
        k' ← get key ;;
        assert (k' == None) ;;
        put key := Some k ;;
        ret Datatypes.tt
      } ;
      def #[ GET ] (_ : 'unit) : 'key {
        k ← get key ;;
        #assert (isSome k) as kSome ;;
        @ret 'key (getSome k kSome)
      }
    ].

  (** KEM package *)

  Definition KEM_loc := fset [:: pk_loc ; sk_loc ; ce_loc ].

  Definition KEM_in b :=
    if b then ISET else IGEN.

  Definition KEM_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key
    ].

  (* Export? *)
  Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
    eapply valid_scheme ; eapply c.(prog_valid)
    : typeclass_instances packages.

  (* TODO Find a way to make this not mandatory *)
  Opaque mkfmap mkdef.

  #[program] Definition KEM (b : bool) : package KEM_loc (KEM_in b) KEM_out :=
    [package
      def #[ KEMGEN ] (_ : 'unit) : 'key {
        sk ← get sk_loc ;;
        assert (sk == None) ;;
        '(pk, sk) ← η.(KEM_kgen) ;;
        put pk_loc := Some pk ;;
        put sk_loc := Some sk ;;
        ret pk
      } ;
      def #[ ENCAP ] (_ : 'unit) : 'elen {
        #import {sig #[ SET ] : 'key → 'unit } as SET ;;
        #import {sig #[ GEN ] : 'unit → 'unit } as GEN ;;
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        c ← get ce_loc ;;
        assert (c == None) ;;
        if b return raw_code 'elen
        then (
          '(k, c) ← η.(KEM_encap) pk ;;
          put ce_loc := Some c ;;
          SET k ;;
          ret c
        )
        else (
          c ← sample uniform i_elen ;;
          put ce_loc := Some c ;;
          GEN Datatypes.tt ;;
          ret c
        )
      } ;
      def #[ DECAP ] (c' : 'elen) : 'key {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        c ← get ce_loc ;;
        assert (c != Some c') ;;
        k ← η.(KEM_decap) sk c' ;;
        ret k
      }
    ].
  Next Obligation.
    ssprove_valid.
    - destruct x2. ssprove_valid.
    - destruct x1. ssprove_valid.
  Qed.

  (** KEM-CCA game *)

  Definition KEM_CCA_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key ;
      val #[GET] : 'unit → 'key
    ].

  (* Maybe inline? *)
  Definition KEM_CCA_loc :=
    KEM_loc :|: KEY_loc.

  #[program] Definition KEM_CCA_pkg b :
    package KEM_CCA_loc [interface] KEM_CCA_out :=
    {package (par (KEM b) (ID IGET)) ∘ KEY }.
  Next Obligation.
    ssprove_valid.
    6: destruct x2. 6: ssprove_valid.
    11: destruct x1. 11: ssprove_valid.
    15:{
      unfold KEM_CCA_out. rewrite -fset_cat. simpl.
      apply fsubsetxx.
    }
    14:{
      instantiate (1 := KEM_in b).
      destruct b. all: unfold KEM_in.
      all: unfold ISET, IGET.
      all: rewrite -fset_cat. all: simpl.
      - apply /fsubsetP. simpl.
        intros n h. rewrite in_fset. rewrite in_fset in h.
        invert_in_seq h.
        + rewrite in_cons. apply/orP. right. rewrite in_cons.
          apply/orP. left. apply eqxx.
        + rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. right.
          rewrite mem_seq1. apply eqxx.
      - apply /fsubsetP. simpl.
        intros n h. rewrite in_fset. rewrite in_fset in h.
        invert_in_seq h.
        + rewrite in_cons. apply/orP. left. apply eqxx.
        + rewrite in_cons. apply/orP. right.
          rewrite in_cons. apply/orP. right.
          rewrite mem_seq1. apply eqxx.
    }
    7,9: unfold KEM_in, ISET, IGEN.
    20: apply fsubsetUr.
    19: apply fsubsetUl.
    13:{ erewrite fsetU0. apply fsubsetxx. }
    all: ssprove_valid.
    2-10: unfold KEM_loc.
    11-15: unfold KEY_loc.
    all: ssprove_valid.
    (* Maybe we can automate this better *)
    apply/fdisjointP.
    intros n h.
    rewrite domm_mkfmap in h. simpl in h.
    rewrite domm_ID_fset. rewrite in_fset. simpl.
    invert_in_seq h.
    all: reflexivity.
  Qed.

  Definition KEM_CCA : loc_GamePair KEM_CCA_out :=
    λ b,
      if b
      then {locpackage KEM_CCA_pkg true }
      else {locpackage KEM_CCA_pkg false }.

  (** DEM package *)

  Definition DEM_loc := fset [:: cc_loc ].

  Definition DEM_in := IGET.

  Definition DEM_out :=
    [interface
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  Definition DEM (b : bool) : package DEM_loc DEM_in DEM_out :=
    [package
      def #[ ENC ] (m : 'plain) : 'clen {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get cc_loc ;;
        assert (c == None) ;;
        k ← GET Datatypes.tt ;;
        if b
        then (
          c ← θ.(DEM_enc) k m ;;
          put cc_loc := Some c ;;
          ret c
        )
        else (
          c ← sample uniform i_clen ;;
          put cc_loc := Some c ;;
          ret c
        )
      } ;
      def #[ DEC ] (c' : 'clen) : 'plain {
        #import {sig #[ GET ] : 'unit → 'key } as GET ;;
        c ← get cc_loc ;;
        assert (c != Some c') ;;
        k ← GET Datatypes.tt ;;
        m ← θ.(DEM_dec) k c' ;;
        ret m
      }
    ].

  (** DEM-CCA game *)

  Definition DEM_CCA_out :=
    [interface
      val #[ GEN ] : 'unit → 'unit ;
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  (* Maybe inline? *)
  Definition DEM_CCA_loc :=
    DEM_loc :|: KEY_loc.

  #[program] Definition DEM_CCA_pkg b :
    package DEM_CCA_loc [interface] DEM_CCA_out :=
    {package (par (DEM b) (ID IGEN)) ∘ KEY }.
  Next Obligation.
    ssprove_valid.
    10:{
      unfold DEM_CCA_out, IGEN.
      rewrite fsetUC.
      rewrite -fset_cat. simpl.
      apply fsubsetxx.
    }
    9:{
      rewrite fsetUC.
      instantiate (1 := fset [:: _ ; _ ]).
      rewrite -fset_cat. simpl.
      apply fsubsetxx.
    }
    15: apply fsubsetUr.
    14: apply fsubsetUl.
    8:{ erewrite fsetU0. apply fsubsetxx. }
    all: ssprove_valid.
    2-5: unfold DEM_loc.
    6-10: unfold KEY_loc.
    all: ssprove_valid.
    (* Maybe we can automate this better *)
    apply/fdisjointP.
    intros n h.
    rewrite domm_mkfmap in h. simpl in h.
    rewrite domm_ID_fset. rewrite in_fset. simpl.
    (* TODO Rename this guy into invert_seq_in *)
    invert_in_seq h.
    all: reflexivity.
  Qed.

  Definition DEM_CCA : loc_GamePair DEM_CCA_out :=
    λ b,
      if b
      then {locpackage DEM_CCA_pkg true }
      else {locpackage DEM_CCA_pkg false }.

  (** PKE-CCA *)

  Definition PKE_loc := fset [:: pk_loc ; sk_loc ; c_loc ].

  Definition PKE_CCA_out :=
    [interface
      val #[ PKGEN ] : 'unit → 'key ;
      val #[ PKENC ] : 'plain → 'elen × 'clen ;
      val #[ PKDEC ] : 'elen × 'clen → 'plain
    ].

  #[program] Definition PKE_CCA_pkg (ζ : PKE_scheme) b :
    package PKE_loc [interface] PKE_CCA_out :=
    [package
      def #[ PKGEN ] (_ : 'unit) : 'key {
        sk ← get sk_loc ;;
        assert (sk == None) ;;
        '(pk, sk) ← ζ.(PKE_kgen) ;;
        put pk_loc := Some pk ;;
        put sk_loc := Some sk ;;
        ret pk
      } ;
      def #[ PKENC ] (m : 'plain) : 'elen × 'clen {
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        c ← get c_loc ;;
        assert (c == None) ;;
        c ← (
          if b return raw_code _
          then ζ.(PKE_enc) pk m
          else c ← sample uniform i_clen ;; ret (gfin 0, c)
        ) ;;
        put c_loc := Some c ;;
        ret c
      } ;
      def #[ PKDEC ] (c' : 'elen × 'clen) : 'plain {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        c ← get c_loc ;;
        assert (Some c' != c) ;;
        m ← ζ.(PKE_dec) sk c' ;;
        ret m
      }
    ].
  Next Obligation.
    ssprove_valid.
    (* TODO A hint to deal with this case *)
    destruct x1. ssprove_valid.
  Qed.

  Definition PKE_CCA (ζ : PKE_scheme) : loc_GamePair PKE_CCA_out :=
    λ b,
      if b
      then {locpackage PKE_CCA_pkg ζ true }
      else {locpackage PKE_CCA_pkg ζ false }.

  (** MOD-CCA *)

  Definition MOD_CCA_loc :=
    fset [:: pk_loc ; c_loc ].

  Definition MOD_CCA_in :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key ;
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  Definition MOD_CCA_out :=
    PKE_CCA_out.

  #[program] Definition MOD_CCA (ζ : PKE_scheme) :
    package MOD_CCA_loc MOD_CCA_in MOD_CCA_out :=
    [package
      def #[ PKGEN ] (_ : 'unit) : 'key {
        #import {sig #[ KEMGEN ] : 'unit → 'key } as KEMGEN ;;
        pk ← get pk_loc ;;
        assert (pk == None) ;;
        pk ← KEMGEN Datatypes.tt ;;
        ret pk
      } ;
      def #[ PKENC ] (m : 'plain) : 'elen × 'clen {
        #import {sig #[ ENCAP ] : 'unit → 'elen } as ENCAP ;;
        #import {sig #[ ENC ] : 'plain → 'clen } as ENC ;;
        pk ← get pk_loc ;;
        assert (isSome pk) ;;
        c ← get c_loc ;;
        assert (c ==  None) ;;
        c₁ ← ENCAP Datatypes.tt ;;
        c₂ ← ENC m ;;
        put c_loc := Some (c₁, c₂) ;;
        ret (c₁, c₂)
      } ;
      def #[ PKDEC ] (c' : 'elen × 'clen) : 'plain {
        #import {sig #[ DECAP ] : 'elen → 'key } as DECAP ;;
        #import {sig #[ DEC ] : 'clen → 'plain } as DEC ;;
        pk ← get pk_loc ;;
        assert (isSome pk) ;;
        c ← get c_loc ;;
        assert (c != Some c') ;;
        let '(c'₁, c'₂) := c' in
        if testSome (λ '(c₁, c₂), c'₁ == c₁) c
        then (
          m ← DEC c'₂ ;;
          ret m
        )
        else (
          k' ← DECAP c'₁ ;;
          m ← θ.(DEM_dec) k' c'₂ ;;
          ret m
        )
      }
    ].
  Next Obligation.
    ssprove_valid.
    destruct x. ssprove_valid.
  Qed.

  (** PKE scheme instance *)
  #[program] Definition KEM_DEM : PKE_scheme := {|
    PKE_kgen := η.(KEM_kgen) ;
    PKE_enc := λ pk m, {code
      '(k, c₁) ← η.(KEM_encap) pk ;;
      c₂ ← θ.(DEM_enc) k m ;;
      ret (c₁, c₂)
    } ;
    PKE_dec := λ sk c, {code
      let '(c₁, c₂) := c in
      k ← η.(KEM_decap) sk c₁ ;;
      m ← θ.(DEM_dec) k c₂ ;;
      ret m
    }
  |}.
  Next Obligation.
    ssprove_valid. destruct x. ssprove_valid.
  Qed.
  Next Obligation.
    ssprove_valid.
  Qed.

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

  #[program] Definition Aux b : package PKE_loc [interface] PKE_CCA_out :=
    {package (MOD_CCA KEM_DEM ∘ par (KEM b) (DEM b) ∘ KEY) }.
  Next Obligation.
    ssprove_valid.
  Admitted.

  Transparent mkfmap mkdef.

  (* TODO MOVE *)
  Lemma code_link_assert :
    ∀ b p,
      code_link (assert b) p = assert b.
  Proof.
    intros b p.
    unfold assert. rewrite code_link_if. cbn. reflexivity.
  Qed.

  Lemma PKE_CCA_perf_false :
      (PKE_CCA KEM_DEM false) ≈₀ Aux false.
      (* (MOD_CCA KEM_DEM ∘ par (KEM b) (DEM b) ∘ KEY). *)
  Proof.
    unfold Aux.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    (* intros id So To m hin.
    invert_interface_in hin.
    all: rewrite ?get_op_default_link.
    all: unfold get_op_default.
    all: lookup_op_squeeze.
    all: lookup_op_squeeze.
    all: cbn. *)
    (* TODO The following should now account for assert and #assert probably
       or maybe is it bind?
    *)
    all: ssprove_code_link_commute.
    all: simpl.
    all: simplify_linking.
    (* We are now in the realm of program logic *)
    - setoid_rewrite code_link_bind. cbn.
      simplify_linking.
      setoid_rewrite code_link_assert.
      setoid_rewrite code_link_bind.
      setoid_rewrite code_link_assert.
      setoid_rewrite code_link_bind.
      (* We have again this erefl that appears because of assertD
        if I cannot prevent them from appearing, then I should deal with
        them in a better way. The best would be to bypass them by treating
        assertD as a special case, don't know if possible.

        ssprove_code_link_commute can probably become some code_link_simplify
        and not check the match thing.

        But first do the keying/keyed thing!
      *)
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
      fdisjoint LA PKE_loc →
      Advantage (PKE_CCA KEM_DEM) A <=
      Advantage KEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (ID KEM_out) (DEM true)) +
      Advantage DEM_CCA (A ∘ (MOD_CCA KEM_DEM) ∘ par (KEM false) (ID DEM_out)).
  Proof.
    intros LA A hA hd.
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