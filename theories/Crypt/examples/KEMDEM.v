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
(* TODO Same as finmap.oextract but with a better name? *)
Definition getSome {A} (o : option A) :
  isSome o → A.
Proof.
  intro h.
  destruct o. 2: discriminate.
  assumption.
Defined.

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

  Definition KEM_in :=
    [interface
      val #[ SET ] : 'key → 'unit ;
      val #[ GEN ] : 'unit → 'unit
    ].

  Definition KEM_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key
    ].

  (* TODO MOVE *)
  Lemma valid_scheme :
    ∀ A L I c,
      @valid_code fset0 [interface] A c →
      valid_code L I c.
  Proof.
    intros A L I c h.
    eapply valid_injectMap. 2: eapply valid_injectLocations.
    1-2: eapply fsub0set.
    rewrite -fset0E in h. auto.
  Qed.

  (* Export? *)
  Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
    eapply valid_scheme ; eapply c.(prog_valid)
    : typeclass_instances packages.

  (* TODO Find a way to make this not mandatory *)
  Opaque mkfmap mkdef.

  #[program] Definition KEM (b : bool) : package KEM_loc KEM_in KEM_out :=
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
    (* fset [:: pk_loc ; sk_loc ; ce_loc ; key ]. *)

  (* TODO MOVE *)
  Lemma domm_ID :
    ∀ I, domm (ID I) = fset (unzip1 I).
  Proof.
    intros I.
    apply eq_fset. intro x.
    rewrite in_fset. rewrite mem_domm.
    unfold ID. rewrite mkfmapE. rewrite getm_def_map_dep.
    rewrite -mkfmapE.
    rewrite -domm_mkfmap. rewrite mem_domm.
    destruct (mkfmap I x) eqn:e.
    - rewrite e. simpl. reflexivity.
    - rewrite e. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma domm_ID_fset :
    ∀ I, domm (ID (fset I)) = fset (unzip1 I).
  Proof.
    intros I.
    rewrite domm_ID.
    apply eq_fset. intro x.
    rewrite !in_fset.
    unfold unzip1.
    apply/mapP.
    destruct (x \in [seq i.1 | i <- I]) eqn: e.
    - move: e => /mapP e. simpl in e. destruct e as [? h ?]. subst.
      simpl. eexists. 2: reflexivity.
      rewrite in_fset. auto.
    - move: e => /mapP e. simpl in e.
      intro h. apply e.
      destruct h as [? h ?]. rewrite in_fset in h.
      eexists. all: eauto.
  Qed.

  #[program] Definition KEM_CCA_pkg b :
    package KEM_CCA_loc [interface] KEM_CCA_out :=
    {package (par (KEM b) (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY }.
  Next Obligation.
    ssprove_valid.
    6: destruct x2. 6: ssprove_valid.
    11: destruct x1. 11: ssprove_valid.
    15:{
      unfold KEM_CCA_out. rewrite -fset_cat. simpl.
      apply fsubsetxx.
    }
    14:{
      instantiate (1 := fset [:: _ ; _ ]).
      erewrite <- fset_cat. simpl.
      apply fsubsetxx.
    }
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
    (* TODO Rename this guy into invert_seq_in *)
    _invert_interface_in h.
    all: reflexivity.
  Qed.

  Definition KEM_CCA : loc_GamePair KEM_CCA_out :=
    λ b,
      if b
      then {locpackage KEM_CCA_pkg true }
      else {locpackage KEM_CCA_pkg false }.

  (** DEM package *)

  Definition DEM_loc := fset [:: cc_loc ].

  Definition DEM_in :=
    [interface
      val #[ GET ] : 'unit → 'key
    ].

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
    {package (par (DEM b) (ID [interface val #[ GEN ] : 'unit → 'unit ])) ∘ KEY }.
  Next Obligation.
    ssprove_valid.
    10:{
      unfold DEM_CCA_out.
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
    _invert_interface_in h.
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

  (* TODO MOVE *)
  Definition testSome {A} (P : A → bool) (o : option A) : bool :=
    match o with
    | Some a => P a
    | None => false
    end.

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

  (* Warning, will probably have extra hyps *)
  Lemma single_key_a :
    ∀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY in
      let K₁ := (par CK₁ (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY in
      let D₀ := (par (ID [interface val #[ GEN ] : 'unit → 'unit ]) CD₀) ∘ KEY in
      let D₁ := (par (ID [interface val #[ GEN ] : 'unit → 'unit ]) CD₁) ∘ KEY in
      AdvantageE ((par CK₀ CD₀) ∘ KEY) ((par CK₁ CD₁) ∘ KEY) A <=
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₀)) +
      AdvantageE D₀ D₁ (A ∘ (par CK₁ (ID ED))).
  Admitted.

  (* Warning, will probably have extra hyps *)
  (* See if we need this one too before proving it. *)
  Lemma single_key_b :
    ∀ CK₀ CK₁ CD₀ CD₁ EK ED A,
      let K₀ := (par CK₀ (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY in
      let K₁ := (par CK₁ (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY in
      let D₀ := (par (ID [interface val #[ GEN ] : 'unit → 'unit ]) CD₀) ∘ KEY in
      let D₁ := (par (ID [interface val #[ GEN ] : 'unit → 'unit ]) CD₁) ∘ KEY in
      AdvantageE ((par CK₀ CD₀) ∘ KEY) ((par CK₀ CD₁) ∘ KEY) A <=
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₀)) +
      AdvantageE D₀ D₁ (A ∘ (par CK₁ (ID ED))) +
      AdvantageE K₀ K₁ (A ∘ (par (ID EK) CD₁)).
  Admitted.

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

  (* TODO MOVE *)
  Lemma adv_equiv_sym :
    ∀ L₀ L₁ E G₀ G₁ h₀ h₁ ε,
      @adv_equiv L₀ L₁ E G₀ G₁ h₀ h₁ ε →
      adv_equiv G₁ G₀ ε.
  Proof.
    intros L₀ L₁ E G₀ G₁ h₀ h₁ ε h.
    intros LA A hA hd₁ hd₀.
    rewrite Advantage_sym.
    eapply h. all: eauto.
  Qed.

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
    rewrite PKE_CCA_perf_false.
    2-3: admit.
    rewrite PKE_CCA_perf_true.
    2-3: admit.
    rewrite GRing.addr0. rewrite GRing.add0r.
    (* Maybe I can state Lemma 19 of the SSP paper using advantage directly
        this way I don't have to type the packages.
        We could also inline the proof... Let's see which is better.
    *)
  Admitted.

End KEMDEM.