(** KEM-DEM example *)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude.

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
  Definition c_loc : Location := ('option ('elen × 'clen) ; 2%N).

  (** Uniform distributions *)
  Definition i_key := key_length.
  Definition i_clen := clen.

  (** PKE scheme *)
  Record PKE_scheme := {
    PKE_loc : {fset Location } ;
    PKE_kgen : code PKE_loc [interface] (chProd 'key 'key) ;
    PKE_enc : 'key → 'plain → code PKE_loc [interface] (chProd 'elen 'clen) ;
    (* clen is global *)
    PKE_dec : 'key → chProd 'elen 'clen → code PKE_loc [interface] 'plain
  }.

  (** KEM scheme *)
  Record KEM_scheme := {
    KEM_loc : {fset Location } ;
    KEM_kgen : code KEM_loc [interface] ('key × 'key) ;
    KEM_encap : 'key → code KEM_loc [interface] 'elen ;
    KEM_decap : 'key → 'elen → code KEM_loc [interface] 'key
  }.

  (** DEM scheme *)
  Record DEM_scheme := {
    DEM_loc : {fset Location } ;
    DEM_enc : 'key → 'plain → code DEM_loc [interface] 'clen ;
    DEM_dec : 'key → 'clen → code DEM_loc [interface] 'plain
  }.

  (** KEY Package *)

  Definition KEY :
    package
      (fset [:: key ])
      [interface]
      [interface
        val #[ GEN ] : 'unit → 'unit ;
        val #[ SET ] : 'key → 'unit ;
        val #[ GET ] : 'unit → 'key
      ] :=
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

  (** Assumed KEM game *)
  (* TODO Not sure if I should do this, or simply assusme some code. *)
  Definition KEM_export :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key
    ].

  Context (KEM₀ : loc_package [interface val #[ SET ] : 'key → 'unit ] KEM_export).
  Context (KEM₁ : loc_package [interface val #[ GEN ] : 'unit → 'unit ] KEM_export).

  (** Assumed DEM game *)
  Definition DEM_export :=
    [interface
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  Context (DEM₀ : loc_package [interface val #[ GET ] : 'unit → 'key ] DEM_export).
  Context (DEM₁ : loc_package [interface val #[ GET ] : 'unit → 'key ] DEM_export).

  (** PKE-CCA *)

  Opaque ValidPackage mkfmap pkg_composition.mkdef.

  (* Probably a loc_GamePair *)
  #[program] Definition PKE_CCA (ζ : PKE_scheme) b :
    package
      (fset [:: pk_loc ; sk_loc ; c_loc ])
      [interface]
      [interface
        val #[ PKGEN ] : 'unit → 'key ;
        val #[ PKENC ] : 'plain → 'elen × 'clen ;
        val #[ PKDEC ] : 'elen × 'clen → 'plain
      ] :=
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
    exact _.
  Qed.
  Next Obligation.
    (* TODO Have a tactic that does most of the work. *)
    eapply valid_package_cons.
    3:{ unfold "\notin" ; rewrite imfset_fset ; rewrite in_fset ; eauto. }
    1: eapply valid_package_cons.
    3:{ unfold "\notin" ; rewrite imfset_fset ; rewrite in_fset ; eauto. }
    1: eapply valid_package1.
    - intro. eapply valid_getr. 1: auto_in_fset.
      intro. Fail eapply valid_assertD. admit.
    - intro. eapply valid_getr. 1: auto_in_fset.
      intro. Fail eapply valid_assertD. admit.
      (* eapply valid_code_from_class. exact _. *)
    - intro. eapply valid_getr. 1: auto_in_fset.
      intro. eapply valid_bind.
      1:{ eapply valid_code_from_class. exact _. }
      intro. eapply valid_bind.
      + (* NEED to update PKE_kgen to use these locs I guess... *)
        admit.
      + intros []. eapply valid_code_from_class. exact _.
  Admitted.

  (** MOD-CCA *)

  Definition MOD_CCA :
    package
      (fset [:: (* TODO *) ])
      [interface (* TODO *) ]
      [interface
        val #[ PKGEN ] : 'unit → 'key ;
        val #[ PKENC ] : 'plain → 'clen ;
        val #[ PKDEC ] : 'elen × 'clen → 'plain
      ].
  Abort.

  (** Security theorem *)

  (* Since in the theorem we use the PKE of construction 23, we can probably
    directly specialise things?
  *)

  (* Theorem PKE_security :
    ∀ LA A,
      ValidPackage LA PKE_CCA_export A_export A →
      fdisjoint LA (PKE_CCA true).(locs) →
      fdisjoint LA (PKE_CCA false).(locs) →
      Advantage PKE_CCA A <=
      Advantage KEM_CCA (A ∘ MOC_CCA ∘ par (ID KEM_export) DEM₀) +
      Advantage DEM_CCA (A ∘ MOD_CCA ∘ par KEM₁ (ID DEM_export)).
  Abort. *)

End KEMDEM.