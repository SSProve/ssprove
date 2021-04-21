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
  Definition c_loc : Location := ('option ('elen × 'clen) ; 2%N).

  (** Uniform distributions *)
  Definition i_key := key_length.
  Definition i_clen := clen.

  (** PKE scheme
    For it to be used in PKE-CCA I specialise the definitions to use locations
    PKE_loc.
  *)
  Definition PKE_loc := fset [:: pk_loc ; sk_loc ; c_loc ].

  Record PKE_scheme := {
    PKE_kgen : code PKE_loc [interface] (chProd 'key 'key) ;
    PKE_enc : 'key → 'plain → code PKE_loc [interface] (chProd 'elen 'clen) ;
    (* clen is global *)
    PKE_dec : 'key → chProd 'elen 'clen → code PKE_loc [interface] 'plain
  }.

  (** KEM scheme *)
  Record KEM_scheme := {
    KEM_loc : {fset Location } ;
    KEM_kgen : code KEM_loc [interface] (chProd 'key 'key) ;
    KEM_encap : 'key → code KEM_loc [interface] (chProd 'key 'elen) ;
    KEM_decap : 'key → 'elen → code KEM_loc [interface] 'key
  }.

  (** DEM scheme *)
  Record DEM_scheme := {
    DEM_loc : {fset Location } ;
    DEM_enc : 'key → 'plain → code DEM_loc [interface] 'clen ;
    DEM_dec : 'key → 'clen → code DEM_loc [interface] 'plain
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

  Definition KEM (b : bool) : package PKE_loc KEM_in KEM_out.
  Admitted.

  (** KEM-CCA game *)

  Definition KEM_CCA_out :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key ;
      val #[GET] : 'unit → 'key
    ].

  Opaque mkfmap mkdef.

  #[program] Definition KEM_CCA_pkg b :
    package (PKE_loc :|: KEY_loc) [interface] KEM_CCA_out :=
    {package (par (KEM b) (ID [interface val #[GET] : 'unit → 'key ])) ∘ KEY }.
  Next Obligation.
    ssprove_valid.
    - unfold FDisjoint. (* Unclear this class is of any use! Same for Parable
        Especially in packages hint DB
      *)
      admit.
    - (* Might be automated *)
      intros n o₀ o₁ h₀ h₁.
      invert_interface_in h₀.
      invert_interface_in h₁.
      reflexivity.
    - erewrite fsetU0. apply fsubsetxx.
    - unfold KEM_CCA_out, KEM_out.
      rewrite -fset_cat. simpl. apply fsubsetxx.
    - rewrite -fset_cat. simpl. (* ssprove_valid. *)
      (* TODO It seems to unfold even valid_package_ext, why?? *)
      (* eapply valid_package_cons. *)
      (* eapply valid_package_cons_upto. *)
      (* The order is wrong, but also it unfolded KEY, I would have liked it
          not to do it. Should I add a second option for coercions to
          use an upto version?
      *)
      admit.
  Admitted.

  Definition KEM_CCA : loc_GamePair KEM_CCA_out :=
    λ b,
      if b
      then {locpackage KEM_CCA_pkg true }
      else {locpackage KEM_CCA_pkg false }.

  (** DEM package *)

  Definition DEM_in :=
    [interface
      val #[ GET ] : 'unit → 'key
    ].

  Definition DEM_out :=
    [interface
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  Definition DEM (b : bool) : package PKE_loc DEM_in DEM_out.
  Admitted.

  (** PKE-CCA *)

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

  (** PKE scheme instance *)
  #[program] Definition KEM_DEM : PKE_scheme := {|
    PKE_kgen := {code η.(KEM_kgen)} ;
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
    (* See what we want as locations. If they are the same, the {code} case
      will not be necessary.
    *)
  Admitted.
  Next Obligation.
    ssprove_valid.
    - admit.
    - destruct x. ssprove_valid. admit.
  Admitted.
  Next Obligation.
    ssprove_valid. all: admit.
  Admitted.

  (** Security theorem *)

  (* Since in the theorem we use the PKE of construction 23, we can probably
    directly specialise things?
  *)

  (* Theorem PKE_security :
    ∀ LA A,
      ValidPackage LA PKE_CCA_export A_export A →
      fdisjoint LA PKE_loc →
      Advantage PKE_CCA A <=
      Advantage KEM_CCA (A ∘ MOC_CCA ∘ par (ID KEM_out) DEM₀) +
      Advantage DEM_CCA (A ∘ MOD_CCA ∘ par KEM₁ (ID DEM_out)).
  Abort. *)

End KEMDEM.