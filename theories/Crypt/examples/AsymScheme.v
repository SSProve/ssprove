(** Asymmetric encryption schemes

  In the stateful and probabilistic setting.
  This module defines:

    1. CPA_security    "security under chosen plaintext attacks"
    2. CPA_rnd_cipher  "cipher looks random"
    3. OT_secrecy      "one-time secrecy"
    4. OT_rnd_cipher   "cipher looks random when the key is used only once"

    4. -> 3. -> 2. -> 1

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl
  Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Import PackageNotation.

Local Open Scope ring_scope.


(* ASymmetric Schemes *)
Module Type AsymmetricSchemeParams.

  Parameter SecurityParameter : choiceType.
  Parameters Plain Cipher PubKey SecKey : finType.
  Parameter plain0 : Plain.
  Parameter cipher0 : Cipher.
  Parameter pub0 : PubKey.
  Parameter sec0 : SecKey.

End AsymmetricSchemeParams.

(** algorithms for Key Generation, Encryption and Decryption  **)
Module Type AsymmetricSchemeAlgorithms (π : AsymmetricSchemeParams).

  Import π.

  Local Open Scope package_scope.

  (* chX is the chUniverse in bijection with X  *)
  (* Parameters choicePlain choiceCipher choicePubKey choiceSecKey : chUniverse. *)
  Parameter Plain_pos : Positive #|Plain|.
  Parameter Cipher_pos : Positive #|Cipher|.
  Parameter PubKey_pos : Positive #|PubKey|.
  Parameter SecKey_pos : Positive #|SecKey|.

  #[local] Existing Instance Plain_pos.
  #[local] Existing Instance Cipher_pos.
  #[local] Existing Instance PubKey_pos.
  #[local] Existing Instance SecKey_pos.

  Definition choicePlain := 'fin #|Plain|.
  Definition choiceCipher := 'fin #|Cipher|.
  Definition choicePubKey := 'fin #|PubKey|.
  Definition choiceSecKey := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (choicePubKey ; 1%N).
  Definition sk_loc : Location := (choiceSecKey ; 2%N).
  Definition m_loc  : Location := (choicePlain ; 3%N).
  Definition c_loc  : Location := (choiceCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)

  (* Key Generation *)
  Parameter KeyGen :
    ∀ {L : {fset Location}},
      code L [interface] (choicePubKey × choiceSecKey).

  (* Encryption algorithm *)
  Parameter Enc :
    ∀ {L : {fset Location}} (pk : choicePubKey) (m : choicePlain),
      code L [interface] choiceCipher.

  (* Decryption algorithm *)
  Parameter Dec_open :
    ∀ {L : {fset Location}} (sk : choiceSecKey) (c : choiceCipher),
      code L fset0 choicePlain.

  Notation " 'chSecurityParameter' " := ('nat) (in custom pack_type at level 2).
  Notation " 'chPlain' " := choicePlain (in custom pack_type at level 2).
  Notation " 'chCipher' " :=  choiceCipher (in custom pack_type at level 2).
  Notation " 'chPubKey' " := choicePubKey (in custom pack_type at level 2).
  Notation " 'chSecKey' " := choiceSecKey (in custom pack_type at level 2).

End AsymmetricSchemeAlgorithms.

(* A Module for Asymmetric Encryption Schemes, inspired to Joy of Crypto *)
Module AsymmetricScheme (π : AsymmetricSchemeParams)
                        (Alg : AsymmetricSchemeAlgorithms π).

  Import π.
  Import Alg.

  (* Compatibitlity *)
  Definition i_plain := #|Plain|.
  Definition i_cipher := #|Cipher|.
  Definition i_pk := #|PubKey|.
  Definition i_sk := #|SecKey|.
  Definition i_bool := 2.

  Local Open Scope package_scope.

   (* Define what it means for an asymmetric encryption scheme to be: *)
   (** SECURE AGAINST CHOSEN-PLAINTEXT ATTACKS **)

  Definition L_locs : { fset Location } := fset [:: pk_loc ; sk_loc ].

  (* TODO INVESTIGATE:
    If I put _ instead of L_locs, the following loops.
    So probably some problem with how I try to infer \in?
  *)
  Definition L_pk_cpa_L :
    package
      L_locs
      [interface]
      [interface val #[challenge_id] : chPlain × chPlain → chCipher ] :=
    [package
      def #[challenge_id] ( mL_mR : chPlain × chPlain ) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
        put pk_loc := pk ;;
        put sk_loc := sk ;;
        c ← Enc pk (fst mL_mR) ;;
        ret c
      }
    ].

  Definition L_pk_cpa_R :
    package
      L_locs
      [interface]
      [interface val #[challenge_id] : chPlain × chPlain → chCipher ] :=
    [package
      def #[challenge_id] ( mL_mR : chPlain × chPlain ) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
        put pk_loc := pk ;;
        put sk_loc := sk ;;
        c ← Enc pk (snd mL_mR) ;;
        ret c
      }
    ].

  Definition cpa_L_vs_R :
    loc_GamePair [interface val #[challenge_id] : chPlain × chPlain → chCipher] :=
    λ b, if b then {locpackage L_pk_cpa_L} else {locpackage L_pk_cpa_R}.

  (** [The Joy of Cryptography] Definition 15.1

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition CPA_security : Prop :=
    ∀ LA A,
      ValidPackage LA [interface val #[challenge_id] : chPlain × chPlain → chCipher] A_export A →
      fdisjoint LA (cpa_L_vs_R true).(locs) →
      fdisjoint LA (cpa_L_vs_R false).(locs) →
      Advantage cpa_L_vs_R A = 0.

  (* Define what it means for an asymmetric encryption scheme to: *)
  (** HAVE PSEUDORND CIPHERTEXT IN PRESENCE OF CHOSEN PLAINTEXT ATTACKS **)

  Definition L_pk_cpa_real :
    package L_locs
      [interface]
      [interface val #[challenge_id] : chPlain → chCipher ] :=
    [package
      def #[challenge_id] (m : chPlain) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
        put pk_loc := pk ;;
        put sk_loc := sk ;;
        c ← Enc pk m ;;
        ret c
      }
    ].

  Definition L_pk_cpa_rand :
    package L_locs
      [interface]
      [interface val #[challenge_id] : chPlain → chCipher ] :=
    [package
      def #[challenge_id] (m : chPlain) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
         put pk_loc := pk ;;
         put sk_loc := sk ;;
         c ← sample uniform i_cipher ;;
         ret c
      }
    ].

  Definition cpa_real_vs_rand :
    loc_GamePair [interface val #[challenge_id] : chPlain → chCipher] :=
    λ b, if b then {locpackage L_pk_cpa_real } else {locpackage L_pk_cpa_rand }.

  (** [The Joy of Cryptography] Definition 15.2

    A public-key encryption scheme has pseudornd ciphertext against
    chosen-plaintext attacks when the following holds.
  *)

  Definition CPA_rnd_cipher : Prop :=
    ∀ LA A,
      ValidPackage LA [interface val #[challenge_id] : chPlain → chCipher] A_export A →
      fdisjoint LA (cpa_real_vs_rand true).(locs) →
      fdisjoint LA (cpa_real_vs_rand false).(locs) →
      Advantage cpa_real_vs_rand A = 0.

  (* Define what it means for an asymmetric encryption scheme to have: *)
  (** ONE-TIME SECRECY **)

  Definition L_locs_counter := fset [:: counter_loc ; pk_loc ; sk_loc].

  Definition L_pk_ots_L :
    package L_locs_counter
      [interface]
      [interface val #[challenge_id] : chPlain × chPlain → 'option chCipher ] :=
    [package
      def #[challenge_id] ( mL_mR : chPlain × chPlain ) : 'option chCipher
      {
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N;;
        if ((count == 0)%N) then
          '(pk, sk) ← KeyGen ;;
          put pk_loc := pk ;;
          put sk_loc := sk ;;
          c ← Enc pk (fst mL_mR) ;;
          ret (some c)
        else ret None
      }
    ].

  Definition L_pk_ots_R :
    package L_locs_counter
      [interface]
      [interface val #[challenge_id] : chPlain × chPlain → 'option chCipher ] :=
    [package
      def #[challenge_id] ( mL_mR :  chPlain × chPlain ) : 'option chCipher
      {
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N;;
        if ((count == 0)%N) then
          '(pk, sk) ← KeyGen ;;
          put pk_loc := pk ;;
          put sk_loc := sk ;;
          c ← Enc pk (snd mL_mR) ;;
          ret (some c)
        else ret None
      }
    ].

  Definition ots_L_vs_R :
    loc_GamePair [interface
      val #[challenge_id] :chPlain × chPlain → 'option chCipher
    ] :=
    λ b, if b then {locpackage L_pk_ots_L } else {locpackage L_pk_ots_R }.

  (** [The Joy of Cryptography] Definition 15.4

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition OT_secrecy : Prop :=
    ∀ LA A,
      ValidPackage LA [interface
        val #[challenge_id] :chPlain × chPlain → 'option chCipher
      ] A_export A →
      fdisjoint LA (ots_L_vs_R true).(locs) →
      fdisjoint LA (ots_L_vs_R false).(locs) →
      Advantage ots_L_vs_R A = 0.

  (*  *)

  Definition L_pk_ots_real :
    package L_locs_counter
      [interface]
      [interface val #[challenge_id'] : chPlain → 'option chCipher ] :=
    [package
      def #[challenge_id'] ( m : chPlain  ) : 'option chCipher
      {
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N;;
        if ((count == 0)%N) then
          '(pk, sk) ← KeyGen ;;
          put pk_loc := pk ;;
          put sk_loc := sk ;;
          c ← Enc pk m ;;
          ret (some c)
        else ret None
      }
    ].

  Definition L_pk_ots_rnd :
    package L_locs_counter
      [interface]
      [interface val #[challenge_id'] : chPlain → 'option chCipher ] :=
    [package
      def #[challenge_id'] ( m : chPlain ) : 'option chCipher
      {
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N;;
        if ((count == 0)%N) then
          '(pk, sk) ← KeyGen ;;
          put pk_loc := pk ;;
          put sk_loc := sk ;;
          c ← sample uniform i_cipher ;;
          ret (Some c)
        else ret None
      }
    ].

  Definition ots_real_vs_rnd :
    loc_GamePair [interface val #[challenge_id'] : chPlain → 'option chCipher] :=
    λ b, if b then {locpackage L_pk_ots_real } else {locpackage L_pk_ots_rnd }.

End AsymmetricScheme.
