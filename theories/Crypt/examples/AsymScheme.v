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
  pkg_core_definition choice_code pkg_composition pkg_rhl
  Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.

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

  (* chX is the choice_code in bijection with X  *)
  (* Parameters chPlain chCipher chPubKey chSecKey : choice_code. *)
  Parameter Plain_pos : Positive #|Plain|.
  Parameter Cipher_pos : Positive #|Cipher|.
  Parameter PubKey_pos : Positive #|PubKey|.
  Parameter SecKey_pos : Positive #|SecKey|.

  #[local] Existing Instance Plain_pos.
  #[local] Existing Instance Cipher_pos.
  #[local] Existing Instance PubKey_pos.
  #[local] Existing Instance SecKey_pos.

  Definition chPlain := 'fin #|Plain|.
  Definition chCipher := 'fin #|Cipher|.
  Definition chPubKey := 'fin #|PubKey|.
  Definition chSecKey := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (chPubKey ; 1%N).
  Definition sk_loc : Location := (chSecKey ; 2%N).
  Definition m_loc  : Location := (chPlain ; 3%N).
  Definition c_loc  : Location := (chCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)
  Definition getpk_id : nat := 42. (* routine to get the public key *)

  (* Key Generation *)
  Parameter KeyGen :
    ∀ {L : {fset Location}},
      code L [interface] (chPubKey × chSecKey).

  (* Encryption algorithm *)
  Parameter Enc :
    ∀ {L : {fset Location}} (pk : chPubKey) (m : chPlain),
      code L [interface] chCipher.

  (* Decryption algorithm *)
  Parameter Dec_open :
    ∀ {L : {fset Location}} (sk : chSecKey) (c : chCipher),
      code L [interface] chPlain.

  Notation " 'plain " := chPlain (in custom pack_type at level 2).
  Notation " 'cipher " :=  chCipher (in custom pack_type at level 2).
  Notation " 'pubkey " :=  chPubKey (in custom pack_type at level 2).

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
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain × 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id] ( mL_mR : 'plain × 'plain ) : 'cipher
      {
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk (fst mL_mR) ;;
        ret c
      }
    ].

  Definition L_pk_cpa_R :
    package
      L_locs
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain × 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id] ( mL_mR : 'plain × 'plain ) : 'cipher
      {
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk (snd mL_mR) ;;
        ret c
      }
    ].

  Definition cpa_L_vs_R :
    loc_GamePair [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id] : 'plain × 'plain → 'cipher
    ] :=
    λ b, if b then {locpackage L_pk_cpa_L} else {locpackage L_pk_cpa_R}.

  (** [The Joy of Cryptography] Definition 15.1

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition CPA_security : Prop :=
    ∀ LA A,
      ValidPackage LA [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain × 'plain → 'cipher
      ] A_export A →
      fdisjoint LA (cpa_L_vs_R true).(locs) →
      fdisjoint LA (cpa_L_vs_R false).(locs) →
      Advantage cpa_L_vs_R A = 0.

  (* Define what it means for an asymmetric encryption scheme to: *)
  (** HAVE PSEUDORND CIPHERTEXT IN PRESENCE OF CHOSEN PLAINTEXT ATTACKS **)

  Definition L_pk_cpa_real :
    package L_locs
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id] (m : 'plain) : 'cipher
      {
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk m ;;
        ret c
      }
    ].

  Definition L_pk_cpa_rand :
    package L_locs
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id] (m : 'plain) : 'cipher
      {
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← sample uniform i_cipher ;;
        ret c
      }
    ].

  Definition cpa_real_vs_rand :
    loc_GamePair [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id] : 'plain → 'cipher
    ] :=
    λ b, if b then {locpackage L_pk_cpa_real } else {locpackage L_pk_cpa_rand }.

  (** [The Joy of Cryptography] Definition 15.2

    A public-key encryption scheme has pseudornd ciphertext against
    chosen-plaintext attacks when the following holds.
  *)

  Definition CPA_rnd_cipher : Prop :=
    ∀ LA A,
      ValidPackage LA [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain → 'cipher
      ] A_export A →
      fdisjoint LA (cpa_real_vs_rand true).(locs) →
      fdisjoint LA (cpa_real_vs_rand false).(locs) →
      Advantage cpa_real_vs_rand A = 0.

  (* Define what it means for an asymmetric encryption scheme to have: *)
  (** ONE-TIME SECRECY **)

  Definition L_locs_counter := fset [:: counter_loc ; pk_loc ; sk_loc ].

  Definition L_pk_ots_L :
    package L_locs_counter
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain × 'plain → 'cipher
      ]
    :=
    [package
      #def #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;
      #def #[challenge_id] (mL_mR : 'plain × 'plain) : 'cipher
      {
        count ← get counter_loc ;;
        #put counter_loc := (count + 1)%N;;
        #assert (count == 0)%N ;;
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk (fst mL_mR) ;;
        ret c
      }
    ].

  Definition L_pk_ots_R :
    package L_locs_counter
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] : 'plain × 'plain → 'cipher
      ]
    :=
    [package
      #def #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;
      #def #[challenge_id] (mL_mR :  'plain × 'plain) : 'cipher
      {
        count ← get counter_loc ;;
        #put counter_loc := (count + 1)%N;;
        #assert (count == 0)%N ;;
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk (snd mL_mR) ;;
        ret c
      }
    ].

  Definition ots_L_vs_R :
    loc_GamePair [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id] :'plain × 'plain → 'cipher
    ] :=
    λ b, if b then {locpackage L_pk_ots_L } else {locpackage L_pk_ots_R }.

  (** [The Joy of Cryptography] Definition 15.4

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition OT_secrecy : Prop :=
    ∀ LA A,
      ValidPackage LA [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id] :'plain × 'plain → 'option 'cipher
      ] A_export A →
      fdisjoint LA (ots_L_vs_R true).(locs) →
      fdisjoint LA (ots_L_vs_R false).(locs) →
      Advantage ots_L_vs_R A = 0.

  (*  *)

  Definition L_pk_ots_real :
    package L_locs_counter
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id'] : 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id'] (m : 'plain) : 'cipher
      {
        count ← get counter_loc ;;
        #put counter_loc := (count + 1)%N;;
        #assert (count == 0)%N ;;
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← Enc pk m ;;
        ret c
      }
    ].

  Definition L_pk_ots_rnd :
    package L_locs_counter
      [interface]
      [interface
        #val #[getpk_id] : 'unit → 'pubkey ;
        #val #[challenge_id'] : 'plain → 'cipher
      ]
    :=
    [package
      #def  #[getpk_id] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      } ;

      #def #[challenge_id'] (m : 'plain) : 'cipher
      {
        count ← get counter_loc ;;
        #put counter_loc := (count + 1)%N;;
        #assert (count == 0)%N ;;
        '(pk, sk) ← KeyGen ;;
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        c ← sample uniform i_cipher ;;
        ret c
      }
    ].

  Definition ots_real_vs_rnd :
    loc_GamePair [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ] :=
    λ b, if b then {locpackage L_pk_ots_real } else {locpackage L_pk_ots_rnd }.

End AsymmetricScheme.
