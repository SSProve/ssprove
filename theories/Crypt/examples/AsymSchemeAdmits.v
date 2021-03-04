(*
    Asymmetric encryption schemes -- stateful and probabilistic setting -- defines :

    1. CPA_security    "security under chosen plaintext attacks"
    2. CPA_rnd_cipher  "cipher looks random"
    3. OT_secrecy      "one-time secrecy"
    4. OT_rnd_cipher   "cipher looks random when the key is used only once"

    4. -> 3. -> 2. -> 1

*)

From Relational Require Import
     OrderEnrichedCategory
     GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     UniformDistrLemmas
     FreeProbProg
     Theta_dens
     RulesStateProb
     UniformStateProb.
From Crypt Require Import
     pkg_core_definition
     pkg_chUniverse
     pkg_composition
     pkg_notation
     pkg_rhl
     Package
     Prelude.


From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.


(* ASymmetric Schemes *)
Module Type AsymmetricSchemeParams.

  Parameter SecurityParameter : choiceType.
  Parameters Plain Cipher PubKey SecKey : finType.
  Parameter plain0 : Plain.
  Parameter cipher0 : Cipher.
  Parameter pub0 : PubKey.
  Parameter sec0 : SecKey.

  (*Rem.: If I don't put these here I get some trubles later... *)

  Parameter probE : Type -> Type.
  Parameter rel_choiceTypes : Type.
  Parameter chEmb : rel_choiceTypes -> choiceType.
  Parameter prob_handler : forall T : choiceType, probE T -> SDistr T.
  Parameter Hch : forall r : rel_choiceTypes, chEmb r.

End AsymmetricSchemeParams.

Module ARules (Aparam : AsymmetricSchemeParams).

  Export Aparam.

  (*: Uniform distributions over Plain, Cipher, Key and bool *)
  Variant Index :=
  | i_plain  : Index
  | i_cipher : Index
  | i_pk     : Index
  | i_sk     : Index
  | i_bool   : Index.


  Module UParam <: UniformParameters.

  Definition Index : Type := Index.
  Definition i0 : Index := i_plain.
  Definition fin_family : Index -> finType := fun i => match i with
                                                   | i_plain   => Plain
                                                   | i_cipher  => Cipher
                                                   | i_pk      => PubKey
                                                   | i_sk      => SecKey
                                                   | i_bool    => bool_finType
                                                   end.

  Definition F_w0 : forall i : Index, (fin_family i).
  Proof.
    case; rewrite /fin_family;
    [exact plain0| exact cipher0 | exact pub0 | exact sec0 | exact false].
  Defined.

  End UParam.

  Module genparam <: RulesParam.

    Definition probE : Type -> Type := probE.
    Definition rel_choiceTypes : Type := rel_choiceTypes.
    Definition chEmb : rel_choiceTypes -> choiceType := chEmb.
    Definition prob_handler : forall T : choiceType, probE T -> SDistr T := prob_handler.
    Definition Hch : forall r : rel_choiceTypes, chEmb r := Hch.

  End genparam.

  Module MyARulesUniform := DerivedRulesUniform genparam UParam.
  Export MyARulesUniform.

End ARules.

(** algorithms for Key Generation, Encryption and Decryption  **)
Module Type AsymmetricSchemeAlgorithms (π : AsymmetricSchemeParams).

  Import π.
  Module asym_rules := (ARules π).
  Export asym_rules.
  Import asym_rules.MyARulesUniform.

  Module MyPackage := Package_Make myparamU.
  Export MyPackage.
  Import PackageNotation.
  Local Open Scope package_scope.

  Definition counter_loc : Location := ('nat; 0%N).
  Definition pk_loc : Location := ('nat; 1%N).
  Definition sk_loc : Location := ('nat; 2%N).
  Definition m_loc  : Location := ('nat; 3%N).
  Definition c_loc  : Location := ('nat; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)


  (* Definition rel_loc : {fset Location} := [fset counter_loc]. *)
  (* Rem.: ; kg_loc ; enc_loc ; dec_loc ; challenge_loc ; pk_loc; sk_loc]. *)

  Definition Plain_len_pos : positive.
  Proof. exists #|Plain|.  apply /card_gt0P. by exists plain0. Defined.

  Definition Cipher_len_pos : positive.
  Proof. exists #|Cipher|. apply /card_gt0P. by exists cipher0. Defined.

  Definition PubKey_len_pos : positive.
  Proof. exists #|PubKey|. apply /card_gt0P. by exists pub0. Defined.

  Definition SecKey_len_pos : positive.
  Proof. exists #|SecKey|. apply /card_gt0P. by exists sec0. Defined.

  Notation " 'chSecurityParameter' " :=
    (chNat) (in custom pack_type at level 2).
  Notation " 'chPlain' " :=
    (chFin Plain_len_pos )
    (in custom pack_type at level 2).
  Notation " 'chCipher' " :=
    (chFin Cipher_len_pos)
    (in custom pack_type at level 2).
  Notation " 'chPubKey' " :=
    (chFin PubKey_len_pos)
    (in custom pack_type at level 2).
  Notation " 'chSecKey' " :=
    (chFin SecKey_len_pos)
    (in custom pack_type at level 2).

  Parameter c2ch : Cipher -> (chFin Cipher_len_pos).
  Parameter ch2c : (chFin Cipher_len_pos) -> Cipher.
  (* *)
  Parameter pk2ch : PubKey -> (chFin PubKey_len_pos).
  Parameter ch2pk : (chFin PubKey_len_pos) -> PubKey.
  (* *)
  Parameter sk2ch : SecKey -> (chFin SecKey_len_pos).
  Parameter ch2sk : (chFin SecKey_len_pos) -> SecKey.
  (* *)
  Parameter m2ch : Plain -> (chFin Plain_len_pos).
  Parameter ch2m : (chFin Plain_len_pos) -> Plain.
  (* *)



  (* Key Generation *)
  Parameter KeyGen : forall { L : {fset Location} }, code L fset0 ((chFin PubKey_len_pos) × (chFin SecKey_len_pos)).


  (* Encryption algorithm *)
  Parameter Enc : forall { L : {fset Location} } (pk : chFin PubKey_len_pos) (m : chFin Plain_len_pos),
      code L fset0 (chFin Cipher_len_pos).

  (* Decryption algorithm *)
  Parameter Dec_open : forall { L : {fset Location} } (sk : chFin SecKey_len_pos) (c : chFin Cipher_len_pos),
      code L fset0 (chFin Plain_len_pos).

End AsymmetricSchemeAlgorithms.


(* A Module for Asymmetric Encryption Schemes, inspired to Joy of Crypto *)
Module AsymmetricScheme (π : AsymmetricSchemeParams)
                        (Alg : AsymmetricSchemeAlgorithms π).


  Import Alg.
  Import PackageNotation.

  Definition U (i : Index) : {rchT : myparamU.rel_choiceTypes & myparamU.probE (myparamU.chEmb rchT)} :=
    (existT (λ rchT : myparamU.rel_choiceTypes, myparamU.probE (myparamU.chEmb rchT))
            (inl (inl i)) (inl (Uni_W i))).

  Local Open Scope package_scope.

  Obligation Tactic := package_obtac.

   (* Define what it means for an asymmetric encryption scheme to be: *)
   (**   *SECURE AGAINST CHOSEN-PLAINTEXT ATTACKS **)

  Definition L_locs : { fset Location } := fset [:: pk_loc; sk_loc ].

  #[program] Definition L_pk_cpa_L_open :
    opackage L_locs
      [interface ]
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

  Definition L_pk_cpa_L : package  [interface ]
                                   [interface val #[challenge_id] : chPlain × chPlain → chCipher].
  Proof. exists L_locs. exact: L_pk_cpa_L_open. Defined.


  #[program] Definition L_pk_cpa_R_open :
    opackage L_locs
             [interface ]
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

  Definition L_pk_cpa_R : package [interface ]
                                  [interface val #[challenge_id] : chPlain × chPlain → chCipher].
  Proof. exists L_locs. exact: L_pk_cpa_R_open. Defined.


  (* Lemma interface_lemma_cpa : *)
  (*   [interface val #[kg_id] : 'unit → chPubKey × chSecKey ; val #[enc_id]: chPubKey × chPlain → chCipher ] = *)
  (*   [interface val #[kg_id] : 'unit → chPubKey × chSecKey ] :|: [interface val #[enc_id]: chPubKey × chPlain → chCipher]. *)
  (* Admitted. *)

  (* Lemma parable_KG_Enc :  parable [interface val #[kg_id] : 'unit → chPubKey × chSecKey ] *)
  (*                                 [interface val #[enc_id] : chPubKey × chPlain → chCipher ] . Admitted. *)

   Definition cpa_L_vs_R : GamePair [interface val #[challenge_id] : chPlain × chPlain → chCipher].
   Proof.
     move => b. destruct b.
     - exact: L_pk_cpa_L.
     - exact: L_pk_cpa_R.
   Defined.


   (* [The Joy of Cryptography] Definition 15.1

     A public-key encryption scheme is secure against chosen-plaintext attacks iff the following is True.
    *)

   Definition CPA_security : Prop := forall A H1 H2, @Advantage _ cpa_L_vs_R A H1 H2 = 0.


     (* Define what it means for an asymmetric encryption scheme to: *)
     (**  *HAVE PSEUDORND CIPHERTEXT IN PRESENCE OF CHOSEN PLAINTEXT ATTACKS **)

   #[program] Definition L_pk_cpa_real_open : opackage L_locs
   [interface  ]
   [interface val #[challenge_id] : chPlain → chCipher ] :=
    [package

       def #[challenge_id] ( m : chPlain ) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
         put pk_loc := pk ;;
         put sk_loc := sk ;;
         c ← Enc pk m ;;
         ret c
      }

    ].


   Definition L_pk_cpa_real : package [interface ]
                                      [interface val #[challenge_id] : chPlain → chCipher].
  Proof. exists L_locs. exact: L_pk_cpa_real_open. Defined.



  #[program] Definition L_pk_cpa_rand_open : opackage L_locs
    [interface ]
    [interface val #[challenge_id] : chPlain → chCipher ]  :=
    [package

       def #[challenge_id] ( m : chPlain ) : chCipher
      {
        '(pk, sk) ← KeyGen ;;
         put pk_loc := pk ;;
         put sk_loc := sk ;;
         c <$ (U i_cipher) ;;
         ret (c2ch c)
      }

    ].


  Definition L_pk_cpa_rand : package [interface ]
                                     [interface val #[challenge_id] : chPlain → chCipher].
  Proof. exists L_locs. exact: L_pk_cpa_rand_open. Defined.

  Definition cpa_real_vs_rand : GamePair [interface val #[challenge_id] : chPlain → chCipher].
  Proof.
    move => b. destruct b.
    - exact: L_pk_cpa_real.
    - exact: L_pk_cpa_rand.
  Defined.

   (* [The Joy of Cryptography] Definition 15.2

     A public-key encryption scheme has pseudornd ciphertext against chosen-plaintext attacks iff the following is True.
    *)

  Definition CPA_rnd_cipher : Prop := forall A H1 H2, @Advantage _ cpa_real_vs_rand A H1 H2 = 0.


  Theorem CPA_rnd_cipher_implies_CPA_security : CPA_rnd_cipher -> CPA_security. Admitted.

   (* Define what it means for an asymmetric encryption scheme to have: *)
  (**   *ONE-TIME SECRECY **)


  Definition L_locs_counter := fset [:: counter_loc; pk_loc; sk_loc].

  #[program] Definition L_pk_ots_L_open : opackage L_locs_counter
    [interface ]
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

  Definition L_pk_ots_L : package [interface ]
                                  [interface val #[challenge_id] : chPlain × chPlain → 'option chCipher].
  Proof. exists L_locs_counter. exact: L_pk_ots_L_open. Defined.


  #[program] Definition L_pk_ots_R_open : opackage L_locs_counter
    [interface ]
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

  Definition L_pk_ots_R : package [interface ]
                                  [interface val #[challenge_id] : chPlain × chPlain → 'option chCipher].
  Proof. exists L_locs_counter. exact: L_pk_ots_R_open. Defined.


   Definition ots_L_vs_R : GamePair [interface val #[challenge_id] :chPlain × chPlain → 'option chCipher].
   Proof.
     move => b. destruct b.
     - exact: L_pk_ots_L.
     - exact: L_pk_ots_R.
   Defined.


   (* [The Joy of Cryptography] Definition 15.4

     A public-key encryption scheme is secure against chosen-plaintext attacks iff the following is True.
    *)

  Definition OT_secrecy : Prop := forall A H1 H2, @Advantage _ ots_L_vs_R A H1 H2 = 0.

  Theorem OT_secrecy_CPA_security : OT_secrecy -> CPA_security. Admitted.


  (*  *)

  #[program] Definition L_pk_ots_real_open :  opackage L_locs_counter
    [interface ]
    [interface val #[challenge_id'] : chPlain → 'option chCipher ]  :=
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


  Definition L_pk_ots_real: package [interface ]
                                    [interface val #[challenge_id'] : chPlain → 'option chCipher ].
  Proof. exists L_locs_counter. exact: L_pk_ots_real_open. Defined.

  #[program] Definition L_pk_ots_rnd_open : opackage L_locs_counter
    [interface ]
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
         c <$ (U i_cipher) ;;
         ret (some (c2ch c))
       else ret None
      }

    ].

  Definition L_pk_ots_rnd: package  [interface ]
                                    [interface val #[challenge_id'] : chPlain → 'option chCipher ].
  Proof. exists L_locs_counter. exact: L_pk_ots_rnd_open. Defined.


  Definition ots_real_vs_rnd :
    GamePair [interface val #[challenge_id'] : chPlain → 'option chCipher].
  Proof.
    move => b. destruct b eqn:Hb.
    - exact: L_pk_ots_real.
    - exact: L_pk_ots_rnd.
  Defined.

  Definition OT_rnd_cipher : Prop := forall A H1 H2, @Advantage _ ots_real_vs_rnd A H1 H2 = 0.

  (* Future work! Please notice that in the paper we only claim OT_rnd_cipher *)
  Lemma OT_rnd_cipher_implies_OT_secrecy : OT_rnd_cipher -> OT_secrecy.
  Proof.  Admitted.

End AsymmetricScheme.
