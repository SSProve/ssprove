(*

  Elgamal encryption scheme.

  We show that DH security implies the security of Elgamal.


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
     realsum
     fingroup.fingroup
     solvable.cyclic
     prime.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

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
     chUniverse
     pkg_composition
     pkg_rhl
     Package
     Prelude
     pkg_notation
     AsymmetricSchemeStateProb.

From Crypt Require Import pkg_notation.

From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Parameter η : nat.
Parameter gT : finGroupType.
Parameter ζ : {set gT}.
Parameter g :  gT.
Parameter g_gen : ζ == <[g]>.
Parameter prime_order : prime #[g].

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g.
  by move/eqP: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

(*Rem.: cyclic -> abelian (i.e. commutative) however the ssreflect definition of abelian is the one with subgroups *)
Lemma group_prodC : forall x y : gT, x * y = y * x.
Admitted.

Inductive probEmpty : Type -> Type := .

Module MyParam <: AsymmetricSchemeParams.

  Definition SecurityParameter : choiceType := nat_choiceType.
  Definition Plain  : finType := FinGroup.arg_finType gT.
  Definition Cipher : finType := prod_finType (FinGroup.arg_finType gT) (FinGroup.arg_finType gT).
  Definition PubKey : finType := FinGroup.arg_finType gT.
  Definition SecKey : finType := [finType of 'Z_q].

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

  Definition probE : Type -> Type := probEmpty.
  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes -> choiceType.
  Proof.  move => contra. contradiction. Defined.

  Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
  Proof. move => contra. contradiction. Defined.

  Definition Hch : forall r : rel_choiceTypes, chEmb r.
  Proof. move => contra. contradiction. Defined.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.
  Module asym_rules := (ARules MyParam).
  Import asym_rules.
  Include (Package_Make myparamU).

  Module MyPackage := Package_Make myparamU.

  Import MyPackage.
  Import PackageNotation.


  Definition counter_loc : Location := (chNat; 0%N).
  Definition pk_loc : Location := (chNat; 1%N).
  Definition sk_loc : Location := (chNat; 2%N).
  Definition m_loc  : Location := (chNat; 3%N).
  Definition c_loc  : Location := (chNat; 4%N).

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


  Definition U (i : Index) :
    {rchT : myparamU.rel_choiceTypes &
            myparamU.probE (myparamU.chEmb rchT)} :=
    (existT (λ rchT : myparamU.rel_choiceTypes, myparamU.probE (chEmb rchT))
            (inl (inl i)) (inl (Uni_W i))).

  (* *)
  Definition pk2ch : PubKey -> (chFin PubKey_len_pos). Admitted.
  Definition ch2pk : (chFin PubKey_len_pos) -> PubKey. Admitted.
  (* *)
  Definition sk2ch : SecKey -> (chFin SecKey_len_pos). Admitted.
  Definition ch2sk : (chFin SecKey_len_pos) -> SecKey. Admitted.
  (* *)
  Definition m2ch : Plain -> (chFin Plain_len_pos). Admitted.
  Definition ch2m : (chFin Plain_len_pos) -> Plain. Admitted.
  (* *)
  Definition c2ch  : Cipher -> (chFin Cipher_len_pos).  Admitted.
  Definition ch2c : (chFin Cipher_len_pos) -> Cipher. Admitted.


  (* (* Key Generation algorithm *) *)
  #[program] Definition KG_open : opackage fset0 [interface] [interface val #[kg_id]: 'unit → chPubKey × chSecKey] :=
    [package def #[kg_id] ( _ : 'unit ) : chPubKey × chSecKey
             {
               x <$ (U i_sk) ;;
               ret ( pk2ch (g^+x), sk2ch x)
             }
     ].
  Definition KG : package [interface] [interface val #[kg_id] : 'unit → chPubKey × chSecKey].
  Proof. exists fset0. exact KG_open. Defined.

  (* Encryption algorithm *)
  #[program] Definition Enc_open : opackage fset0 [interface] [interface val #[enc_id] : chPubKey × chPlain → chCipher] :=
    [package def #[enc_id] (pk_m : chPubKey × chPlain) : chCipher
             {
               y <$ (U i_sk) ;;
               ret (c2ch (g^+y, ( (ch2pk (fst pk_m))^+y * (ch2m (snd pk_m)))))
             }
    ].

  Definition Enc : package [interface] [interface val #[enc_id]: chPubKey × chPlain → chCipher].
  Proof. exists fset0. exact Enc_open. Defined.


  (* Decryption algorithm *)
  #[program] Definition Dec_open : opackage fset0 [interface] [interface val #[dec_id] : chSecKey × chCipher → chPlain ] :=
    [package def #[dec_id] (sk_c : chSecKey × chCipher) : chPlain
             {
               ret (m2ch ( (snd (ch2c (snd sk_c))) * ((fst (ch2c (snd sk_c)))^-(ch2sk(fst sk_c))) ))
             }
    ].
  Definition Dec : package [interface] [interface val #[dec_id] :  chSecKey × chCipher → chPlain].
  Proof. exists fset0. exact Dec_open. Defined.

End MyAlg.

Local Open Scope package_scope.

Module Elgamal_Scheme :=  AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg asym_rules MyPackage Elgamal_Scheme PackageNotation.

Obligation Tactic := package_obtac.

Lemma counter_loc_in : is_true (counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)])). Proof. package_obtac. Qed.
Lemma pk_loc_in : is_true (pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)])). Proof. package_obtac. Qed.
Lemma sk_loc_in : is_true (sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)])). Proof. package_obtac. Qed.
(* Lemma c_loc_in : is_true (c_loc \in (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)])). Proof. package_obtac. Qed. *)

Definition DH_loc := fset [:: pk_loc; sk_loc].

#[program] Definition DH_real_opkg : opackage DH_loc [interface] [interface val #[10]: 'unit → chPubKey × chCipher ] :=
  [ package def #[10] ( _ : 'unit ) : chPubKey × chCipher
             {
               a <$ (U i_sk);; b <$ (U i_sk);;
               put pk_loc := pk2ch (g^+a);;
               put sk_loc := sk2ch a ;;
               (* put c_loc  := c2ch (g^+b, g^+(a * b));; *)
               ret (pk2ch (g^+a), c2ch (g^+b, g^+(a * b)) )
             }

  ].

Definition DH_real : package  [interface] [interface val #[10]: 'unit → chPubKey × chCipher ].
Proof. exists DH_loc. exact: DH_real_opkg. Defined.

#[program] Definition DH_rnd_opkg : opackage  DH_loc [interface] [interface val #[10]: 'unit → chPubKey × chCipher ] :=
  [ package def #[10] ( _ : 'unit ) : chPubKey × chCipher
             {
               a <$ (U i_sk);; b <$ (U i_sk);; c <$ (U i_sk);;
               put pk_loc := pk2ch (g^+a);;
               put sk_loc := sk2ch a ;;
               (* put c_loc  := c2ch (g^+b, g^+c) ;; *)
               ret (pk2ch (g^+a), c2ch (g^+b, g^+c) )
             }

  ].

Definition DH_rnd : package  [interface] [interface val #[10]: 'unit → chPubKey × chCipher ].
Proof. exists DH_loc. exact: DH_rnd_opkg. Defined.


(*Rem.: I don't understand why this Fail *)
#[program] Definition Aux_opkg : opackage (fset [:: counter_loc])
     [interface val #[10]: 'unit → chPubKey × chCipher]
     [interface val #[challenge_id'] : chPlain → 'option chCipher] :=
  [
    package def #[challenge_id'] ( m : chPlain ) : 'option chCipher
             {
                count ← get counter_loc ;;
                put counter_loc := (count + 1)%N;;
                if ((count == 0)%N) then
                  '(pk, c) ← op [ #[10] : 'unit → chPubKey × chCipher] Datatypes.tt ;;
                   ret (some (c2ch ((ch2c c).1 , (ch2m m) * ((ch2c c).2))))
                else ret None
             }

  ].


Definition Aux : package [interface val #[10]: 'unit → chPubKey × chCipher]
                         [interface val #[challenge_id'] : chPlain → 'option chCipher].
Proof. exists (fset [:: counter_loc]). exact: Aux_opkg. Defined.


Definition Aux_DH_real (m : 'I_#|gT|) :  code (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *) ]) fset0 (chOption (chFin Cipher_len_pos)).
Proof.
  apply: bind.
  { apply: (getr counter_loc counter_loc_in) => count.
    apply: ret count.
  }
  move => /= count. apply: bind.
  { apply: (putr _ counter_loc_in).
    - simpl. exact: (count + 1)%N.
    - apply: ret Datatypes.tt. }
  move => tt. destruct count eqn: Hcount.
  - apply: bind.
    { apply: (sampler (U i_sk)) => /= a. apply: ret a. }
    move => /= a. apply: bind.
    { apply: (sampler (U i_sk)) => /= b. apply: ret b. }
    move => /= b. apply: bind.
    { apply: (putr _ pk_loc_in (pk2ch (g^+a))). apply: ret Datatypes.tt. }
    move => tt1. apply: bind.
    { apply: (putr _ sk_loc_in  (sk2ch a)). apply: ret Datatypes.tt. }
    move => tt2.
    (* apply: bind. *)
    (* { apply: (putr _ c_loc_in (c2ch (g^+b, (ch2m m) * g^+(a * b)))). apply: ret Datatypes.tt. } *)
    (* move => tt3. *)
    apply: ret (some (c2ch (g^+b, (ch2m m)* g^+(a * b)))).
  - apply: ret None.
Defined.

Definition Aux_DH_rnd (m : 'I_#|gT|) :  code (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)]) fset0 (chOption (chFin Cipher_len_pos)).
Proof.
  apply: bind.
  { apply: (getr counter_loc counter_loc_in) => count.
    apply: ret count. }
  move => /= count. apply: bind.
  { apply: (putr _ counter_loc_in).
    - simpl. exact: (count + 1)%N.
    - apply: ret Datatypes.tt. }
  move => tt. destruct count eqn: Hcount.
  - apply: bind.
    { apply: (sampler (U i_sk)) => /= a. apply: ret a. }
    move => /= a. apply: bind.
    { apply: (sampler (U i_sk)) => /= b. apply: ret b. }
    move => /= b. apply: bind.
    { apply: (sampler (U i_sk)) => /= c. apply: ret c. }
    move => /= c. apply: bind.
    { apply: (putr _ pk_loc_in (pk2ch (g^+a))). apply: ret Datatypes.tt. }
    move => tt1. apply: bind.
    { apply: (putr _ sk_loc_in (sk2ch a)). apply: ret Datatypes.tt. }
    move => tt3.
    (* apply: bind. *)
    (* { apply: (putr _ c_loc_in (c2ch (g^+b, (g^+c)))). apply: ret Datatypes.tt. }  *)
    (* move => tt2. *)
    apply: ret (some (c2ch (g^+b, (ch2m m) * (g^+c)))).
  - apply: ret None.
Defined.

Definition LHS0 (m : 'I_#|gT|) : code (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)])  fset0 (chOption (chFin Cipher_len_pos)).
Proof.
  apply: bind.
  { apply: (getr counter_loc counter_loc_in) => /= count.
    apply: ret count. }
  move => /= count. apply: bind.
  { apply: (putr _ counter_loc_in).
    - simpl. exact: (count + 1)%N.
    - apply: ret Datatypes.tt. }
   move => tt1. destruct count eqn: Hcount.
  - apply: bind.
    { apply: (sampler (U i_sk)) => /= a. apply: ret a. }
    move => /= a. apply: bind.
    { apply: (putr _ pk_loc_in (pk2ch (g^+a))). apply: ret Datatypes.tt. }
    move => tt2. apply: bind.
    { apply: (putr _ sk_loc_in (sk2ch a)). apply: ret Datatypes.tt. }
    move => tt3. apply: bind.
    { apply: (sampler (U i_sk)) => /= b. apply: ret b. }
    move => /= b. (* apply: bind. *)
    (* { apply: (putr _ sk_loc_in b). apply: ret Datatypes.tt. } *)
    (* move => tt3.   *)
    (* apply: bind. *)
    (* { apply: (putr _ c_loc_in (c2ch (g^+b, (ch2m m) * (g^+(a*b))))). apply: ret Datatypes.tt. } *)
    (* move => tt4. *)
    apply: ret (some (c2ch (g^+b, (ch2m m) * (g^+(a*b))))).
  - apply: ret None.
Defined.


Definition RHS0 (m : 'I_#|gT|) : code (fset [:: counter_loc; pk_loc; sk_loc (*; c_loc *)]) fset0 (chOption (chFin Cipher_len_pos)).
Proof.
  apply: bind.
  { apply: (getr counter_loc counter_loc_in) => /= count.
    apply: ret count. }
  move => /= count. apply: bind.
  { apply: (putr _ counter_loc_in).
    - simpl. exact: (count + 1)%N.
    - apply: ret Datatypes.tt. }
  move => tt2. destruct count eqn: Hcount.
  - apply: bind.
     { apply: (sampler (U i_sk)) => /= a. apply: ret a. }
     move => /= a. apply: bind.
     (* { apply: (sampler (U i_sk)) => /= b. apply: ret b. } *)
     (* move => /= b. apply: bind. *)
     { apply: (putr _ pk_loc_in (pk2ch (g^+a))). apply: ret Datatypes.tt. }
     move => tt1. apply: bind.
     { apply: (putr _ sk_loc_in (sk2ch a)). apply: ret Datatypes.tt. }
    move => tt4. apply: bind.
    { apply: (sampler (U i_cipher)) => /= c. apply: ret c. }
    move => /= c. (*  apply: bind. *)
     (* { apply: (sampler (U i_sk)) => /= b. apply: ret b. } *)
     (* move => /= b.  *)
    (* apply: bind. *)
    (* { apply: (putr _ c_loc_in (c2ch c)). apply: ret Datatypes.tt. } *)
    (* move => tt3. *)
    apply: ret (some (c2ch c)).
  - apply: ret None.
Defined.

Lemma group_OTP_math { L : {fset  Location } } : forall m (s : heap_choiceType),
   MyAlg.MyPackage.θ_dens
     (MyAlg.MyPackage.θ0
        (@repr _ L ( (b ← (b ← sample U i_sk ;; ret b) ;;
                      c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c)))))) s) =
   MyAlg.MyPackage.θ_dens
     (MyAlg.MyPackage.θ0
        (@repr _ L ((b ← (b ← sample U i_sk ;; ret b) ;; c ← (c ← sample U i_sk ;; ret c) ;;
                     ret (Some (c2ch (g ^+ b, g ^+ c)))))) s).
Admitted. (* Rem.: look for an informal proof of this in the CertyCrypt paper *)

Lemma group_OTP { L : { fset Location } } : forall m,
    ⊨ ⦃ λ '(h1, h2), h1 = h2 ⦄
      @repr _ L ((c ← (c ← sample U i_cipher ;; ret c) ;; ret (Some (c2ch c))))  ≈
      @repr _ L ((b ← (b ← sample U i_sk ;; ret b) ;;
                  c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c))))) ⦃ eq ⦄.
Proof.
  move => m.
  unshelve apply: rrewrite_eqDistrL.
  { eapply (
        ((b ← (b ← sample U i_sk ;; ret b) ;;
          c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, g ^+ c)))))). }
  { apply: rrewrite_eqDistrL.
    - by apply: rreflexivity_rule.
    - exact: group_OTP_math. }
  move => s. apply rcoupling_eq with (ψ := fun '(s1, s2) => s1 = s2). 2: by reflexivity.
  (*Rem.:
   1. sampling c <$ U i_cipher is the same as sampling two element of the group say (C1,C2) <$ U (G × G)
   2. the map (g^+_, g^+_) is a bijection and we can use the uniform bij rule.
 *) Admitted.

(* Note duplicate in SymmetricSchemeStateProb *)
(* TODO MOVE But where? *)
Lemma eq_prog_semj_impl :
  ∀ L L' R R' A
    (p : code L _ A) (q : code R _ _)
    (p' : code L' _ A) (q' : code R' _ _),
    L = L' →
    R = R' →
    sval p = sval p' →
    sval q = sval q' →
    ⊨ ⦃ λ '(s1, s2), s1 = s2 ⦄ repr p ≈ repr q ⦃ eq ⦄ →
    ⊨ ⦃ λ '(s1, s2), s1 = s2 ⦄ repr p' ≈ repr q' ⦃ λ '(a, b) '(c, d), a = c ∧ b = d ⦄.
Proof.
  intros L L' R R' A p q p' q' eL eR ep eq.
  subst L' R'.
  eapply code_ext in ep.
  eapply code_ext in eq.
  subst q' p'.
  intro h.
  eapply post_weaken_rule. 1: eauto.
  cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

 Lemma cipher_encoding_correct : forall b c m,
      c2ch (g ^+ b, ch2m m * g ^+ c) = c2ch ((ch2c (c2ch (g ^+ b, g ^+ c))).1, ch2m m * (ch2c (c2ch (g ^+ b, g ^+ c))).2).
  Admitted.

 Lemma pk_encoding_correct : forall p,
     ch2pk (pk2ch p ) = p. Admitted.

Lemma game_hop : forall A Hdisj1 Hdisj2 Hdisj1' Hdisj2',
  @AdvantageE _ (ots_real_vs_rnd false) (ots_real_vs_rnd true) A Hdisj1 Hdisj2 =
  @AdvantageE _ (Aux ∘ DH_real) (Aux ∘ DH_rnd) A Hdisj1' Hdisj2'.
Proof.
  rewrite /AdvantageE => A Hdisj1 Hdisj2 Hdisj1' Hdisj2'.
  (**********************************)
  have HR : Pr (A ∘ ots_real_vs_rnd false) true = Pr (A ∘ Aux ∘ DH_rnd) true.
  { apply: GRing.subr0_eq. apply: normr0_eq0.
    (*Rem.: I don't know why fold does not fold *)
    have Hfool : `|Pr (A ∘ ots_real_vs_rnd false) true - Pr (A ∘ Aux ∘ DH_rnd) true| =
    (@AdvantageE [interface val #[challenge_id'] : chPlain → 'option chCipher ]
                 (ots_real_vs_rnd false) (Aux ∘ DH_rnd) A Hdisj1 Hdisj1') by [].
    rewrite Hfool.
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold Aux, Enc, DH_rnd. unfold Aux_opkg.
    unfold ots_real_vs_rnd. unfold L_pk_ots_rnd.
    unfold L_pk_ots_rnd_open.
    package_link_simplify.
    intros id hinterface m.
    invert_interface_in hinterface.
     repeat opackage_transport_simplify.
    package_pdef_simpl.
    unfold pdefS in m. simpl in m.
    suffices: ⊨ ⦃ fun '(h1,h2) => h1 = h2⦄ repr (RHS0 m) ≈ repr (Aux_DH_rnd m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - by rewrite /L_locs_counter !fsetU0.
      - by rewrite /DH_loc -fset_cat /=.
      - unfold RHS0.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal.
        destruct a.
        2: reflexivity.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          unfold raw_par in e. rewrite unionmE in e.
          unfold trim in e. rewrite filtermE in e.
          simpl in e. rewrite in_fset in e.
          match type of e with
          | context [ ?i \in ?s] =>
            set (foo := i \in s) ;
            change (i \in s) with foo in e
          end.
          assert (foo = true).
          { subst foo. clear. rewrite in_cons. cbn.
            apply/orP. left. apply/andP. split.
            - apply/eqP. reflexivity.
            - apply/eqP. reflexivity.
          }
          clearbody foo. subst.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. unfold raw_par in e.
        rewrite unionmE in e.
        unfold trim in e. rewrite filtermE in e.
        simpl in e. rewrite in_fset in e.
        match type of e with
        | context [ ?i \in ?s] =>
          set (foo := i \in s) ;
          change (i \in s) with foo in e
        end.
        assert (foo = true).
        { subst foo. clear. rewrite in_cons. cbn.
          apply/orP. left. apply/andP. split.
          - apply/eqP. reflexivity.
          - apply/eqP. reflexivity.
        }
        clearbody foo. subst.
        simpl in e. noconf e.
        reflexivity.
      - cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality counter.
        f_equal. destruct counter eqn:Hcounter. 2: reflexivity.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal. extensionality b.
        f_equal. extensionality c.
        f_equal. f_equal. f_equal. f_equal.
        exact: (cipher_encoding_correct (b%N) (c%N) m).
    }
    - rewrite /RHS0 /Aux_DH_rnd.
      apply: rsame_head => counter.
      destruct counter eqn:Hcounter.
      -- apply: rsame_head => tt.
         unshelve apply: rrewrite_eqDistrR.
         { eapply (
             (a ← (a ← sample U i_sk ;; ret a) ;;
              (* b ← (b ← sample U i_sk ;; ret b) ;; *)
              c ← (c ← sample U i_cipher ;; ret c) ;;
              (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
              (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
              ret (Some (c2ch c))) ). }
         { apply: rsame_head => a.
           apply: rrewrite_eqDistrR. { apply: rsame_head => tt1. apply: rswap_ruleR.
                                       + move => bs bs' H. assumption.
                                       + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                                                        apply: rreflexivity_rule.
                                       + by apply (rsamplerC (U i_cipher)). }
         move => s. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
         apply: rswap_ruleR. { move => bs bs' H. assumption. }
           - move => tt1 aa. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                             apply: rreflexivity_rule.
           - apply (rsamplerC (U i_cipher)). }
         move => s. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
         apply: rsame_head => a.
         apply: rrewrite_eqDistrL.
         --- exact: rreflexivity_rule.
         --- move => s0. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
             { unshelve apply: rrewrite_eqDistrL.
               { eapply (
                   (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
                   (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
                   (b ← (b ← sample U i_sk ;; ret b) ;;
                    c ← (c ← sample U i_sk ;; ret c) ;;
                    ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c))) )). }
               -- unshelve apply: rrewrite_eqDistrL.
                  { eapply (
                        (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
                        (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
                        (c ← (c ← sample U i_cipher ;; ret c) ;;
                        ret (Some (c2ch c))) ). }
                  --- apply: rrewrite_eqDistrL.
                      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                        + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                        + apply: rsamplerC (U i_cipher) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                      move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                      apply: rsame_head => tt'. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                        + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                        + apply: rsamplerC' (U i_cipher)(put sk_loc := sk2ch a ;; ret Datatypes.tt).
                  --- move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                      apply: rsame_head => tt'. apply: rsame_head => tt''. exact: group_OTP.
               -- move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rrewrite_eqDistrL.
                  { apply: rsame_head => b. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC (U i_sk) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                  move => s2. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rrewrite_eqDistrR.
                  { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC' (U i_sk) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                  move => s3. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rsame_head => tt1.
                  apply: rrewrite_eqDistrL.
                  { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC' (U i_sk) (put sk_loc := sk2ch a ;; ret Datatypes.tt). }
                  move => s4. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rsame_head => b. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC (U i_sk) (put sk_loc := sk2ch a ;; ret Datatypes.tt).  }
      -- apply: rreflexivity_rule. }
  rewrite HR. clear HR.
  have HL : Pr (A ∘ ots_real_vs_rnd true) true = Pr (A ∘ Aux ∘ DH_real) true.
  { apply: GRing.subr0_eq. apply: normr0_eq0.
    have Hfool : `|Pr (A ∘ ots_real_vs_rnd true) true - Pr (A ∘ Aux ∘ DH_real) true| =
    (@AdvantageE [interface val #[challenge_id'] : chPlain → 'option chCipher ]
                 (ots_real_vs_rnd true) (Aux ∘ DH_real) A Hdisj1 Hdisj1') by [].
    rewrite Hfool.
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold Aux, DH_real, DH_real_opkg. unfold Aux_opkg.
    unfold ots_real_vs_rnd. unfold L_pk_ots_real.
    unfold L_pk_ots_real_open.
    package_link_simplify.
    intros id hinterface m.
    invert_interface_in hinterface.
    repeat opackage_transport_simplify.
    package_pdef_simpl.
    unfold pdefS in m. simpl in m.
    suffices: ⊨ ⦃ fun '(h1,h2) => h1 = h2⦄ repr (LHS0 m) ≈ repr (Aux_DH_real m) ⦃ eq ⦄.
     { eapply eq_prog_semj_impl.
      - by rewrite /L_locs_counter !fsetU0.
      - by rewrite /DH_loc -fset_cat /=.
      - unfold LHS0.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal.
        destruct a.
        2: reflexivity.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          unfold raw_par in e. rewrite unionmE in e.
          unfold trim in e. rewrite filtermE in e.
          simpl in e. rewrite in_fset in e.
          match type of e with
          | context [ ?i \in ?s] =>
            set (foo := i \in s) ;
            change (i \in s) with foo in e
          end.
          assert (foo = true).
          { subst foo. clear. rewrite in_cons. cbn.
            apply/orP. left. apply/andP. split.
            - apply/eqP. reflexivity.
            - apply/eqP. reflexivity.
          }
          clearbody foo. subst.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. unfold raw_par in e.
        rewrite unionmE in e.
        unfold trim in e. rewrite filtermE in e.
        simpl in e. rewrite in_fset in e.
        match type of e with
        | context [ ?i \in ?s] =>
          set (foo := i \in s) ;
          change (i \in s) with foo in e
        end.
        assert (foo = true).
        { subst foo. clear. rewrite in_cons. cbn.
          apply/orP. left. apply/andP. split.
          - apply/eqP. reflexivity.
          - apply/eqP. reflexivity.
        }
        clearbody foo. subst.
        simpl in e. noconf e.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal. f_equal.
        destruct lookup_op as [f|] eqn:e.
        2:{
          simpl in e.
          unfold raw_par in e. rewrite unionmE in e.
          unfold trim in e. rewrite filtermE in e.
          simpl in e.
          rewrite filtermE in e. simpl in e.
          rewrite in_fset in e.
          match type of e with
          | context [ ?i \in ?s] =>
            set (foo := i \in s) ;
            change (i \in s) with foo in e
          end.
          assert (foo = true).
          { subst foo. clear. rewrite in_cons.
            apply/orP. left. apply/eqP. reflexivity.
          }
          clearbody foo. subst.
          destruct chUniverse_eqP. 2: contradiction.
          destruct chUniverse_eqP. 2: contradiction.
          discriminate.
        }
        eapply lookup_op_spec in e. unfold raw_par in e.
        rewrite unionmE in e.
        unfold trim in e. rewrite filtermE in e.
        simpl in e. rewrite filtermE in e.
        simpl in e. rewrite in_fset in e.
        match type of e with
        | context [ ?i \in ?s] =>
          set (foo := i \in s) ;
          change (i \in s) with foo in e
        end.
        assert (foo = true).
        { subst foo. clear. rewrite in_cons.
          apply/orP. left. apply/eqP. reflexivity.
        }
        clearbody foo. subst. noconf e.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality b. f_equal. f_equal.
        rewrite pk_encoding_correct.
        f_equal. by rewrite expgM group_prodC.
      - rewrite /Aux_DH_real.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal.
        destruct a. 2: reflexivity.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal. extensionality b.
        f_equal. f_equal. f_equal.
        f_equal.
        exact: cipher_encoding_correct (b%N) ((a * b)%Nrec) m.
     }
     rewrite /LHS0 /Aux_DH_real.
     apply: rsame_head => counter.
     apply: rsame_head => tt.
     destruct counter eqn:Hcounter.
    ++ apply: rsame_head => a.
       apply: rrewrite_eqDistrL.
       { apply: rswap_ruleR. { move => bs bs' H. assumption. }
       -- move => x y. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                       apply: rreflexivity_rule.
       -- apply (rsamplerC ( U i_sk)). }
       move => s. apply rcoupling_eq with (ψ := fun '(s1, s2) => s1 = s2). 2: by reflexivity.
       apply: rsame_head => tt1.
       apply: rswap_ruleR. { move => bs bs' H. assumption. }
       --- move => b tt2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                       apply: rreflexivity_rule.
       --- apply (rsamplerC' (U i_sk)).
    ++ apply: rreflexivity_rule. }
  rewrite HL. clear HL.
  by rewrite distrC.
Qed.

Definition DH_security : Prop := forall A Hdisj1 Hdisj2,
    @AdvantageE _ DH_real DH_rnd A  Hdisj1 Hdisj2 = 0.

Theorem Elgamal_CPA_security (dh_secure : DH_security) : CPA_security.
Proof.
  apply: OT_secrecy_CPA_security.
  apply: OT_rnd_cipher_implies_OT_secrecy.
  rewrite /OT_rnd_cipher.
  move => A Hdisj1 Hdisj2.
  rewrite /Advantage.
  fold (@AdvantageE _ (ots_real_vs_rnd false) (ots_real_vs_rnd true) A Hdisj1 Hdisj2).
  rewrite game_hop. 1,2: by admit.
  rewrite /AdvantageE => H1 H2. rewrite !link_assoc.
  have H1' : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) (A ∘ Aux).π1 (DH_real).π1 by admit.
  have H2' : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) (A ∘ Aux).π1 (DH_rnd).π1 by admit.
  fold (@AdvantageE _ DH_real DH_rnd (A ∘ Aux) H1' H2').
  by apply: dh_secure.
Admitted.
