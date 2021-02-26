(*

  ElGamal encryption scheme.

  We show that DH security implies the security of ElGamal.


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
     pkg_chUniverse
     pkg_composition
     pkg_rhl
     Package
     Prelude
     pkg_notation
     AsymScheme.

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
Definition ζ : {set gT} := [set : gT].
Parameter g :  gT.
Parameter g_gen : ζ = <[g]>.
Parameter prime_order : prime #[g].

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

Lemma group_prodC : forall x y : gT, x * y = y * x.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.


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


 Definition gT_pos : positive.
 Proof. exists #|gT|. apply /card_gt0P. by exists g. Defined. 
 

  Definition SecKey_len_pos : positive.
  Proof. exists #|SecKey|. apply /card_gt0P. by exists sec0. Defined.

 Definition choicePlain  : chUniverse := chFin gT_pos.
 Definition choicePubKey : chUniverse := chFin gT_pos.
 Definition choiceCipher : chUniverse := chProd (chFin gT_pos) (chFin gT_pos). 
 Definition choiceSecKey : chUniverse := chFin SecKey_len_pos. 
 
 Definition counter_loc : Location := ('nat; 0%N). 
 Definition pk_loc : Location := (choicePubKey; 1%N). 
 Definition sk_loc : Location := (choiceSecKey; 2%N).
 Definition m_loc  : Location := (choicePlain; 3%N). 
 Definition c_loc  : Location := (choiceCipher; 4%N).
 
 Definition kg_id : nat := 5.
 Definition enc_id : nat := 6.
 Definition dec_id : nat := 7.
 Definition challenge_id : nat := 8. (*challenge for LR *)
 Definition challenge_id' : nat := 9. (*challenge for real rnd *) 
  
  Definition U (i : Index) :
    {rchT : myparamU.rel_choiceTypes &
            myparamU.probE (myparamU.chEmb rchT)} :=
    (existT (λ rchT : myparamU.rel_choiceTypes, myparamU.probE (chEmb rchT))
            (inl (inl i)) (inl (Uni_W i))).

  Definition gT2ch : gT -> chFin gT_pos.
  Proof.
    move => /= A. 
     destruct (@cyclePmin gT g A) as [i Hi]. Check cyclePmin. 
    { rewrite -g_gen.
      apply: in_setT. } 
    exists i.
    rewrite orderE in Hi.
    rewrite /= -cardsT.
    setoid_rewrite g_gen.
    assumption.
  Defined.   

  Definition ch2gT : (chFin gT_pos) -> gT.
  Proof. 
    move => /= [i Hi]. exact: (g^+i).
  Defined.
  
  Lemma ch2gT_gT2ch (A : gT) : ch2gT (gT2ch A) = A.
  Proof.
   unfold gT2ch.
   destruct (@cyclePmin gT g A) as [i Hi]. subst.
   simpl. reflexivity.
  Qed. 
  
  Lemma gT2ch_ch2gT (chA : chFin gT_pos) : gT2ch (ch2gT chA) = chA.
  Proof.
    unfold ch2gT, gT2ch.
    destruct chA as [i hi]. simpl in *.
    destruct cyclePmin as [j hj e].
    assert (e' : i = j).
    { move: e => /eqP e. rewrite eq_expg_mod_order in e.
      move: e => /eqP e.
      rewrite !modn_small in e.
      - auto.
      - auto.
      - rewrite orderE. rewrite -g_gen. rewrite cardsT. auto.
    }
    subst j.
    f_equal.
    apply bool_irrelevance.
  Qed. 

  
  Definition pk2ch : PubKey -> choicePubKey := gT2ch. 
  Definition ch2pk : choicePubKey -> PubKey := ch2gT. 
  Definition m2ch : Plain -> choicePlain := gT2ch.
  Definition ch2m : choicePlain -> Plain := ch2gT.

  (* *)
  Definition sk2ch : SecKey -> choiceSecKey.
  Proof.
    move => /= [a Ha].
    exists a.
    rewrite card_ord. assumption.
  Defined.

  Definition ch2sk : (chFin SecKey_len_pos) -> SecKey.
    move => /= [a Ha].
    exists a.
    rewrite card_ord in Ha. assumption.
  Defined.

  
  (* *)
  Definition c2ch  : Cipher -> choiceCipher.
  Proof.
    move => [g1 g2] /=. 
    exact: (gT2ch g1, gT2ch g2).
  Defined.

  Definition ch2c : choiceCipher -> Cipher.
  Proof. 
    move => [A B].
    exact: (ch2gT A, ch2gT B).
  Defined.

  (* (* Key Generation algorithm *) *)
  Definition KeyGen { L : {fset Location} }: program L fset0 (choicePubKey × choiceSecKey) :=
    x <$ (U i_sk) ;;
    ret ( pk2ch (g^+x), sk2ch x).

  (* Encryption algorithm *)
  Definition Enc { L : {fset Location} } (pk : choicePubKey) (m : choicePlain) : program L fset0 (choiceCipher) :=
    y <$ (U i_sk) ;;
    ret (c2ch (g^+y, (ch2pk pk)^+y * (ch2m m))).


  (* Decryption algorithm *)
  Definition Dec_open { L : {fset Location} } (sk : choiceSecKey) (c : choiceCipher) :
    program L fset0 (choicePlain) :=
               ret (m2ch ( (fst (ch2c c)) * ( (snd (ch2c c))^-(ch2sk sk)) )).

  Notation " 'chSecurityParameter' " :=
    (chNat) (in custom pack_type at level 2).
  Notation " 'chPlain' " := choicePlain 
    (* (chFin Plain_len_pos ) *)
    (in custom pack_type at level 2).
  Notation " 'chCipher' " := choiceCipher
    (* (chFin Cipher_len_pos) *)
    (in custom pack_type at level 2).
  Notation " 'chPubKey' " := choicePubKey
    (* (chFin PubKey_len_pos) *)
    (in custom pack_type at level 2).
  Notation " 'chSecKey' " := choiceSecKey
    (* (chFin SecKey_len_pos) *)
    (in custom pack_type at level 2).
  
End MyAlg.

Local Open Scope package_scope.

Module ElGamal_Scheme :=  AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg asym_rules MyPackage ElGamal_Scheme PackageNotation.

Obligation Tactic := package_obtac.

Lemma counter_loc_in : is_true (counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc ])). Proof. package_obtac. Qed.
Lemma pk_loc_in : is_true (pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ])). Proof. package_obtac. Qed.
Lemma sk_loc_in : is_true (sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ])). Proof. package_obtac. Qed.

Definition DH_loc := fset [:: pk_loc; sk_loc].

#[program] Definition DH_real_opkg : opackage DH_loc [interface] [interface val #[10]: 'unit → chPubKey × chCipher ] :=
  [ package def #[10] ( _ : 'unit ) : chPubKey × chCipher
             {
               a <$ (U i_sk);; b <$ (U i_sk);;
               put pk_loc := pk2ch (g^+a);;
               put sk_loc := sk2ch a ;;
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
               ret (pk2ch (g^+a), c2ch (g^+b, g^+c) )
             }

  ].

Definition DH_rnd : package  [interface] [interface val #[10]: 'unit → chPubKey × chCipher ].
Proof. exists DH_loc. exact: DH_rnd_opkg. Defined.


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


(* Aux ∘ DH_real *)
Definition Aux_DH_real (m : 'I_#|gT|) :  program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption choiceCipher).
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
    apply: ret (some (c2ch (g^+b, (ch2m m)* g^+(a * b)))).
  - apply: ret None.
Defined.

(* Aux ∘ DH_rnd *)
Definition Aux_DH_rnd (m : 'I_#|gT|) :  program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption choiceCipher).
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
    apply: ret (some (c2ch (g^+b, (ch2m m) * (g^+c)))).
  - apply: ret None.
Defined.

Definition LHS0 (m : 'I_#|gT|) : program (fset [:: counter_loc; pk_loc; sk_loc ])  fset0 (chOption choiceCipher).
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
    move => /= b.
    apply: ret (some (c2ch (g^+b, (ch2m m) * (g^+(a*b))))).
  - apply: ret None.
Defined.


Definition RHS0 (m : 'I_#|gT|) : program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption choiceCipher).
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
     { apply: (putr _ pk_loc_in (pk2ch (g^+a))). apply: ret Datatypes.tt. }
     move => tt1. apply: bind.
     { apply: (putr _ sk_loc_in (sk2ch a)). apply: ret Datatypes.tt. }
    move => tt4. apply: bind.
    { apply: (sampler (U i_cipher)) => /= c. apply: ret c. }
    move => /= c.
    apply: ret (some (c2ch c)).
  - apply: ret None.
Defined.



Lemma group_OTP { L : { fset Location } } : forall m,
    ⊨ ⦃ λ '(h1, h2), h1 = h2 ⦄
      @repr _ L ((c ← (c ← sample U i_cipher ;; ret c) ;; ret (Some (c2ch c))))  ≈
      @repr _ L ((b ← (b ← sample U i_sk ;; ret b) ;;
                  c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c))))) ⦃ eq ⦄.
Proof.
  move => m.
  unshelve apply: rrewrite_eqDistrR.
  { eapply (
        bc ← (bc ← sample U (i_prod i_sk i_sk) ;; ret bc) ;;
               ret (Some (c2ch ( g^+ (bc.1), (ch2m m) * g ^+ (bc.2))))). } 
  { suffices:
      ⊨ ⦃ λ '(h1, h2), h1 = h2 ⦄
        @repr _  L (c ← (c ← sample U i_cipher ;; ret c) ;; ret c) ≈
        @repr _  L (bc ← (bc ← sample U (i_prod i_sk i_sk) ;; ret bc) ;; ret ((g ^+ bc.1, ch2m m * g ^+ bc.2))) ⦃ eq ⦄.
    { admit. (*CA: I think that to show this we can use (twice) again the Uniform_bij_rule, and show that Some ∘ c2ch is a bijection *) }
    Check Uniform_bij_rule.
    admit. 
     }
  (*CA: just Fubini? *) admit. 
Admitted.

(* Note duplicate in SymmetricSchemeStateProb *)
(* TODO MOVE But where? *)
Lemma eq_prog_semj_impl :
  ∀ L L' R R' A
    (p : program L _ A) (q : program R _ _)
    (p' : program L' _ A) (q' : program R' _ _),
    L = L' →
    R = R' →
    sval p = sval p' →
    sval q = sval q' →
    ⊨ ⦃ λ '(s1, s2), s1 = s2 ⦄ repr p ≈ repr q ⦃ eq ⦄ →
    ⊨ ⦃ λ '(s1, s2), s1 = s2 ⦄ repr p' ≈ repr q' ⦃ λ '(a, b) '(c, d), a = c ∧ b = d ⦄.
Proof.
  intros L L' R R' A p q p' q' eL eR ep eq.
  subst L' R'.
  eapply program_ext in ep.
  eapply program_ext in eq.
  subst q' p'.
  intro h.
  eapply post_weaken_rule. 1: eauto.
  cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.


Lemma pk_encoding_correct : forall p,
    ch2pk (pk2ch p ) = p.
Proof.
  move => /= A. rewrite /ch2pk /pk2ch. exact: ch2gT_gT2ch. 
Qed.

Lemma ch2c_c2ch : forall x, ch2c (c2ch x) = x.
Proof.
  move => [C1 C2]. rewrite /ch2c /c2ch.  
  by rewrite !ch2gT_gT2ch. 
Qed. 

 Lemma cipher_encoding_correct : forall b c m,
     c2ch (g ^+ b, ch2m m * g ^+ c) = c2ch ((ch2c (c2ch (g ^+ b, g ^+ c))).1, ch2m m * (ch2c (c2ch (g ^+ b, g ^+ c))).2).
 Proof.
   move => b c m. by rewrite !ch2c_c2ch.
 Qed.


Lemma game_hop : forall A Hdisj1 Hdisj2 Hdisj1' Hdisj2',
  @AdvantageE _ (ots_real_vs_rnd false) (ots_real_vs_rnd true) A Hdisj1 Hdisj2 =
  @AdvantageE _ (Aux ∘ DH_real) (Aux ∘ DH_rnd) A Hdisj1' Hdisj2'.
Proof.
  rewrite /AdvantageE => A Hdisj1 Hdisj2 Hdisj1' Hdisj2'.
  have HR : Pr (A ∘ ots_real_vs_rnd false) true = Pr (A ∘ Aux ∘ DH_rnd) true.
  { apply: GRing.subr0_eq. apply: normr0_eq0.
    (* strangely this does not fold *)
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
      - by rewrite /L_locs_counter.
      - by rewrite /DH_loc -fset_cat /=.
      - rewrite /RHS0 /=.
        f_equal. extensionality counter.
        f_equal. by destruct counter eqn:Hcounter.
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
      - by rewrite /L_locs_counter.
      - by rewrite /DH_loc -fset_cat /=.
      - rewrite /LHS0 /=.
        f_equal. extensionality counter.
        f_equal. destruct counter eqn:Hcounter; rewrite //=.
        f_equal. extensionality a.
        f_equal. f_equal. f_equal. extensionality b.
        f_equal. f_equal.
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

Lemma counter_DH_loc : (fset [:: counter_loc] :|: DH_loc) = fset ([:: counter_loc; pk_loc; sk_loc]).
Proof.
  rewrite /DH_loc.
  apply eq_fset => x.
  by rewrite in_fsetU !in_fset  mem_seq1 mem_seq2 mem_seq3.
Qed.

Lemma counter_pk_sk_disj : fset [:: counter_loc] :&: fset [:: pk_loc; sk_loc] == fset0 .
Proof.
  apply /eqP.
  apply eq_fset => x.
  rewrite in_fsetI in_fset0.
  apply: negPf. apply /andP.  move => [H1 H2].
  rewrite in_fset mem_seq1 in H1. move/eqP: H1. move => H1. subst.
  rewrite in_fset mem_seq2 in H2. move /orP: H2. move => [K | K]; move /eqP : K ; move => K ; inversion K.
Qed.

Theorem ElGamal_OT (dh_secure : DH_security) : OT_rnd_cipher.
Proof.
  rewrite /OT_rnd_cipher.
  move => A /= Hdisj1 Hdisj2.  unfold L_locs_counter in Hdisj1, Hdisj2.
  rewrite /Advantage.
  fold (@AdvantageE _ (ots_real_vs_rnd false) (ots_real_vs_rnd true) A Hdisj1 Hdisj2).
  rewrite game_hop.
  1: { simpl (Aux ∘ DH_real).π1. rewrite /DH_loc counter_DH_loc. assumption. }
  2: {
  rewrite /AdvantageE => H1 H2. rewrite !link_assoc.
  have H1' : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) (A ∘ Aux).π1 (DH_real).π1.
  { simpl (A ∘ Aux).π1. simpl (DH_real).π1. simpl (Aux ∘ DH_real).π1 in H1. unfold DH_loc in *.
    unfold fdisjoint in *.
    rewrite fsetIUr in H1.
    rewrite fsetU_eq0 in H1.
    move /andP: H1 => [H11 H12].
    move /eqP : H12 => H12.
    rewrite fsetIUl H12 fset0U.
    exact: counter_pk_sk_disj.
  }
  have H2' : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) (A ∘ Aux).π1 (DH_rnd).π1.
  { simpl (A ∘ Aux).π1. simpl (DH_rnd).π1. simpl (Aux ∘ DH_rnd).π1 in H1. unfold DH_loc in *.
    unfold fdisjoint in *.
    rewrite fsetIUr in H2.
    rewrite fsetU_eq0 in H2.
    move /andP: H2 => [H21 H22].
    move /eqP : H22 => H22.
    rewrite fsetIUl H22 fset0U.
    exact: counter_pk_sk_disj.
  }
  fold (@AdvantageE _ DH_real DH_rnd (A ∘ Aux) H1' H2').
    by apply: dh_secure. }
  simpl (Aux ∘ DH_rnd).π1. rewrite /DH_loc counter_DH_loc. assumption.
Qed.

