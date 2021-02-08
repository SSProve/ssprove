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
  (* ER: ; kg_loc ; enc_loc ; dec_loc ; challenge_loc ; pk_loc; sk_loc]. *)

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
  Definition pk2ch_aux (i : nat) (Hi : (i < #[g])%N)  : (chFin PubKey_len_pos).
  Proof.
    exists i.
    rewrite orderE in Hi.
    rewrite /= -cardsT. 
    setoid_rewrite g_gen.
    assumption.
  Defined. 
  
  Definition pk2ch : PubKey -> (chFin PubKey_len_pos).
  Proof.
    move => /= A.  
    destruct (@cyclePmin gT g A) as [i Hi]. 
    { rewrite -g_gen. 
      apply: in_setT. } 
    exact: pk2ch_aux i Hi. 
  Defined. 
  
  Definition ch2pk : (chFin PubKey_len_pos) -> PubKey.
  Proof.
    move => /= [i Hi]. exact: (g^+i).
  Defined. 

  (* *)
  Definition sk2ch : SecKey -> (chFin SecKey_len_pos).
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
  Definition m2ch : Plain -> (chFin Plain_len_pos) := pk2ch. 
  Definition ch2m : (chFin Plain_len_pos) -> Plain := ch2pk. 
  (* *)
  Definition c2ch  : Cipher -> (chFin Cipher_len_pos).
  Proof.
    move => [g1 g2] /=. 
    rewrite card_prod. 
    apply: mxvec_index.
    - exact: pk2ch g1.
    - exact: pk2ch g2.
  Defined.     
  
  Definition ch2c : (chFin Cipher_len_pos) -> Cipher.
  Proof.
    rewrite /=. rewrite card_prod.
    move => ij. destruct (@pair_of_mxvec_index #|gT| #|gT| ij) as [i j]. 
    - by apply: mxvec_indexP.
    - exact: (g^+i, g^+j).
  Defined.
  
  (* (* Key Generation algorithm *) *)
  Definition KeyGen { L : {fset Location} }: program L fset0 ((chFin PubKey_len_pos) × (chFin SecKey_len_pos)) :=
    x <$ (U i_sk) ;;
    ret ( pk2ch (g^+x), sk2ch x).
           
  (* Encryption algorithm *)
  Definition Enc { L : {fset Location} } (pk : chFin PubKey_len_pos) (m : chFin Plain_len_pos) : program L fset0 (chFin Cipher_len_pos) :=
    y <$ (U i_sk) ;;
    ret (c2ch (g^+y, (ch2pk pk)^+y * (ch2m m))).


  (* Decryption algorithm *)
  Definition Dec_open { L : {fset Location} } (sk : chFin SecKey_len_pos) (c : chFin Cipher_len_pos) :
    program L fset0 (chFin Plain_len_pos) := 
               ret (m2ch ( (fst (ch2c c)) * ( (snd (ch2c c))^-(ch2sk sk)) )).

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
Definition Aux_DH_real (m : 'I_#|gT|) :  program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption (chFin Cipher_len_pos)).
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
Definition Aux_DH_rnd (m : 'I_#|gT|) :  program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption (chFin Cipher_len_pos)).
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

Definition LHS0 (m : 'I_#|gT|) : program (fset [:: counter_loc; pk_loc; sk_loc ])  fset0 (chOption (chFin Cipher_len_pos)).
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


Definition RHS0 (m : 'I_#|gT|) : program (fset [:: counter_loc; pk_loc; sk_loc ]) fset0 (chOption (chFin Cipher_len_pos)).
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

Lemma group_OTP_math { L : {fset  Location } } : forall m (s : heap_choiceType),
   MyAlg.MyPackage.θ_dens
     (MyAlg.MyPackage.θ0
        (@repr _ L ( (b ← (b ← sample U i_sk ;; ret b) ;;
                      c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c)))))) s) =
   MyAlg.MyPackage.θ_dens
     (MyAlg.MyPackage.θ0
        (@repr _ L ((b ← (b ← sample U i_sk ;; ret b) ;; c ← (c ← sample U i_sk ;; ret c) ;;
                     ret (Some (c2ch (g ^+ b, g ^+ c)))))) s). 
Admitted. (* CA: look for an informal proof of this in the CertyCrypt paper *)
  
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
  (*CA:
   1. sampling c <$ U i_cipher is the same as sampling two element of the group say (C1,C2) <$ U (G × G) 
   2. the map (g^+_, g^+_) is a bijection and we can use the uniform bij rule.
 *) Admitted.  
  
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


(*CA: it would be good to prove these before the deadline *)
Lemma pkch_i : forall i (H : (i < #[g])%N), ch2pk (pk2ch (g^+i)) = g^+i. 
Proof.
  move => i Hi.
  rewrite orderE in Hi.
  rewrite -g_gen in Hi.  
  rewrite cardsT in Hi.  
  rewrite /ch2pk. 
  have Heq: (pk2ch (g ^+i) ) = (@Ordinal _ i Hi)  by admit. 
  by rewrite Heq.
Admitted.   

Lemma pk_encoding_correct : forall p,
    ch2pk (pk2ch p ) = p.
Proof.
  move => /= A.
  destruct (@cyclePmin gT g A) as [i Hi].
  {  rewrite -g_gen. 
     apply: in_setT. }
  subst. exact: pkch_i. 
Qed.

Lemma ch2c_c2ch : forall x, ch2c (c2ch x) = x.
Proof.
Admitted. 

 
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
  
