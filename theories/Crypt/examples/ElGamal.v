(** ElGamal encryption scheme.

  We show that DH security implies the security of ElGamal.

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition pkg_chUniverse pkg_composition pkg_rhl Package Prelude
  pkg_notation AsymScheme.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.
Import mc_1_10.Num.Theory.

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

Lemma group_prodC :
  ∀ x y : gT, x * y = y * x.
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


Inductive probEmpty : Type → Type := .

Module MyParam <: AsymmetricSchemeParams.

  Definition SecurityParameter : choiceType := nat_choiceType.
  Definition Plain  : finType := FinGroup.arg_finType gT.
  Definition Cipher : finType :=
    prod_finType (FinGroup.arg_finType gT) (FinGroup.arg_finType gT).
  Definition PubKey : finType := FinGroup.arg_finType gT.
  Definition SecKey : finType := [finType of 'Z_q].

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

  Definition probE : Type → Type := probEmpty.
  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes → choiceType.
  Proof.
    intro. contradiction.
  Defined.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intro. contradiction.
  Defined.

  Definition Hch : ∀ r : rel_choiceTypes, chEmb r.
  Proof.
    intro. contradiction.
  Defined.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.
  Module asym_rules := (ARules MyParam).
  Import asym_rules.
  Include (Package_Make myparamU).

  Module MyPackage := Package_Make myparamU.

  Import MyPackage.
  Import PackageNotation.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := ('nat ; 1%N).
  Definition sk_loc : Location := ('nat ; 2%N).
  Definition m_loc  : Location := ('nat ; 3%N).
  Definition c_loc  : Location := ('nat ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)

  (* Will subsume both Plain and PubKey positivity proofs
    The idea is that the proofs don't get in the way.
  *)
  Instance gT_card_pos : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists plain0. auto.
  Qed.

  Definition Plain_len_pos := gT_card_pos.

  (* We have to keep it to make the module mechanism happy. *)
  Definition PubKey_len_pos : Positive #|PubKey|.
  Proof.
    apply /card_gt0P. by exists pub0.
  Defined.

  Instance Cipher_len_pos : Positive #|Cipher|.
  Proof.
    apply /card_gt0P. by exists cipher0.
  Qed.

  Instance SecKey_len_pos : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. by exists sec0.
  Qed.

  Notation " 'chSecurityParameter' " :=
    ('nat) (in custom pack_type at level 2).
  Notation " 'chPlain' " :=
    ('fin #|Plain|)
    (in custom pack_type at level 2).
  Notation " 'chCipher' " :=
    ('fin #|Cipher|)
    (in custom pack_type at level 2).
  Notation " 'chPubKey' " :=
    ('fin #|PubKey|)
    (in custom pack_type at level 2).
  Notation " 'chSecKey' " :=
    ('fin #|SecKey|)
    (in custom pack_type at level 2).

  Definition U (i : Index) :
    {rchT : myparamU.rel_choiceTypes &
            myparamU.probE (myparamU.chEmb rchT)} :=
    (existT (λ rchT : myparamU.rel_choiceTypes, myparamU.probE (chEmb rchT))
            (inl (inl i)) (inl (Uni_W i))).

  (* *)
  Definition pk2ch_aux (i : nat) (Hi : (i < #[g])%N) : 'fin #|PubKey|.
  Proof.
    exists i.
    rewrite orderE in Hi.
    rewrite /= -cardsT.
    setoid_rewrite g_gen.
    assumption.
  Defined.

  Definition pk2ch : PubKey → 'fin #|PubKey|.
  Proof.
    move => /= A.
    destruct (@cyclePmin gT g A) as [i Hi].
    { rewrite -g_gen.
      apply: in_setT. }
    exact: pk2ch_aux i Hi.
  Defined.

  Definition ch2pk : 'fin #|PubKey| → PubKey.
  Proof.
    move => /= [i Hi]. exact: (g^+i).
  Defined.

  (* *)
  Definition sk2ch : SecKey → 'fin #|SecKey|.
  Proof.
    move => /= [a Ha].
    exists a.
    rewrite card_ord. assumption.
  Defined.

  Definition ch2sk : 'fin #|SecKey| → SecKey.
    move => /= [a Ha].
    exists a.
    rewrite card_ord in Ha. assumption.
  Defined.

  (* *)
  Definition m2ch : Plain → 'fin #|Plain| := pk2ch.
  Definition ch2m : 'fin #|Plain| → Plain := ch2pk.

  (* *)
  Definition c2ch : Cipher → 'fin #|Cipher|.
  Proof.
    move => [g1 g2] /=.
    rewrite card_prod.
    apply: mxvec_index.
    - exact: pk2ch g1.
    - exact: pk2ch g2.
  Defined.

  Definition ch2c : 'fin #|Cipher| → Cipher.
  Proof.
    rewrite /=. rewrite card_prod.
    move => ij. destruct (@pair_of_mxvec_index #|gT| #|gT| ij) as [i j].
    - by apply: mxvec_indexP.
    - exact: (g^+i, g^+j).
  Defined.

  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    program L [interface] ('fin #|PubKey| × 'fin #|SecKey|) :=
    {program
      x ← sample U i_sk ;;
      ret (pk2ch (g^+x), sk2ch x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : 'fin #|PubKey|) (m : 'fin #|Plain|) :
    program L [interface] ('fin #|Cipher|) :=
    {program
      y ← sample U i_sk ;;
      ret (c2ch (g^+y, (ch2pk pk)^+y * (ch2m m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : 'fin #|SecKey|) (c : 'fin #|Cipher|) :
    program L [interface] ('fin #|Plain|) :=
    {program
      ret (m2ch ((fst (ch2c c)) * ((snd (ch2c c))^-(ch2sk sk))))
    }.

End MyAlg.

Local Open Scope package_scope.

Module ElGamal_Scheme := AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg asym_rules MyPackage ElGamal_Scheme PackageNotation.

Lemma counter_loc_in :
  counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma pk_loc_in :
  pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma sk_loc_in :
  sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Definition DH_loc := fset [:: pk_loc ; sk_loc].

Definition DH_real :
  package DH_loc [interface]
    [interface val #[10] : 'unit → chPubKey × chCipher ] :=
    [package
      def #[10] (_ : 'unit) : chPubKey × chCipher
      {
        a ← sample U i_sk ;;
        b ← sample U i_sk ;;
        put pk_loc := pk2ch (g^+a) ;;
        put sk_loc := sk2ch a ;;
        ret (pk2ch (g^+a), c2ch (g^+b, g^+(a * b)))
      }
    ].

Definition DH_rnd :
  package DH_loc [interface]
    [interface val #[10] : 'unit → chPubKey × chCipher ] :=
    [package
      def #[10] (_ : 'unit) : chPubKey × chCipher
      {
        a ← sample U i_sk ;;
        b ← sample U i_sk ;;
        c ← sample U i_sk ;;
        put pk_loc := pk2ch (g^+a) ;;
        put sk_loc := sk2ch a ;;
        ret (pk2ch (g^+a), c2ch (g^+b, g^+c))
      }
    ].

Definition Aux :
  package (fset [:: counter_loc])
    [interface val #[10] : 'unit → chPubKey × chCipher]
    [interface val #[challenge_id'] : chPlain → 'option chCipher] :=
    [package
      def #[challenge_id'] (m : chPlain) : 'option chCipher
      {
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N ;;
        if (count == 0)%N then
          '(pk, c) ← op [ #[10] : 'unit → chPubKey × chCipher ] Datatypes.tt ;;
          ret (Some (c2ch ((ch2c c).1 , (ch2m m) * ((ch2c c).2))))
        else ret None
      }
    ].

Definition DH_security : Prop :=
  ∀ LA A,
    ValidPackage LA [interface val #[10] : 'unit → chPubKey × chCipher ] A_export A →
    fdisjoint LA DH_loc →
    AdvantageE DH_real DH_rnd A = 0.

(* TODO MOVE *)
Lemma AdvantageE_le_0 :
  ∀ G₀ G₁ A,
    AdvantageE G₀ G₁ A <= 0 →
    AdvantageE G₀ G₁ A = 0.
Proof.
  intros G₀ G₁ A h.
  unfold AdvantageE in *.
  rewrite mc_1_10.Num.Theory.normr_le0 in h.
  apply/mc_1_10.Num.Theory.normr0P. auto.
Qed.

(* TODO MOVE *)
Lemma Advantage_le_0 :
  ∀ G A,
    Advantage G A <= 0 →
    Advantage G A = 0.
Proof.
  intros G A h.
  rewrite -> Advantage_E in *. apply AdvantageE_le_0. auto.
Qed.

Theorem ElGamal_OT (dh_secure : DH_security) : OT_rnd_cipher.
Proof.
  unfold OT_rnd_cipher. intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  apply Advantage_le_0.
  rewrite Advantage_E.
  pose proof (
    Advantage_triangle_chain (ots_real_vs_rnd false) [::
      Aux ∘ DH_real ;
      Aux ∘ DH_rnd
    ] (ots_real_vs_rnd true) A
  ) as ineq.
  advantage_sum simpl in ineq.
  rewrite !GRing.addrA in ineq.
  eapply ler_trans. 1: exact ineq.
  clear ineq.
  rewrite -Advantage_link. erewrite dh_secure. 2: exact _.
  2:{
    rewrite fdisjointUl. apply/andP. split.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
    - unfold DH_loc. rewrite fset_cons. rewrite -fset0E. rewrite fsetU0.
      rewrite fdisjoint1s.
      apply/negP. intro e.
      rewrite in_fset in e. rewrite in_cons in e. rewrite mem_seq1 in e.
      move: e => /orP [/eqP e | /eqP e].
      all: discriminate.
  }
Admitted.

(* TODO OLD BELOW
  I will now try to salvage the parts that are necessary to conclude.
  The rest will be dropped.
*)

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



Lemma group_OTP { L : { fset Location } } : forall m,
    ⊨ ⦃ λ '(h1, h2), h1 = h2 ⦄
      @repr _ L ((c ← (c ← sample U i_cipher ;; ret c) ;; ret (Some (c2ch c))))  ≈
      @repr _ L ((b ← (b ← sample U i_sk ;; ret b) ;;
                  c ← (c ← sample U i_sk ;; ret c) ;; ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c))))) ⦃ eq ⦄.
Proof.
  move => m.
  unshelve apply: rrewrite_eqDistrL.
  { eapply (
        ((B ← (B ← sample U i_pk ;; ret B) ;;
          A ← (A ← sample U i_pk ;; ret A) ;; ret (Some (c2ch (B, A)))))). }
  { unshelve apply: rpost_weaken_rule.
    { exact : eq. }
    2: { by move => [a1 s1] [a2 s2]. }
    Check Uniform_bij_rule_sq.
(*CA: morally c2ch = pk2ch × pk2ch so after convinced Coq of this it suffices to apply
      Uniform_bij_rule_sq *) admit.
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


(*Rem.: it would be good to prove these before the deadline *)
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

