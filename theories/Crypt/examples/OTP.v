(*
  OTP example
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl pkg_notation Package Prelude pkg_notation.
Set Warnings "-custom-entry-overriden".
From Crypt Require Import package_instance.
Set Warnings "custom-entry-overriden".

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

Local Open Scope ring_scope.

Module Type SymmetricSchemeParam.

  Parameter N : nat.
  Parameter N_pos : Positive N.
  Existing Instance N_pos.
  Parameters Words Key : finType.
  Parameter w0 : Words.
  Parameter k0 : Key.
  Parameter plus : Words → Key → Words.
  Notation "m ⊕ k" := (plus m k) (at level 70).
  Parameter plus_involutive : ∀ m k, (m ⊕ k) ⊕ k = m.

End SymmetricSchemeParam.

Module OTP_example.

  Parameter (n : nat).
  Parameter (n_pos : Positive n).

  Lemma expn2n : (succn (succn (Zp_trunc (2^n)))) = (2^n)%N.
  Proof.
    apply Zp_cast.
    pose proof n_pos as n_pos.
    destruct n as [| k].
    1:{ inversion n_pos. }
    rewrite expnS.
    move: (PositiveExp2 k).
    rewrite /Positive !mulSnr => Hpos.
    change (0 * ?n ^ ?m)%N with 0%N.
    set (m := (2^ k)%N) in *. clearbody m.
    apply /ltP. move: Hpos => /ltP Hpos.
    apply PeanoNat.Nat.lt_sub_lt_add_l.
    move: Hpos.
    case m.
    1:{ intro h. inversion h. }
    intro n'. auto.
  Qed.

  Module π <: SymmetricSchemeParam.

    Definition N : nat := 2^n.

    Definition N_pos : Positive N := _.

    Definition Words : finType := [finType of 'Z_N].

    Definition Key : finType := [finType of 'Z_N].

    Definition w0 : Words := 0.

    Definition k0 : Key := 0.

    #[program] Definition plus : Words → Key → Words :=
      λ w k,
        @Ordinal _ (BinNat.N.to_nat (BinNat.N.lxor (BinNat.N.of_nat (nat_of_ord w)) (BinNat.N.of_nat (nat_of_ord k)))) _.
    Next Obligation.
      destruct w as [w Hw], k as [k Hk].
      destruct w as [|Pw], k as [|Pk].
      1:{ simpl. assumption. }
      1:{
        simpl.
        rewrite Pnat.SuccNat2Pos.id_succ.
        assumption.
      }
      1:{
        simpl.
        rewrite Pnat.SuccNat2Pos.id_succ.
        assumption.
      }
      remember (succn Pw) as w.
      remember (succn Pk) as k.
      assert (H :
        ∀ m,
          (2 ^ m)%nat =
          BinNat.N.to_nat
            (BinNat.N.pow (BinNums.Npos (BinNums.xO 1%AC)) (BinNat.N.of_nat m))
      ).
      { induction m.
        - reflexivity.
        - rewrite expnSr.
          rewrite Nnat.Nat2N.inj_succ.
          rewrite BinNat.N.pow_succ_r'.
          rewrite Nnat.N2Nat.inj_mul.
          rewrite PeanoNat.Nat.mul_comm.
          apply f_equal2.
          + apply IHm.
          + reflexivity.
      }
      unfold N in *.
      move: (BinNat.N.log2_lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) => Hbound.
      assert (BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat w)) (BinNat.N.of_nat n)) as H1.
      { rewrite -BinNat.N.log2_lt_pow2.
        2:{
          rewrite Heqw. rewrite Nnat.Nat2N.inj_succ.
          apply BinNat.N.lt_0_succ.
        }
        unfold BinNat.N.lt.
        rewrite Nnat.N2Nat.inj_compare.
        rewrite PeanoNat.Nat.compare_lt_iff.
        rewrite Nnat.Nat2N.id.
        rewrite -H.
        apply /ltP.
        unfold Zp_trunc in *.
        rewrite expn2n in Hw.
        apply Hw.
      }
      assert (BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat k)) (BinNat.N.of_nat n)) as H2.
      { rewrite -BinNat.N.log2_lt_pow2.
        2:{
          rewrite Heqk. rewrite Nnat.Nat2N.inj_succ.
          apply BinNat.N.lt_0_succ.
        }
        unfold BinNat.N.lt.
        rewrite Nnat.N2Nat.inj_compare.
        rewrite PeanoNat.Nat.compare_lt_iff.
        rewrite Nnat.Nat2N.id.
        rewrite -H.
        apply /ltP.
        rewrite expn2n in Hk.
        apply Hk.
      }
      move: (BinNat.N.max_lub_lt _ _ _ H1 H2) => Hm.
      destruct ((BinNat.N.lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) == BinNat.N0) eqn:H0.
      1:{
        simpl. move: H0. move /eqP => H0. rewrite H0. simpl.
        rewrite expn2n. rewrite expn_gt0. apply /orP. left. auto.
      }
      move: (BinNat.N.le_lt_trans _ _ _ Hbound Hm).
      rewrite -BinNat.N.log2_lt_pow2.
      2:{
        apply BinNat.N.neq_0_lt_0.
        move: H0. move /eqP. auto.
      }
      unfold BinNat.N.lt.
      rewrite Nnat.N2Nat.inj_compare.
      rewrite PeanoNat.Nat.compare_lt_iff.
      move => Hlt.
      apply /ltP.
      simpl in *.
      rewrite H.
      rewrite -H expn2n H.
      assumption.
    Qed.

    Notation "m ⊕ k" := (plus m k) (at level 70).

    Lemma plus_involutive : ∀ m k, (m ⊕ k) ⊕ k = m.
    Proof.
      intros m k.
      move: ord_inj => Hordinj.
      unfold injective in Hordinj.
      apply Hordinj.
      destruct m. cbn.
      rewrite Nnat.N2Nat.id.
      rewrite BinNat.N.lxor_assoc.
      rewrite BinNat.N.lxor_nilpotent.
      rewrite BinNat.N.lxor_0_r.
      rewrite Nnat.Nat2N.id.
      reflexivity.
    Qed.

    Lemma plus_comm : ∀ m k, (m ⊕ k) = (k ⊕ m).
    Proof.
      intros m k.
      move: ord_inj => Hordinj.
      unfold injective in Hordinj.
      apply Hordinj.
      destruct m. cbn.
      rewrite BinNat.N.lxor_comm. reflexivity.
    Qed.

    Lemma plus_assoc : ∀ m n k, ((m ⊕ n) ⊕ k) = (m ⊕ (n ⊕ k)).
    Proof.
      intros m n k.
      move: ord_inj => Hordinj.
      unfold injective in Hordinj.
      apply Hordinj.
      destruct m. cbn.
      rewrite !Nnat.N2Nat.id.
      rewrite BinNat.N.lxor_assoc. reflexivity.
    Qed.

  End π.

  #[local] Open Scope package_scope.

  Import π.

  Definition i1 : nat := 0.

  Definition U (i : Index) : Op :=
    existT _ ('fin i) (inl (Uni_W i)).

  Definition i_words : positive := mkpos (2^n)%N.
  Definition i_key : positive := mkpos (2^n)%N.

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).

  Definition key2ch : Key → 'fin (2^n)%N.
  Proof.
    intros [k kpos].
    rewrite expn2n in kpos.
    exists k.
    exact kpos.
  Defined.

  Definition ch2key : 'fin (2^n)%N → Key.
  Proof.
    intros [n Hn].
    exists n.
    simpl in Hn. rewrite -expn2n in Hn.
    exact Hn.
  Defined.

  Definition words2ch : Words → 'fin (2^n)%N.
  Proof.
    intros [w wpos].
    exists w.
    rewrite expn2n in wpos.
    exact wpos.
  Defined.

  Definition ch2words : 'fin (2^n)%N → Words.
  Proof.
    intros [n Hn].
    exists n.
    simpl in Hn. rewrite -expn2n in Hn.
    exact Hn.
  Defined.

  Lemma words2ch_ch2words :
    ∀ x, words2ch (ch2words x) = x.
  Proof.
    intros x.
    unfold words2ch, ch2words.
    destruct x. f_equal. apply bool_irrelevance.
  Qed.

  Lemma ch2words_words2ch :
    ∀ x, ch2words (words2ch x) = x.
  Proof.
    intros x.
    unfold words2ch, ch2words.
    destruct x. f_equal. apply bool_irrelevance.
  Qed.

  Lemma words2ch_ch2key :
    ∀ x, words2ch (ch2key x) = x.
  Proof.
    intros x.
    unfold words2ch, ch2key.
    destruct x. f_equal. apply bool_irrelevance.
  Qed.

  Lemma ch2key_words2ch :
    ∀ x, ch2key (words2ch x) = x.
  Proof.
    intros x.
    unfold words2ch, ch2key.
    destruct x. f_equal. apply bool_irrelevance.
  Qed.

  Opaque key2ch ch2key words2ch ch2words.

  Definition Enc {L : {fset Location}} (m : Words) (k : Key) :
    code L [interface] Words :=
    {code
       ret (m ⊕ k)
    }.

  Definition KeyGen {L : {fset Location}} :
    code L [interface] Key :=
    {code
       k ← sample U i_key ;;
       ret (ch2key k)
    }.

  Definition dec {L : {fset Location }}(c : Words) (k : Key) :
    code L [interface] Words := Enc k c.

  Definition IND_CPA_location : {fset Location} := fset0.

  (* REM: Key is always sampled at the side of the encrypter. *)
  (* This assumption is stronger than usual crypto definitions. *)
  (* We need control over the key to apply coupling. *)
  Definition IND_CPA_real :
    package IND_CPA_location
      [interface]
      [interface val #[i1] : chWords → chWords ] :=
    [package
        def #[i1] (m : chWords) : chWords
        {
          k_val ← sample U i_key ;;
          r ← Enc (ch2words m) (ch2key k_val) ;;
          ret (words2ch r)
        }
    ].

  Definition IND_CPA_ideal :
    package IND_CPA_location
      [interface ]
      [interface val #[i1] : chWords → chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords
      {
        m'    ← sample U i_words ;;
        k_val ← sample U i_key ;;
        r     ← Enc (ch2words m') (ch2key k_val) ;;
        ret (words2ch r)
      }
    ].

  Definition IND_CPA : loc_GamePair [interface val #[i1] : chWords → chWords ] :=
    λ b,
      if b then {locpackage IND_CPA_real}
           else {locpackage IND_CPA_ideal}.

  (** Technical step

    Uniform distrbutions are not factorised yet so we have to inline rules
    in examples. Hopefully this will go away in the future.

  *)

  Lemma r_uniform_bij :
    ∀ {A₀ A₁ : ord_choiceType} i j pre post f
      (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
      bijective f →
      (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
      ⊢ ⦃ pre ⦄
        x ← sample U i ;; c₀ x ≈
        x ← sample U j ;; c₁ x
      ⦃ post ⦄.
  Proof.
    intros A₀ A₁ i j pre post f c₀ c₁ bijf h.
    rewrite rel_jdgE.
    change (repr (sampler (U ?i) ?k))
    with (bindrFree (@Uniform_F i heap_choiceType) (λ x, repr (k x))).
    eapply bind_rule_pp.
    - eapply Uniform_bij_rule. eauto.
    - intros a₀ a₁. simpl.
      rewrite <- rel_jdgE.
      eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
      move: e => /eqP e. subst.
      eapply rpre_weaken_rule. 1: eapply h.
      intros h₀ h₁. simpl. intros [? ?]. subst. auto.
  Qed.

  (* End of technical step *)

  #[local] Open Scope ring_scope.

  Lemma IND_CPA_ideal_real :
    IND_CPA false ≈₀ IND_CPA true.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    apply rconst_samplerL. intro m_val.
    pose (f := λ (k : Arit (U i_key)), words2ch (ch2key k ⊕ ch2words m ⊕ (ch2words m_val))).
    assert (bij_f : bijective f).
    { subst f.
      exists (λ x, words2ch (ch2words x ⊕ (ch2words m_val) ⊕ ch2words m)).
      - intro x. rewrite ch2words_words2ch. rewrite !plus_involutive.
        apply words2ch_ch2key.
      - intro x. rewrite ch2key_words2ch. rewrite !plus_involutive.
        apply words2ch_ch2words.
    }
    eapply r_uniform_bij with (1 := bij_f). intro k_val.
    apply r_ret. intros s₀ s₁ e. intuition auto.
    subst f. simpl. f_equal.
    rewrite ch2key_words2ch.
    rewrite <- plus_assoc.
    rewrite [X in _ = X]plus_comm. f_equal.
    rewrite plus_comm. rewrite plus_involutive.
    reflexivity.
  Qed.

  Theorem unconditional_secrecy :
    ∀ LA A,
      ValidPackage LA
        [interface val #[i1] : chWords → chWords ] A_export A →
      Advantage IND_CPA A = 0.
  Proof.
    intros LA A vA.
    rewrite Advantage_E. eapply IND_CPA_ideal_real. 1: eauto.
    all: eapply fdisjoints0.
  Qed.

End OTP_example.
