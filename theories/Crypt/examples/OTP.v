(*
  OTP example
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
     fingroup.fingroup
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
     pkg_composition
     pkg_rhl
     pkg_notation
     Package
     Prelude.

From Crypt Require Import pkg_notation.

From Coq Require Import Utf8 Lia.
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

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.

Module Type SymmetricSchemeParam.

  Parameter N : nat.
  Parameter N_pos : Positive N.
  Existing Instance N_pos.
  Parameters Words Key : finType.
  Parameter w0 : Words.
  Parameter k0 : Key.
  Parameter plus : Words -> Key -> Words.
  Notation "m ⊕ k" := (plus m k) (at level 70).
  Parameter plus_involutive : forall m k, (m ⊕ k) ⊕ k = m.

End SymmetricSchemeParam.

(* Symmetric Schemes *)
Module Type SymmetricSchemeRules (π : SymmetricSchemeParam).

  Import π.
  Inductive probEmpty : Type -> Type := .

  Module genparam <: RulesParam.

    Definition probE : Type -> Type := probEmpty.
    Definition rel_choiceTypes : Type := void.
    Definition chEmb : rel_choiceTypes -> choiceType.
    Proof. move => v. inversion v. Defined.
    Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
    Proof. move => T v. inversion v. Defined.
    Definition Hch : forall r : rel_choiceTypes, chEmb r.
    Proof. move => v. inversion v. Defined.

  End genparam.

  Variant Index :=
  | i_words : Index
  | i_key  : Index.

  Module Uparam <: UniformParameters.

    Definition Index : Type := Index.
    Definition i0 : Index := i_words.
    Definition fin_family : Index -> finType := fun i => match i with
                                                    | i_words   => Words
                                                    | i_key    => Key
                                                    end.

    Definition F_w0 : forall i : Index, (fin_family i).
    Proof.
      rewrite /fin_family.
      case.
      - exact w0.
      - exact k0.
    Defined.

  End Uparam.

  Module MyRules := DerivedRulesUniform genparam Uparam.

End SymmetricSchemeRules.

Module OTP_example.

  Parameter n : nat.
  Parameter n_pos : Positive n.

  Lemma expn2n : (succn (succn (Zp_trunc (2^n)))) = (2^n)%N.
  Proof.
    apply Zp_cast.
    have n_pos : (lt 0 n).
    { have := n_pos. apply /ltP. }
    simpl.
    destruct n as [| n].
    + apply /ltP; intuition.
    + rewrite expnS.
      move : (PositiveExp2 n).
      rewrite /Positive !mulSnr=> Hpos.
      change (0 * ?n ^ ?m)%N with (0%N).
      set (m := (2^n)%N) in *; clearbody m.
      apply /ltP.
      apply PeanoNat.Nat.lt_sub_lt_add_l.
      move: Hpos.
      case m.
      ++ move=> Hcontra.
          have falso := PeanoNat.Nat.lt_irrefl 0.
          exfalso.
          apply falso.
          apply /ltP. apply Hcontra.
      ++ move=> n'; apply /ltP.
  Qed.

  Module π <: SymmetricSchemeParam.

    Definition N : nat := 2^(@mkpos n n_pos).
    Definition N_pos : Positive N := _.
    Definition Words : finType := [finType of 'Z_(mkpos N)].
    Definition Key : finType := [finType of 'Z_(mkpos N)].
    Definition w0 : Words := 0.
    Definition k0 : Key := 0.
    Program Definition plus : Words -> Key -> Words :=
      fun w k => @Ordinal _ (BinNat.N.to_nat (BinNat.N.lxor (BinNat.N.of_nat (nat_of_ord w)) (BinNat.N.of_nat (nat_of_ord k)))) _.
    Next Obligation.
      destruct w as [w Hw], k as [k Hk].
      destruct w as [|Pw], k as [|Pk].
      1: { simpl. assumption. }
      1: { simpl.
           rewrite Pnat.SuccNat2Pos.id_succ.
           assumption. }
      1: { simpl.
           rewrite Pnat.SuccNat2Pos.id_succ.
           assumption. }
      remember (succn Pw) as w.
      remember (succn Pk) as k.
      assert (forall m, (2 ^ m)%nat = BinNat.N.to_nat
                              (BinNat.N.pow (BinNums.Npos (BinNums.xO 1%AC)) (BinNat.N.of_nat m))) as H.
      { induction m.
        - reflexivity.
        - rewrite expnSr.
          rewrite Nnat.Nat2N.inj_succ.
          rewrite BinNat.N.pow_succ_r'.
          rewrite Nnat.N2Nat.inj_mul.
          rewrite PeanoNat.Nat.mul_comm.
          apply f_equal2.
          + apply IHm.
          + reflexivity. }
      unfold N in *.
      move: (BinNat.N.log2_lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) => Hbound.
      assert (BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat w)) (BinNat.N.of_nat n)) as H1.
      { rewrite -BinNat.N.log2_lt_pow2.
        2: { rewrite Heqw. rewrite Nnat.Nat2N.inj_succ.
             apply BinNat.N.lt_0_succ. }
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
        2: { rewrite Heqk. rewrite Nnat.Nat2N.inj_succ.
             apply BinNat.N.lt_0_succ. }
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
      1: { simpl. move: H0. move /eqP => H0. rewrite H0. simpl.
           rewrite expn2n.
           rewrite expn_gt0. apply /orP. left. auto. }
      move: (BinNat.N.le_lt_trans _ _ _ Hbound Hm).
      rewrite -BinNat.N.log2_lt_pow2.
      2: { apply BinNat.N.neq_0_lt_0.
           move: H0. move /eqP. auto. }
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
    Lemma plus_involutive : forall m k, (m ⊕ k) ⊕ k = m.
    Proof.
      move => m k.
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

    Lemma plus_comm : forall m k, (m ⊕ k) = (k ⊕ m).
    Proof.
      move=> m k.
      move: ord_inj => Hordinj.
      unfold injective in Hordinj.
      apply Hordinj.
      destruct m. cbn.
      by rewrite BinNat.N.lxor_comm.
    Qed.

    Lemma plus_assoc : forall m n k, ((m ⊕ n) ⊕ k) = (m ⊕ (n ⊕ k)).
    Proof.
      move=> m n k.
      move: ord_inj => Hordinj.
      unfold injective in Hordinj.
      apply Hordinj.
      destruct m. cbn.
      rewrite !Nnat.N2Nat.id.
      by rewrite BinNat.N.lxor_assoc.
    Qed.

  End π.

  Local Open Scope package_scope.

  Import π.
  Include (SymmetricSchemeRules π).

  Module MyPackage := Package_Make (MyRules.myparamU).
  Import MyPackage.
  Import PackageNotation.
  Export MyRules.

  Definition i1 : nat := 0.

  Definition U (i : Index) : Op :=
    existT _ (inl (inl i)) (inl (Uni_W i)).

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).

  Definition Enc {L : {fset Location}} (m : Words) (k : Key) :
    code L [interface] Words :=
    {code
       ret (m ⊕ k)
    }.

  Definition KeyGen {L : {fset Location}} :
    code L [interface] Key :=
    {code
       k <$ U (i_key) ;;
       ret k
    }.

  Definition dec {L : {fset Location }}(c : Words) (k : Key) :
    code L [interface] Words := Enc k c.

  Definition IND_CPA_location : {fset Location} := fset0.

  Definition key2ch : Key -> 'fin (2^n)%N.
    move=> [k kpos].
    rewrite expn2n in kpos.
    exists k.
    exact: kpos.
  Qed.

  Definition words2ch : Words -> 'fin (2^n)%N.
    move=> [w wpos].
    rewrite expn2n in wpos.
    exists w.
    exact wpos.
  Qed.

  Definition ch2words : 'fin (2^n)%N -> Words.
    move=> [n Hn].
    exists n.
    simpl in Hn. rewrite -expn2n in Hn.
    exact Hn.
  Qed.

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
          k_val <$ U (i_key) ;;
          r ← (Enc (ch2words m) k_val) ;;
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
          m'    <$ (U i_words) ;;
          k_val <$ (U i_key) ;;
          r     ← Enc m' k_val ;;
          ret (words2ch r)
        }
      ].

  Definition IND_CPA : loc_GamePair [interface val #[i1] : chWords → chWords ] :=
    λ (b : bool),
      if b then {locpackage IND_CPA_real}
           else {locpackage IND_CPA_ideal}.

  Local Open Scope ring_scope.

  (* One-sided sampling rule. *)
  (* Removes the need for intermediate games in some cases. *)
  Lemma rconst_samplerL :
    ∀ {B : ord_choiceType} {D}
      (c₀ : (Arit D) -> raw_code B) (c₁ : raw_code B) (post : postcond B B),
      (forall x, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
      ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← sample D ;; c₀ x ≈ c₁ ⦃ post ⦄.
  Proof.
    intros B D c₀ c₁ post h.
    eapply r_transR with (x ← sample D ;; (fun _ => c₁) x).
    - apply rdead_sampler_elimL.
      apply rreflexivity_rule.
    - ssprove_same_head_r.
      apply h.
  Qed.

  Lemma IND_CPA_ideal_real : (IND_CPA false) ≈₀ (IND_CPA true).
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.

    apply rconst_samplerL=>m_val.
    pose f := (fun k => k ⊕ ch2words m ⊕ m_val).
    have f_bij : bijective f.
    { apply Bijective with (g:= fun x => (x ⊕ m_val ⊕ ch2words m)).
      1-2: rewrite /f /cancel=> x; by rewrite !plus_involutive.
    }
    eapply rpost_weaken_rule with eq.
    2: { by move=> [? ?] [? ?] [-> ->]. }
    apply (
      @rpost_conclusion_rule_cmd _ _ _
        (λ '(s₀,s₁), s₀ = s₁)
        (cmd_sample (U i_key))
        (cmd_sample (U i_key))
        (λ k, words2ch (m_val ⊕ k))
        (λ k, words2ch (ch2words m ⊕ k))
    ).
    eapply rpost_weaken_rule with (fun '(w1, s1) '(w2, s2) => s1 = s2 /\ f w1 == w2).
    { (* NOTE: Is it really needed change judgement here? *)
      rewrite rel_jdgE. rewrite repr_cmd_bind.
      simpl (repr (ret _)).
      rewrite bindrFree_ret.
      have Huni := (@Uniform_bij_rule i_key i_key _ _ f f_bij (fun '(s₀, s₁) => s₀ = s₁)).
      apply Huni.
    }
    move=> [k1 s1] [k2 s2] [-> Hxor].
    rewrite /f in Hxor.
    apply reflection_nonsense in Hxor.
    have <- : (k2 ⊕ ch2words m) = (ch2words m ⊕ k2).
    { apply plus_comm. }
    rewrite plus_assoc plus_comm plus_assoc plus_comm in Hxor.
    rewrite -Hxor !plus_involutive.
    split; reflexivity.
  Qed.

  Theorem unconditional_secrecy :
    ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords ],
      Advantage IND_CPA A = 0.
  Proof.
    move=> A.
    rewrite Advantage_E IND_CPA_ideal_real //; apply fdisjoints0.
  Qed.

End OTP_example.
