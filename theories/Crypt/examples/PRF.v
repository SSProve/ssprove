(** PRF Example

  Inspired by "State Separation for Code-Based Game-Playing Proofs"
  by Brzuska et al.

  Appendix A.

  "Given a pseudorandom function (PRF) we construct a symmetric encryption
  scheme that is indistinguishable under chosen plaintext attacks (IND-CPA)."

*)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Section PRF_example.

  Context (n : nat).

  Definition Words_N : nat := 2^n.
  Definition Words_N_pos : Positive Words_N := _.
  Definition Words : choice_type := chFin (mkpos Words_N).
  Definition Key_N : nat := 2^n.
  Definition Key_N_pos : Positive Key_N := _.
  Definition Key : choice_type := chFin (mkpos Key_N).

  (* TW: Is this normal that this definition is so big? *)
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
    assert (
      ∀ m,
        (2 ^ m)%nat = BinNat.N.to_nat (BinNat.N.pow (BinNums.Npos (BinNums.xO 1%AC)) (BinNat.N.of_nat m))
    ) as H.
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
    unfold Words_N, Key_N in *.
    move: (BinNat.N.log2_lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) => Hbound.
    assert (
      BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat w)) (BinNat.N.of_nat n)
    ) as H1.
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
      apply Hw.
    }
    assert (
      BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat k)) (BinNat.N.of_nat n)
    ) as H2.
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
      apply Hk.
    }
    move: (BinNat.N.max_lub_lt _ _ _ H1 H2) => Hm.
    destruct ((BinNat.N.lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) == BinNat.N0) eqn:H0.
    1:{
      simpl. move: H0. move /eqP => H0. rewrite H0. simpl.
      rewrite expn_gt0. apply /orP. left. auto.
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
    assumption.
  Qed.

  Notation "m ⊕ k" := (plus m k) (at level 70).

  Lemma plus_involutive :
    ∀ m k, (m ⊕ k) ⊕ k = m.
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

  #[local] Open Scope package_scope.

  Definition key_location : Location := (0, 'option Key).
  Definition plain_location : Location := (1, Words).
  Definition cipher_location : Location := (2, Words).
  Definition i0 : nat := 3.
  Definition i1 : nat := 4.
  Definition i2 : nat := 5.
  Definition salt_location : Location := (6, 'nat).
  Definition table_location : Location :=
    (7, chMap 'nat ('fin (2^n)%N)).

  Context (PRF : Words → Key → Key).

  Notation " 'word " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'key " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_key : nat := 2^n.
  Definition i_words : nat := 2^n.

  Definition enc {L : Locations} (m : Words) (k : Key) :
    code L [interface] ('fin (2^n) × 'fin (2^n)) :=
      {code
        r ← sample uniform i_words ;;
        let pad := PRF r k in
        let c := m ⊕ pad in
        ret (r, c)
      }.

  Definition kgen : code emptym [interface] 'fin (2^n) :=
    {code
      k ← sample uniform i_key ;;
      ret k
    }.

  Definition dec (c : Words) (k : Key) :
    code
      ([fmap key_location; table_location])
      [interface]
      ('fin (2^n) × 'fin (2^n)) :=
    enc k c.

  Definition EVAL_location_tt := [fmap key_location].
  Definition EVAL_location_ff := [fmap table_location].

  Definition EVAL_pkg_tt :
    package [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package EVAL_location_tt ;
      #def #[i0] (r : 'word) : 'key
      {
        k_init ← get key_location ;;
        match k_init with
        | None =>
            k ← sample uniform i_key ;;
            #put key_location := Some k ;;
            ret (PRF r k)
        | Some k_val =>
            ret (PRF r k_val)
        end
      }
    ].

  Definition EVAL_pkg_ff :
    package [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package EVAL_location_ff ;
      #def #[i0] (r : 'word) : 'key
      {
        T ← get table_location ;;
        match getm T r with
        | None =>
            T_key ← sample uniform i_key ;;
            #put table_location := (setm T r T_key) ;;
            ret T_key
        | Some T_key => ret T_key
        end
      }
    ].

  Definition EVAL b : game [interface #val #[i0] : 'word → 'key ] :=
    if b then EVAL_pkg_tt else EVAL_pkg_ff.

  Definition MOD_CPA_tt_pkg :
    package [interface #val #[i0] : 'word → 'key ]
      [interface #val #[i1] : 'word → 'word × 'word ] :=
    [package emptym ;
      #def #[i1] (m : 'word) : 'word × 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform i_words ;;
        pad ← eval r ;;
        let c := m ⊕ pad in
        ret (r, c)
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package [interface #val #[i0] : 'word → 'key]
      [interface #val #[i1] : 'word → 'word × 'word ]:=
    [package emptym ;
      #def #[i1] (m : 'word) : 'word × 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform i_words ;;
        m' ← sample uniform i_words ;;
        pad ← eval r ;;
        let c := (m' ⊕ pad) in
        ret (r, c)
      }
    ].

  Definition IND_CPA_location : Locations := [fmap key_location].

  Definition IND_CPA_pkg_tt :
    package
      [interface]
      [interface #val #[i1] : 'word → 'word × 'word ] :=
    [package IND_CPA_location ;
      #def #[i1] (m : 'word) : 'word × 'word
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val ← sample uniform i_key ;;
          #put key_location := Some k_val ;;
          enc m k_val
        | Some k_val =>
          enc m k_val
        end
      }
   ].

  Definition IND_CPA_pkg_ff :
    package
      [interface]
      [interface #val #[i1] : 'word → 'word × 'word ] :=
    [package IND_CPA_location ;
      #def #[i1] (m : 'word) : 'word × 'word
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val ← sample uniform i_key ;;
          #put key_location := Some k_val ;;
          m' ← sample uniform i_words ;;
          enc m' k_val
        | Some k_val =>
          m' ← sample uniform i_words ;;
          enc m' k_val
        end
      }
    ].

  Definition IND_CPA b : game [interface #val #[i1] : 'word → 'word × 'word ] :=
    if b then IND_CPA_pkg_tt else IND_CPA_pkg_ff.

  Local Open Scope ring_scope.

  Definition prf_epsilon A := Advantage EVAL A.

  Definition statistical_gap :=
    AdvantageE (MOD_CPA_ff_pkg ∘ EVAL false) (MOD_CPA_tt_pkg ∘ EVAL false).

  Lemma IND_CPA_equiv_false :
    IND_CPA false ≈₀ MOD_CPA_ff_pkg ∘ (EVAL true).
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq. cbn. intros [k|].
    - cbn. ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn.
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  Lemma IND_CPA_equiv_true :
    MOD_CPA_tt_pkg ∘ (EVAL true) ≈₀ IND_CPA true.
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq. cbn. intros [k|].
    - cbn. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  (** Security of PRF

    The bound is given by using the triangle inequality several times,
    using the following chain:
    IND_CPA false ≈ MOD_CPA_ff_pkg ∘ EVAL true
                  ≈ MOD_CPA_ff_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL true
                  ≈ IND_CPA true

  *)
  Theorem security_based_on_prf :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word × 'word ] A_export A →
      fseparate LA (IND_CPA false).(locs) →
      fseparate LA (IND_CPA true).(locs) →
      Advantage IND_CPA A <=
      prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
      statistical_gap A +
      prf_epsilon (A ∘ MOD_CPA_tt_pkg).
  Proof.
    intros LA A vA hd₀ hd₁. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    ssprove triangle (IND_CPA false) [::
      MOD_CPA_ff_pkg ∘ EVAL true ;
      MOD_CPA_ff_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL true
    ] (IND_CPA true) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    erewrite IND_CPA_equiv_false by ssprove_valid.
    erewrite IND_CPA_equiv_true by ssprove_valid.
    rewrite GRing.add0r GRing.addr0.
    rewrite !Advantage_link Advantage_sym //.
  Qed.

End PRF_example.
