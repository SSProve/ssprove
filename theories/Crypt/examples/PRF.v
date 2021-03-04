(** PRF Example

  Inspired by "State Separation for Code-Based Game-Playing Proofs"
  by Brzuska et al.

  Appendix A.

  "Given a pseudorandom function (PRF) we construct a symmetric encryption
  scheme that is indistinguishable under chosen plaintext attacks (IND-CPA)."

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb StdDistr
  pkg_core_definition pkg_chUniverse pkg_composition pkg_rhl  Package Prelude
  pkg_notation.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Module Type SymmetricSchemeParam.

  Parameter Words_N Key_N : nat.
  Parameter Words_N_pos : Positive Words_N.
  Parameter Key_N_pos : Positive Key_N.
  Existing Instance Words_N_pos.
  Existing Instance Key_N_pos.

  Definition Words := chFin (mkpos Words_N).
  Definition Key := chFin (mkpos Key_N).

  Parameter plus : Words → Key → Words.

  Notation "m ⊕ k" := (plus m k) (at level 70).

  Parameter plus_involutive : ∀ m k, (m ⊕ k) ⊕ k = m.

End SymmetricSchemeParam.

(* Symmetric Schemes *)
Module Type SymmetricSchemeRules (π : SymmetricSchemeParam).

  Import π.

  Inductive probEmpty : Type → Type :=.

  Module genparam <: RulesParam.

    Definition probE : Type → Type := probEmpty.
    Definition rel_choiceTypes : Type := void.

    Definition chEmb : rel_choiceTypes → choiceType.
    Proof.
      intro v. inversion v.
    Defined.

    Definition prob_handler :
      ∀ (T : choiceType),
        probE T → SDistr T.
    Proof.
      intros T v. inversion v.
    Defined.

    Definition Hch :
      ∀ (r : rel_choiceTypes), chEmb r.
    Proof.
      intro v. inversion v.
    Defined.

  End genparam.

  Module MyRules := DerivedRulesUniform genparam.

End SymmetricSchemeRules.

Module PRF_example.

  Parameter n : nat.

  Module π <: SymmetricSchemeParam.

    Definition Words_N : nat := 2^n.
    Definition Words_N_pos : Positive Words_N := _.
    Definition Words : chUniverse := chFin (mkpos Words_N).
    Definition Key_N : nat := 2^n.
    Definition Key_N_pos : Positive Key_N := _.
    Definition Key : chUniverse := chFin (mkpos Key_N).

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

  End π.

  Local Open Scope package_scope.

  Import π.
  Include (SymmetricSchemeRules π).

  Module MyPackage := Package_Make (MyRules.myparamU).
  Import MyPackage.
  Import PackageNotation.

  Definition key_location : Location := ('option Key ; 0).
  Definition plain_location : Location := (Words ; 1).
  Definition cipher_location : Location := (Words ; 2).
  Definition i0 : nat := 3.
  Definition i1 : nat := 4.
  Definition i2 : nat := 5.
  Definition salt_location : Location := ('nat ; 6).
  Definition table_location : Location :=
    (chMap 'nat ('fin (2^n)%N) ; 7).

  Definition rel_loc : {fset Location} :=
    fset [:: key_location ; table_location ].

  Parameter PRF : Words → Key → Key.

  Definition U (i : nat) `{Positive i} :
    { rchT : MyRules.myparamU.rel_choiceTypes &
      MyRules.myparamU.probE (MyRules.myparamU.chEmb rchT) } :=
    existT (λ rchT : MyRules.myparamU.rel_choiceTypes, MyRules.myparamU.probE (MyRules.myparamU.chEmb rchT))
            ('fin i) (inl (MyRules.Unif_Fin (mkpos i))).

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_key : nat := 2^n.
  Definition i_words : nat := 2^n.

  Definition enc {L : { fset Location }} (m : Words) (k : Key) :
    program L [interface] ('fin (2^n) × 'fin (2^n)) :=
      {program
        r ← sample U i_words ;;
        let pad := PRF r k in
        let c := m ⊕ pad in
        ret (r, c)
      }.

  Definition kgen : program fset0 [interface] 'fin (2^n) :=
    {program
      k ← sample U i_key ;;
      ret k
    }.

  Definition dec (c : Words) (k : Key) :
    program
      (fset [:: key_location; table_location])
      [interface]
      ('fin (2^n) × 'fin (2^n)) :=
    enc k c.

  Definition EVAL_location_tt := (fset [:: key_location]).
  Definition EVAL_location_ff := (fset [:: table_location]).

  Definition EVAL_pkg_tt :
    package EVAL_location_tt [interface]
      [interface val #[i0] : chWords → chKey ] :=
    [package
      def #[i0] (r : chWords) : chKey
      {
        k_init ← get key_location ;;
        match k_init with
        | None =>
            k ← sample U i_key ;;
            put key_location := Some k ;;
            ret (PRF r k)
        | Some k_val =>
            ret (PRF r k_val)
        end
      }
    ].

  Definition EVAL_pkg_ff :
    package EVAL_location_ff [interface]
      [interface val #[i0] : chWords → chKey ] :=
    [package
      def #[i0] (r : chWords) : chKey
      {
        T ← get table_location ;;
        match getm T r with
        | None =>
            T_key ← sample U i_key ;;
            put table_location := (setm T r T_key) ;;
            ret T_key
        | Some T_key => ret T_key
        end
      }
    ].

  (* TODO Not the most satisfying, it would be nice to think of something else
    This might come with more automation to deal with the GamePair type.
  *)
  Definition EVAL : loc_GamePair [interface val #[i0] : chWords → chKey ] :=
    λ b, if b then {locpackage EVAL_pkg_tt } else {locpackage EVAL_pkg_ff }.

  Definition MOD_CPA_location : {fset Location} := fset0.

  Definition MOD_CPA_tt_pkg :
    package MOD_CPA_location [interface val #[i0] : chWords → chKey ]
      [interface val #[i1] : chWords → chWords × chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        #import {sig #[i0] : chWords → chKey } as eval ;;
        r ← sample U i_words ;;
        pad ← eval r ;;
        let c := m ⊕ pad in
        ret (r, c)
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package MOD_CPA_location [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords × chWords ]:=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        #import {sig #[i0] : chWords → chKey } as eval ;;
        r ← sample U i_words ;;
        m' ← sample U i_words ;;
        pad ← eval r ;;
        let c := (m' ⊕ pad) in
        ret (r, c)
      }
    ].

  Definition IND_CPA_location : {fset Location} := fset [:: key_location].

  Definition IND_CPA_pkg_tt :
    package IND_CPA_location
      [interface]
      [interface val #[i1] : chWords → chWords × chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val ← sample U i_key ;;
          put key_location := Some k_val ;;
          enc m k_val
        | Some k_val =>
          enc m k_val
        end
      }
   ].

  Definition IND_CPA_pkg_ff :
    package IND_CPA_location
      [interface]
      [interface val #[i1] : chWords → chWords × chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val ← sample U i_key ;;
          put key_location := Some k_val ;;
          m' ← sample U i_words ;;
          enc m' k_val
        | Some k_val =>
          m' ← sample U i_words ;;
          enc m' k_val
        end
      }
    ].

  Definition IND_CPA :
    loc_GamePair [interface val #[i1] : chWords → chWords × chWords ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_tt } else {locpackage IND_CPA_pkg_ff }.

  Local Open Scope ring_scope.

  Definition prf_epsilon A := Advantage EVAL A.

  Definition statistical_gap :=
    AdvantageE (MOD_CPA_ff_pkg ∘ EVAL false) (MOD_CPA_tt_pkg ∘ EVAL false).

  Lemma IND_CPA_equiv_false :
    IND_CPA false ≈₀ MOD_CPA_ff_pkg ∘ (EVAL true).
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁). 2: reflexivity.
    1:{
      simpl. intros s₀ s₁. split.
      - intro e. rewrite e. auto.
      - intro e. rewrite e. auto.
    }
    (* We now conduct the proof in relational logic. *)
    intros id S T m hin.
    invert_interface_in hin.
    rewrite get_op_default_link.
    (* First we need to squeeze the programs out of the packages *)
    (* Hopefully I will find a way to automate it. *)
    unfold get_op_default.
    destruct lookup_op as [f|] eqn:e.
    2:{
      exfalso.
      simpl in e.
      destruct chUniverse_eqP. 2: eauto.
      destruct chUniverse_eqP. 2: eauto.
      discriminate.
    }
    eapply lookup_op_spec in e. simpl in e.
    rewrite setmE in e. rewrite eq_refl in e.
    noconf e.
    (* Now to the RHS *)
    destruct lookup_op as [f|] eqn:e.
    2:{
      exfalso.
      simpl in e.
      destruct chUniverse_eqP. 2: eauto.
      destruct chUniverse_eqP. 2: eauto.
      discriminate.
    }
    eapply lookup_op_spec in e. simpl in e.
    rewrite setmE in e. rewrite eq_refl in e.
    noconf e.
    (* Now the linking *)
    cbn.
    destruct chUniverse_eqP as [e|]. 2: contradiction.
    rewrite cast_fun_K. clear e.
    cbn.
    (* We are now in the realm of program logic *)
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_same_head_r. cbn. intros [k|].
    - cbn. ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn.
      (* Swapping:

        k_val/put/m'/r vs a₁/a₁0/a/put
        where k_val = a, r = a₁, m' = a₁0

        Meaning k_val/put/m'/r vs r/m'/k_val/put
        Starting from the right,
        r/m'/k_val/put
        m'/r/k_val/put
        m'/k_val/r/put
        k_val/m'/r/put
        k_val/m'/put/r
        k_val/put/m'/r
      *)
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
    eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁). 2: reflexivity.
    1:{
      simpl. intros s₀ s₁. split.
      - intro e. rewrite e. auto.
      - intro e. rewrite e. auto.
    }
    (* We now conduct the proof in relational logic. *)
    intros id S T m hin.
    invert_interface_in hin.
    rewrite get_op_default_link.
    (* First we need to squeeze the programs out of the packages *)
    (* Hopefully I will find a way to automate it. *)
    unfold get_op_default.
    destruct lookup_op as [f|] eqn:e.
    2:{
      exfalso.
      simpl in e.
      destruct chUniverse_eqP. 2: eauto.
      destruct chUniverse_eqP. 2: eauto.
      discriminate.
    }
    eapply lookup_op_spec in e. simpl in e.
    rewrite setmE in e. rewrite eq_refl in e.
    noconf e.
    (* Now to the RHS *)
    destruct lookup_op as [f|] eqn:e.
    2:{
      exfalso.
      simpl in e.
      destruct chUniverse_eqP. 2: eauto.
      destruct chUniverse_eqP. 2: eauto.
      discriminate.
    }
    eapply lookup_op_spec in e. simpl in e.
    rewrite setmE in e. rewrite eq_refl in e.
    noconf e.
    (* Now the linking *)
    cbn.
    destruct chUniverse_eqP as [e|]. 2: contradiction.
    rewrite cast_fun_K. clear e.
    cbn.
    (* We are now in the realm of program logic *)
    ssprove_swap_lhs 0%N.
    ssprove_same_head_r. cbn. intros [k|].
    - cbn. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn.
      (* Swapping:

        a₁/a/put vs k_val/put/r
        where k_val = a, r = a₁

        Meaning r/k_val/put vs k_val/put/r
        Starting from the right,
        k_val/put/r
        k_val/r/put
        r/k_val/put
      *)
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
        [interface val #[i1] : chWords → chWords × chWords ] A_export A →
      fdisjoint LA (IND_CPA false).(locs) →
      fdisjoint LA (IND_CPA true).(locs) →
      Advantage IND_CPA A <=
      prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
      statistical_gap A +
      prf_epsilon (A ∘ MOD_CPA_tt_pkg).
  Proof.
    intros LA A vA hd₀ hd₁. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    pose proof (
      Advantage_triangle_chain (IND_CPA false) [::
        MOD_CPA_ff_pkg ∘ EVAL true ;
        MOD_CPA_ff_pkg ∘ EVAL false ;
        MOD_CPA_tt_pkg ∘ EVAL false ;
        MOD_CPA_tt_pkg ∘ EVAL true
      ] (IND_CPA true) A
    ) as ineq.
    advantage_sum simpl in ineq.
    rewrite !GRing.addrA in ineq.
    eapply ler_trans. 1: exact ineq.
    clear ineq.
    erewrite IND_CPA_equiv_false. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    erewrite IND_CPA_equiv_true. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    rewrite GRing.add0r GRing.addr0.
    rewrite !Advantage_link. rewrite Advantage_sym. auto.
  Qed.

End PRF_example.
