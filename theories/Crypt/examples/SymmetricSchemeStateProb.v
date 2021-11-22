(*
   Inspired to "State Separation for Code-Based Game-Playing Proofs" - Brzuska et al.

   Appendix A.

   "Given a pseudorandom function (PRF) we construct a symmetric encryption scheme
    that is indistinguishable under chosen plaintext attacks (IND-CPA). "

*)

(* Rem.: TODO In the SSEP paper packages return (r,c) we only return c *)

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
     StdDistr.
From Crypt Require Import
     pkg_core_definition
     chUniverse
     pkg_composition
     pkg_rhl
     Package
     Prelude
     pkg_notation.

From Crypt Require Import pkg_notation.

From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
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

(* Local Open Scope ring_scope. *)

Module Type SymmetricSchemeParam.

  Parameter Words_N Key_N : nat.
  Parameter Words_N_pos : Positive Words_N.
  Parameter Key_N_pos : Positive Key_N.
  Existing Instance Words_N_pos.
  Existing Instance Key_N_pos.
  Definition Words := (chFin (mkpos Words_N)).
  Definition Key := chFin (mkpos Key_N).
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
    Definition chUniverse : Type := void.
    Definition chElement : chUniverse -> choiceType.
    Proof. move => v. inversion v. Defined.
    Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
    Proof. move => T v. inversion v. Defined.
    Definition Hch : forall r : chUniverse, chElement r.
    Proof. move => v. inversion v. Defined.

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
      unfold Words_N, Key_N in *.
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
        apply Hk.
      }
      move: (BinNat.N.max_lub_lt _ _ _ H1 H2) => Hm.
      destruct ((BinNat.N.lxor (BinNat.N.of_nat w) (BinNat.N.of_nat k)) == BinNat.N0) eqn:H0.
      1: { simpl. move: H0. move /eqP => H0. rewrite H0. simpl.
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
  End π.

  Local Open Scope package_scope.

  Import π.
  Include (SymmetricSchemeRules π).

  Module MyPackage := Package_Make (MyRules.myparamU).
  Import MyPackage.
  Import PackageNotation.

  Definition key_location : Location := ('option Key; 0).
  Definition plain_location : Location := (Words; 1).
  Definition cipher_location : Location := (Words; 2).
  Definition i0 : nat := 3.
  Definition i1 : nat := 4.
  Definition i2 : nat := 5.
  Definition salt_location : Location := ('nat; 6).
  Definition table_location : Location :=
    (chMap 'nat ('fin (2^n)%N) ; 7).

  Definition rel_loc : {fset Location} :=
    fset [:: key_location ; cipher_location ; table_location ].
  (* Rem.: i0;  i1; i2 ; -> only memory locations should belong here, not program entries/package oracles *)


  (* Parameter PRF : forall (r: Words) (k : Key), raw_code Key. *)
  (* Parameter PRF_valid : forall r k, ValidCode rel_loc fset0 (PRF r k). *)
  Parameter PRF : Words -> Key -> Key.
  Parameter prf_epsilon : R.

  Definition U (i : positive) : {rchT : MyRules.myparamU.chUniverse & MyRules.myparamU.probE (MyRules.myparamU.chElement rchT)} :=
    (existT (λ rchT : MyRules.myparamU.chUniverse, MyRules.myparamU.probE (MyRules.myparamU.chElement rchT))
            (chFin i) (inl (MyRules.Unif_Fin i))).
  Obligation Tactic := package_obtac.

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_key : nat := 2^n.
  Definition i_words : nat := 2^n.

  Definition EVAL_location := (fset [:: key_location ; table_location]).

  #[program] Definition EVAL_opkg_tt :
    opackage EVAL_location [interface]
      [interface val #[i0] : chWords → chKey ] :=
  [package
    def #[i0] ( r : chWords) : chKey
    {
      k_init ← get key_location ;;
      match k_init with
      | None =>
           k <$ (U (mkpos i_key)) ;;
           let pad := PRF r k in
           put key_location := Some pad ;;
           ret pad
      | Some k_val =>
           let pad := PRF r k_val in
           put key_location := Some pad ;;
           ret pad
      end
    }
  ].

  Definition EVAL_pkg_tt :
    package [interface] [interface val #[i0] : chWords → chKey].
  Proof.
    exists EVAL_location. exact: EVAL_opkg_tt.
  Defined.

  #[program] Definition EVAL_opkg_ff :
    opackage EVAL_location [interface]
      [interface val #[i0] : chWords → chKey] :=
    [package
      def #[i0] (r : chWords) : chKey
      {
        T ← get table_location ;;
        match getm T r with
        | None =>
            T_key <$ (U (mkpos i_key)) ;;
            put table_location := (setm T r T_key) ;;
            ret T_key
        | Some T_key => ret T_key
        end
      }
    ].

  Definition EVAL_pkg_ff :
    package [interface] [interface val #[i0] : chWords → chKey].
  Proof.
    exists EVAL_location. exact: EVAL_opkg_ff.
  Defined.

  Definition EVAL : GamePair  [interface val #[i0] : chWords → chKey] :=
    λ (b : bool),
      if b then EVAL_pkg_tt else EVAL_pkg_ff.

  (*Rem.: Notice that we put also table_location here!
        Because we want IND_CPA ∘ ENC  and MOD_CPA ∘ EVAL to have the same locations.
  *)
  Definition ENC_location := fset [:: key_location ; cipher_location ; table_location ].

  #[program] Definition ENC_opkg :
    opackage ENC_location [interface]
      [interface val #[i2] : chWords × chKey → chWords] :=
    [package
      def #[i2] (mk : chWords × chKey) : chWords
      {
        r <$ U (mkpos i_words) ;;
        let pad := PRF r (snd mk) in
        put key_location := Some pad ;;
        put cipher_location := (fst mk) ⊕ pad ;;
        c ← get cipher_location ;;
        ret (c)
      }
    ].

  Definition ENC_pkg :
    package [interface] [interface val #[i2] :  chWords × chKey → chWords].
  Proof.
    exists ENC_location. exact ENC_opkg.
  Defined.

  Definition MOD_CPA_location := [fset cipher_location].

  #[program] Definition MOD_CPA_tt :
    opackage MOD_CPA_location [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords
      {
        r <$ (U (mkpos i_words)) ;;
        pad ← op [ #[i0] : chWords → chKey ] r ;;
        put cipher_location := (m ⊕ pad) ;;
        c ← get cipher_location ;;
        ret (c)
      }
    ].


  Definition MOD_CPA_tt_pkg :
    package [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords ].
  Proof.
    exists MOD_CPA_location. exact:MOD_CPA_tt.
  Defined.

  #[program] Definition MOD_CPA_ff :
    opackage MOD_CPA_location [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords ]:=
    [package
      def #[i1] (m : chWords) : chWords
      {
        r  <$ (U (mkpos i_words)) ;;
        m' <$ (U (mkpos i_words)) ;;
        pad ← op [ #[i0] : chWords → chKey ] r ;;
        put cipher_location := (m' ⊕ pad) ;;
        c ← get cipher_location ;;
        ret c
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords ].
  Proof.
    exists MOD_CPA_location. exact:MOD_CPA_ff.
  Defined.

  Definition IND_CPA_location : {fset Location} := fset [:: key_location].

  #[program] Definition IND_CPA_opkg_tt :
    opackage IND_CPA_location
      [interface val #[i2] : chWords × chKey → chWords]
      [interface val #[i1] : chWords → chWords ] :=
   [package
      def #[i1] (m : chWords) : chWords
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val <$ (U (mkpos i_key)) ;;
          c_val ← op [ #[i2] : chWords × chKey → chWords ] (m, k_val) ;;
          ret c_val
        | Some k_val =>
          c_val ← op [ #[i2] : chWords × chKey → chWords ] (m, k_val) ;;
          ret c_val
        end
      }
    ].

  Definition IND_CPA_pkg_tt :
    package
      [interface val #[i2] : chWords × chKey → chWords]
      [interface val #[i1] : chWords → chWords ].
  Proof.
    exists IND_CPA_location. exact: IND_CPA_opkg_tt.
  Defined.

  #[program] Definition IND_CPA_opkg_ff :
    opackage IND_CPA_location
      [interface val #[i2] : chWords × chKey → chWords]
      [interface val #[i1] : chWords → chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords
      {
        k ← get key_location ;;
        match k with
        | None =>
          k_val <$ (U (mkpos i_key)) ;;
          m' <$ (U (mkpos i_words)) ;;
          c_val ← op [ #[i2] : chWords × chKey → chWords ]
                  (m', k_val) ;;
          ret c_val
        | Some k_val =>
          m' <$ (U (mkpos i_words)) ;;
          c_val ← op [ #[i2] : chWords × chKey → chWords ]
                  (m', k_val) ;;
          ret c_val
        end
      }
    ].

  Definition IND_CPA_pkg_ff :
    package
      [interface val #[i2] : chWords × chKey → chWords]
      [interface val #[i1] : chWords → chWords ].
  Proof.
    exists IND_CPA_location.
    exact: IND_CPA_opkg_ff.
  Defined.

  Definition IND_CPA : GamePair [interface val #[i1] : chWords → chWords ] :=
    λ (b : bool),
      if b then (link IND_CPA_pkg_tt ENC_pkg)
      else (link IND_CPA_pkg_ff  ENC_pkg).

  Local Open Scope ring_scope.

  Definition PRF_security :=
    ∀ A H1 H2, (@Advantage _ EVAL A H1 H2) <= prf_epsilon.

  Definition statistical_gap { A } : R :=
    `|Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true|.

  Ltac fold_repr :=
    change (repr' ?p ?h) with (repr (exist _ p h)).

  Lemma key_location_in_rel_loc : key_location \in rel_loc.
  Proof.
    package_obtac.
  Qed.

  Lemma cipher_location_in_rel_loc : cipher_location \in rel_loc.
  Proof.
    package_obtac.
  Qed.

  Definition LHS0 (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
      move => /= m_val'. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
        { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ ((PRF r_val k_val)))).  apply: ret Datatypes.tt. }
        move => tt'. apply: bind.
        { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
        move => c.
        exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k.
      apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
      move => /= m_val'. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
        { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ ((PRF r_val k)))).  apply: ret Datatypes.tt. }
        move => tt'. apply: bind.
        { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
        move => c.
        exact: ret c.
  Defined.

  Definition RHS0 (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k. apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  Definition RHS0_swap (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. destruct option_k as [k_val |].
    - apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  Definition RHS0_swap_swap  (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. destruct option_k as [k_val |].
    - apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m_val' ⊕ (PRF r_val k))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  (* Note duplicate in ElGamalStateProb *)
  (* TODO MOVE But where? *)
  Lemma eq_prog_semj_impl :
    ∀ L L' R R' A
      (p : code L _ A) (q : code R _ _)
      (p' : code L' _ A) (q' : code R' _ _),
      L = L' →
      R = R' →
      p ∙1 = p' ∙1 →
      q ∙1 = q' ∙1 →
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


Lemma subset_key_rel : fsubset (fset [:: key_location ]) (fset [:: key_location ; cipher_location ; table_location ]).
Proof.
  apply /eqP. apply eq_fset => x.
  rewrite in_fsetU !in_fset. rewrite !in_cons.
  rewrite in_fset0. rewrite -orbA Bool.orb_false_r Bool.orb_false_l.
  by rewrite !orbA Bool.orb_diag.
Qed.

  Lemma IND_CPA_location_rel_loc :
    rel_loc = IND_CPA_location :|: ENC_location.
  Proof.
    rewrite /IND_CPA_location /ENC_location /rel_loc.
    move/fsetUidPr : subset_key_rel => H. by subst.
  Qed.


  Lemma MOD_CPA_location_rel_loc :
    rel_loc = MOD_CPA_location :|: EVAL_location.
  Proof.
    rewrite /rel_loc /MOD_CPA_location /EVAL_location.
    apply eq_fset => x.
    rewrite in_fset. rewrite in_cons. rewrite in_cons. rewrite mem_seq1.
    rewrite !in_fsetU. rewrite !in_fset1.
    rewrite in_fset. rewrite in_cons. rewrite mem_seq1.
    rewrite in_fset0.
    rewrite orbF.
    rewrite orbCA. reflexivity.
  Qed.

  Lemma perfect_equivalence0 :
    ∀ (A : Adversary4Game [interface val #[i1] : chWords → chWords ])
      (Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                              A.π1 (IND_CPA_location :|: ENC_location))
      (Hdisjoint2 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                              A.π1 (MOD_CPA_location :|: EVAL_location)) ,
      (Pr (A ∘ IND_CPA false) true) =
      (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ (EVAL true)) true).
  Proof.
    intros A Hdisjoint1 Hdisjoint2.
    rewrite /IND_CPA.
    rewrite -link_assoc.
    apply: GRing.subr0_eq. apply: normr0_eq0.
    fold (@AdvantageE [interface val #[i1] : chWords → chWords]
                      (IND_CPA_pkg_ff ∘ ENC_pkg) (MOD_CPA_ff_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
    (* rewrite /IND_CPA_pkg_ff /IND_CPA_opkg_ff /MOD_CPA_ff_pkg /MOD_CPA_ff_pkg /MOD_CPA_ff. *)
    rewrite (eq_upto_inv_perf_ind' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2. (* rewrite /eq_up_to_inv_alt2. *)
    unfold IND_CPA_pkg_ff. unfold MOD_CPA_ff_pkg.
    unfold IND_CPA_opkg_ff. unfold MOD_CPA_ff.
    package_link_simplify.
    intros id h m.
    invert_interface_in h.
    repeat opackage_transport_simplify.
    package_pdef_simpl.
    match type of m with
    | context [ opackage_transport _ ?e _ ] =>
      rewrite (uip e erefl) in m ;
      change (opackage_transport erefl erefl ?z) with z in m
    end.
    unfold pdefS in m. simpl in m.
    change (Choice.sort (chElement ('fin (2^n)%N))) in m.
    suffices: ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ repr (LHS0 m) ≈ repr (RHS0 m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - exact: IND_CPA_location_rel_loc.
      - exact: MOD_CPA_location_rel_loc.
      - simpl. f_equal. extensionality v.
        destruct v.
        + cbn - [lookup_op]. f_equal. extensionality a.
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
          cbn. reflexivity.
        + cbn - [lookup_op]. f_equal. extensionality a.
          f_equal. extensionality b.
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
          cbn. reflexivity.
      - cbn - [lookup_op]. f_equal. extensionality a.
        f_equal. extensionality b.
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn. f_equal. extensionality c.
        destruct c.
        + cbn. reflexivity.
        + cbn. reflexivity.
    }
    rewrite /LHS0 /RHS0.
    unshelve apply: rrewrite_eqDistrR.
    { exact: RHS0_swap. }
    2:{ move => s. unshelve eapply rcoupling_eq with (ψ := fun '(s1, s2) => s1 = s2).
        - apply: rsame_head => r.
          unshelve eapply rswap_ruleR.
          { move => bs1 bs2 H. assumption. }
          { move => k m'. destruct k as [k_val |].
            + apply: rsym_pre. { move => s1 s2 H. symmetry. assumption. }
              by apply: rreflexivity_rule.
            + apply: rsym_pre. { move => s1 s2 H. symmetry. assumption. }
              by apply: rreflexivity_rule.
          }
    apply: (rsamplerC (U (mkpos i_words)) (option_k ← get key_location ;; ret option_k)).
    - reflexivity. }
    unshelve eapply rrewrite_eqDistrR.
    { exact: RHS0_swap_swap m. }
    2:{ move => s.  unshelve eapply rcoupling_eq with (ψ := fun '(s1, s2) => s1 = s2).
        - unshelve eapply rswap_ruleR.
          { move => bs1 bs2 H. assumption. }
          { move => k m'. destruct k as [k_val |].
            + apply: rsym_pre. { move => s1 s2 H. symmetry. assumption. }
              by apply: rreflexivity_rule.
            + apply: rsym_pre. { move => s1 s2 H. symmetry. assumption. }
              by apply: rreflexivity_rule.
          }
    apply: rsamplerC (U (mkpos i_words)) (option_k ← get key_location ;; ret option_k).
        - reflexivity. }
    rewrite /RHS0_swap_swap.
    apply: rsame_head => option_k.
    destruct option_k as [k_val | ].
    + unshelve eapply rswap_ruleR.
      { by intuition. }
      ++ move => r m'.
        apply: rsym_pre. { move => s1 s2 H. symmetry. assumption. }
          by apply: rreflexivity_rule.
      ++ apply: rsamplerC (U (mkpos i_words)) (m_val' ← sample U (mkpos i_words) ;; ret m_val').
    + apply: rrewrite_eqDistrL.
      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => a1 a2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
          by apply: rreflexivity_rule.
        ++ apply: rsamplerC (U (mkpos i_words)) (r_val ← sample U (mkpos i_words) ;; ret r_val). }
      move => s. apply rcoupling_eq with (ψ := fun '(h1, h2) => h1 = h2). 2: by reflexivity.
      apply: rrewrite_eqDistrL.
      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => a1 a2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
            by apply: rreflexivity_rule.
        ++ apply: rsamplerC' (U (mkpos i_words)) (k_val ← sample U (mkpos i_key) ;; ret k_val). }
      move => s'. apply rcoupling_eq with (ψ := fun '(h1, h2) => h1 = h2). 2: by reflexivity.
      apply: rsame_head => m'.
      apply: rswap_ruleR. { move => bs bs' H. assumption. }
      ++ move => k r. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
          by apply: rreflexivity_rule.
      ++ apply: rsamplerC (U (mkpos i_words))  (k_val ← sample U (mkpos i_key) ;; ret k_val).
Qed.

  Definition LHS1 (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ ((PRF r_val k_val)))).
        apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k.
      apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
       move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ ((PRF r_val k)))).
        apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  Definition RHS1 (m : ('fin (2^n)%N)) :
    code rel_loc fset0  ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => option_k. destruct option_k as [k_val |].
    - apply: bind.
      { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
       move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ (PRF r_val k))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  Definition RHS1_swap (m : ('fin (2^n)%N)) :
    code rel_loc fset0 ('fin (2^n)%N).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_rel_loc) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. destruct option_k as [k_val |].
    - apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k_val))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ (PRF r_val k_val))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k. apply: bind.
       { apply: (putr _ key_location_in_rel_loc (Some (PRF r_val k))). apply: ret Datatypes.tt. }
        move => tt. apply: bind.
      { apply: (putr _ cipher_location_in_rel_loc (m ⊕ (PRF r_val k))). apply: ret Datatypes.tt. }
      move => tt'. apply: bind.
      { apply: (getr _ cipher_location_in_rel_loc) => /= c_val. apply: ret c_val. }
      move => c.
      exact: ret c.
  Defined.

  Lemma perfect_equivalence1 (A : Adversary4Game [interface val #[i1] : chWords → chWords ])
      { Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                               A.π1 (IND_CPA_location :|: ENC_location) }
      { Hdisjoint2 : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                               A.π1 (MOD_CPA_location :|: EVAL_location) } :
  (Pr (A ∘ IND_CPA true) true) = (Pr ((A ∘ MOD_CPA_tt_pkg) ∘ (EVAL true)) true).
  Proof.
    rewrite -link_assoc.
    apply: GRing.subr0_eq. apply: normr0_eq0.
    rewrite /IND_CPA.
    fold (@AdvantageE [interface val #[i1] : chWords → chWords] (IND_CPA_pkg_tt ∘ ENC_pkg) (MOD_CPA_tt_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
    rewrite (eq_upto_inv_perf_ind' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold IND_CPA_pkg_tt. unfold MOD_CPA_tt_pkg.
    unfold IND_CPA_opkg_tt. unfold MOD_CPA_tt.
    package_link_simplify.
    intros id h m.
    invert_interface_in h.
    repeat opackage_transport_simplify.
    package_pdef_simpl.
    match type of m with
    | context [ opackage_transport _ ?e _ ] =>
      (* rewrite (uip e erefl) in m ; *)
      change (opackage_transport erefl erefl ?z) with z in m
    end.
    unfold pdefS in m. simpl in m.
    change (Choice.sort (chElement ('fin (2^n)%N))) in m.
    suffices: ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ repr (LHS1 m) ≈ repr (RHS1 m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - exact: IND_CPA_location_rel_loc.
      - exact: MOD_CPA_location_rel_loc.
      - simpl.  f_equal. extensionality v.
        cbn - [lookup_op].
        destruct v eqn:Hv.
        + cbn - [lookup_op].
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
          cbn. reflexivity.
        + cbn - [lookup_op]. f_equal. extensionality a.
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
          cbn. reflexivity.
      - cbn - [lookup_op]. f_equal. extensionality a.
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn. f_equal. extensionality c.
        destruct c.
        + cbn. reflexivity.
        + cbn. reflexivity.
    }
    rewrite /LHS1 /RHS1.
    unshelve eapply rrewrite_eqDistrR.
    { exact: RHS1_swap. }
    - rewrite /RHS1_swap. apply: rsame_head => option_k.
      destruct option_k as [k_val | ].
      + apply: rreflexivity_rule.
      + apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => k r.
          apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
          apply: rreflexivity_rule.
        ++ apply: rsamplerC (U (mkpos i_words)) (k_val ← sample U (mkpos i_key) ;; ret k_val).
    - move => s.
      unshelve eapply rcoupling_eq. { exact : (fun '(h1, h2) => h1 = h2). } 2: by reflexivity.
      rewrite /RHS1_swap.
      apply: rswap_ruleR. { move => bs bs' H. assumption. }
      + move => r k.
        apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
        apply: rreflexivity_rule.
      + apply: rsamplerC (U (mkpos i_words)) (option_k ← get key_location ;; ret option_k).
Qed.


Lemma same_locations :
  IND_CPA_location :|: ENC_location = MOD_CPA_location :|: EVAL_location.
Proof.  by rewrite -IND_CPA_location_rel_loc -MOD_CPA_location_rel_loc. Qed.

Lemma ciper_key_table1 : fset [:: cipher_location] :&: fset [:: key_location; table_location] = fset0.
Proof.
  apply eq_fset => x.
  rewrite in_fsetI in_fset0.
  apply: negPf. apply /andP.  move => [H1 H2].
  rewrite in_fset mem_seq1 in H1. move/eqP: H1. move => H1. subst.
  rewrite in_fset mem_seq2 in H2. move /orP: H2. move => [K | K]; inversion K.
Qed.

 Lemma still_disjoint : forall X, ( X :&: ([fset cipher_location] :|: fset [:: key_location; table_location]) == fset0) ->

                             (X :|: [fset cipher_location]) :&: fset [:: key_location; table_location] == fset0.
 Proof.
   move => X Hdisjoint.
   rewrite fsetIUl. rewrite fsetIUr fsetU_eq0 in Hdisjoint.
   move/andP: Hdisjoint. move => [H1 H2]. move/eqP: H1. move/eqP: H2. move => H1 H2.
     by rewrite H1 fset0U ciper_key_table1.
 Qed.


  Theorem security_based_on_prf (Hprf : PRF_security) :
    ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords ],
    ∀ Hdisjoint1 Hdisjoint2,
      (@Advantage _ IND_CPA A Hdisjoint1 Hdisjoint2) <=
      prf_epsilon + (@statistical_gap A + prf_epsilon).
  Proof.
    rewrite /Advantage => A Hdisjoint1 Hdisjoint2.
    simpl (IND_CPA true).π1 in Hdisjoint2. simpl (IND_CPA false).π1 in Hdisjoint1.
    rewrite same_locations in Hdisjoint2.
    rewrite (@perfect_equivalence0 A Hdisjoint1 Hdisjoint2).
    rewrite (@perfect_equivalence1 A Hdisjoint1 Hdisjoint2).
    have sum_sub : `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true| =
                  `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL false) true +
                    Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL false) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true|
      by rewrite  GRing.subrK.
    rewrite sum_sub. clear sum_sub.
    apply: ler_trans. { rewrite -GRing.addrA. apply: ler_norm_add. }
    apply: ler_add.
    - rewrite distrC. rewrite same_locations in Hdisjoint1.
      apply: (Hprf (A ∘ MOD_CPA_ff_pkg)); rewrite /=;  unfold MOD_CPA_location, EVAL_location in *;
      by apply: still_disjoint.
      - have sum_sub : `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL_pkg_tt) true| =
                      `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_tt) true +
                        Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_tt) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL_pkg_tt) true|
          by rewrite GRing.subrK.
        rewrite sum_sub. clear sum_sub.
        apply: ler_trans. { rewrite -GRing.addrA. apply: ler_norm_add. }
        rewrite GRing.addrC.
        apply: ler_add.
        + rewrite /statistical_gap distrC /EVAL. exact: lerr.
        + apply: (Hprf (A ∘ MOD_CPA_ff_pkg)); rewrite /=; unfold fdisjoint, MOD_CPA_location, EVAL_location in *;
            by apply still_disjoint.
Qed.

End PRF_example.

