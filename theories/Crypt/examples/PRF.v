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

  Definition U (i : positive) :
    { rchT : MyRules.myparamU.rel_choiceTypes &
      MyRules.myparamU.probE (MyRules.myparamU.chEmb rchT) } :=
    existT (λ rchT : MyRules.myparamU.rel_choiceTypes, MyRules.myparamU.probE (MyRules.myparamU.chEmb rchT))
            (chFin i) (inl (MyRules.Unif_Fin i)).

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_key : nat := 2^n.
  Definition i_words : nat := 2^n.

  Definition enc {L : { fset Location }} (m : Words) (k : Key) :
    program L fset0  ('fin (2^n) × 'fin (2^n)) :=
      {program
        r ← sample U (mkpos i_words) ;;
        let pad := PRF r k in
        let c := m ⊕ pad in
        ret (r, c)
      }.

  Definition kgen : program fset0 fset0 'fin (2^n) :=
    {program
      k <$ U (mkpos i_key) ;;
      ret k
    }.

  Definition dec (c : Words) (k : Key) :
    program (fset [:: key_location; table_location])
            fset0
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
            k ← sample U (mkpos i_key) ;;
            put key_location := Some k ;;
            ret (PRF r k)
        | Some k_val =>
            ret (PRF r k_val)
        end
      }
    ].

  Definition EVAL_pkg_ff :
    package EVAL_location_ff [interface]
      [interface val #[i0] : chWords → chKey] :=
    [package
      def #[i0] (r : chWords) : chKey
      {
        T ← get table_location ;;
        match getm T r with
        | None =>
            T_key ← sample U (mkpos i_key) ;;
            put table_location := (setm T r T_key) ;;
            ret T_key
        | Some T_key => ret T_key
        end
      }
    ].

  Definition EVAL : GamePair  [interface val #[i0] : chWords → chKey] :=
    λ b, if b then {locpackage EVAL_pkg_tt } else {locpackage EVAL_pkg_ff }.

  Definition MOD_CPA_location : {fset Location} := fset0.

  Definition MOD_CPA_tt_pkg :
    package MOD_CPA_location [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords × chWords ] :=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        r ← sample U (mkpos i_words) ;;
        pad ← op [ #[i0] : chWords → chKey ] r ;;
        let c := (m ⊕ pad) in
        ret (r, c)
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package MOD_CPA_location [interface val #[i0] : chWords → chKey]
      [interface val #[i1] : chWords → chWords × chWords ]:=
    [package
      def #[i1] (m : chWords) : chWords × chWords
      {
        r ← sample U (mkpos i_words) ;;
        m' ← sample U (mkpos i_words) ;;
        pad ← op [ #[i0] : chWords → chKey ] r ;;
        let c := (m' ⊕ pad) in
        ret (r, c)
      }
    ].

  (* Rem.: I was forced to add also table_location, o.w.
    cannot apply eq_prog_semj_impl
  *)
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
          k_val ← sample U (mkpos i_key) ;;
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
          k_val ← sample U (mkpos i_key) ;;
          put key_location := Some k_val ;;
          m' ← sample U (mkpos i_words) ;;
          enc m' k_val
        | Some k_val =>
          m' ← sample U (mkpos i_words) ;;
          enc m' k_val
        end
      }
    ].

  Definition IND_CPA :
    GamePair [interface val #[i1] : chWords → chWords × chWords ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_tt } else {locpackage IND_CPA_pkg_ff }.

  Local Open Scope ring_scope.

  Definition prf_epsilon A := Advantage EVAL A.

  Definition statistical_gap :=
    AdvantageE
      {locpackage MOD_CPA_ff_pkg ∘ EVAL false }
      {locpackage MOD_CPA_tt_pkg ∘ EVAL false }.

  Ltac fold_repr :=
    change (repr' ?p ?h) with (repr (mkprog p h)).

  Lemma key_location_in_rel_loc : key_location \in rel_loc.
  Proof.
    auto_in_fset.
  Qed.

  Lemma key_location_in_INDCPA_location : key_location \in IND_CPA_location.
  Proof.
    auto_in_fset.
  Qed.

  (* TODO See if it is better to have packages or raw packages here
    and above.
  *)
  Lemma IND_CPA_equiv_false :
    (IND_CPA false) ≈[ λ A, 0 ] {locpackage MOD_CPA_ff_pkg ∘ (EVAL true) }.
  Proof.
    (* Here the proof should come down to using the syntactic rules. *)
  Admitted.

  Lemma IND_CPA_equiv_true :
  {locpackage MOD_CPA_tt_pkg ∘ (EVAL true) } ≈[ λ A, 0 ] (IND_CPA true).
  Proof.
  Admitted.

  (* TODO MOVE *)
  Lemma Advantage_E :
    ∀ I (G : GamePair I) A,
      Advantage G A = AdvantageE (G false) (G true) A.
  Proof.
    intros I G A.
    reflexivity.
  Qed.

  (* TODO MOVE *)
  (* Similar to reduction lemma *)
  Lemma Advantage_link :
    ∀ I E (G₀ G₁ : Game_Type I) (A : Adversary4Game _) (P : loc_package _ E),
      AdvantageE G₀ G₁ {locpackage A ∘ P} =
      AdvantageE {locpackage P ∘ G₀} {locpackage P ∘ G₁} A.
  Proof.
    intros I E G₀ G₁ A P.
    unfold AdvantageE. simpl.
    package_before_rewrite.
    rewrite !link_assoc.
    package_after_rewrite.
    f_equal. f_equal.
    - f_equal. f_equal. apply loc_package_ext.
      + simpl. rewrite fsetUA. reflexivity.
      + intro. reflexivity.
    - f_equal. f_equal. f_equal. apply loc_package_ext.
      + simpl. rewrite fsetUA. reflexivity.
      + simpl. intro. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma ler_refl :
    ∀ (x y :R),
      x = y →
      x <= y.
  Proof.
    intros x y [].
    auto.
  Qed.

  (** Security of PRF

    The bound is given by using the triangle inequality several times,
    using the following chain:
    IND_CPA false ≈ MOD_CPA_ff_pkg ∘ EVAL true
                  ≈ MOD_CPA_ff_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL true
                  ≈ IND_CPA true

    TODO: It would be nice to have the same names as the paper
    TODO: Can we devise a tactic to do the hops automatically?

  *)
  Theorem security_based_on_prf :
    ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords × chWords ],
      adv_forp A IND_CPA →
      Advantage IND_CPA A <=
      prf_epsilon {locpackage A ∘ MOD_CPA_ff_pkg } +
      statistical_gap A +
      prf_epsilon {locpackage A ∘ MOD_CPA_tt_pkg }.
  Proof.
    intros A hA. unfold prf_epsilon, statistical_gap.
    (* TODO adv_forp hyps are probably redundant of G in F,G,H *)
    (* First application of triangle inequality *)
    (* HOP IND_CPA false ≈ MOD_CPA_ff_pkg ∘ EVAL true *)
    pose proof @TriangleInequality as h1.
    specialize h1 with (3 := Advantage_equiv _ IND_CPA).
    specialize h1 with (1 := IND_CPA_equiv_false).
    specialize h1 with (1 := AdvantageE_equiv _ _ _).
    specialize (h1 A).
    unfold adv_forp in hA. simpl in hA. move: hA => /andP [hd _].
    forward h1.
    { unfold adv_for. simpl. rewrite hd. simpl.
      rewrite fdisjointUr.
      apply/andP. split.
      - unfold MOD_CPA_location. apply fdisjoints0.
      - rewrite fdisjointC. rewrite fdisjointC in hd.
        eapply fdisjoint_trans. 2: exact hd.
        unfold EVAL_location_tt, IND_CPA_location.
        apply fsubsetxx.
    }
    forward h1.
    { unfold adv_for. simpl. rewrite hd.
      rewrite andbC. simpl.
      rewrite fdisjointUr. apply/andP. split.
      - unfold MOD_CPA_location. apply fdisjoints0.
      - rewrite fdisjointC. rewrite fdisjointC in hd.
        eapply fdisjoint_trans. 2: exact hd.
        unfold EVAL_location_tt, IND_CPA_location.
        apply fsubsetxx.
    }
    forward h1.
    { unfold adv_for. simpl. rewrite hd. simpl. reflexivity. }
    cbn beta in h1.
    (* Second application of triangle inequality *)
    (* HOP MOD_CPA_ff_pkg ∘ EVAL true ≈ MOD_CPA_ff_pkg ∘ EVAL false *)
    pose proof @TriangleInequality as h2.
    lazymatch type of h1 with
    | context [ _ + AdvantageE ?p ?q _ ] =>
      specialize h2 with (3 := AdvantageE_equiv _ p q)
    end.
    (* Somehow, it doesn't work directly *)
    unshelve pose (foo := {locpackage MOD_CPA_ff_pkg ∘ EVAL false }).
    specialize h2 with (1 := AdvantageE_equiv _ _ foo).
    subst foo.
    specialize h2 with (1 := AdvantageE_equiv _ _ _).
    specialize (h2 A).
    forward h2.
    { unfold adv_for. simpl. apply/andP. split.
      - rewrite fdisjointUr. apply/andP. split.
        + unfold MOD_CPA_location. apply fdisjoints0.
        + rewrite fdisjointC. rewrite fdisjointC in hd.
          eapply fdisjoint_trans. 2: exact hd.
          unfold EVAL_location_tt, IND_CPA_location.
          apply fsubsetxx.
      - rewrite fdisjointUr. apply/andP. split.
        + unfold MOD_CPA_location. apply fdisjoints0.
        + rewrite fdisjointC. rewrite fdisjointC in hd.
          eapply fdisjoint_trans. 2: exact hd.
          unfold EVAL_location_ff, IND_CPA_location.
          (* Can we avoid this? *)
          (* Or should we require IND_CPA_location to include table_location?
            Or do as below and simply add a requirement of disjointness?
            Doesn't seem great.
          *)
          (* apply fsubsetxx. *)
          give_up.
    }
    forward h2.
    { unfold adv_for. simpl. rewrite hd. admit. }
    forward h2.
    { unfold adv_for. simpl. rewrite hd. admit. }
    (* HOP MOD_CPA_ff_pkg ∘ EVAL false ≈ MOD_CPA_tt_pkg ∘ EVAL false *)
    pose proof @TriangleInequality as h3.
    lazymatch type of h2 with
    | context [ _ + AdvantageE ?p ?q _ ] =>
      specialize h3 with (3 := AdvantageE_equiv _ p q)
    end.
    unshelve pose (foo := {locpackage MOD_CPA_tt_pkg ∘ EVAL false }).
    specialize h3 with (1 := AdvantageE_equiv _ _ foo).
    subst foo.
    specialize h3 with (1 := AdvantageE_equiv _ _ _).
    specialize (h3 A).
    forward h3.
    { unfold adv_for. simpl. admit. }
    forward h3.
    { unfold adv_for. simpl. rewrite hd. admit. }
    forward h3.
    { unfold adv_for. simpl. rewrite hd. admit. }
    (* HOP MOD_CPA_tt_pkg ∘ EVAL false ≈ MOD_CPA_tt_pkg ∘ EVAL true *)
    pose proof @TriangleInequality as h4.
    lazymatch type of h3 with
    | context [ _ + AdvantageE ?p ?q _ ] =>
      specialize h4 with (3 := AdvantageE_equiv _ p q)
    end.
    unshelve pose (foo := {locpackage MOD_CPA_tt_pkg ∘ EVAL true }).
    specialize h4 with (1 := AdvantageE_equiv _ _ foo).
    subst foo.
    specialize h4 with (1 := IND_CPA_equiv_true).
    specialize (h4 A).
    forward h4.
    { unfold adv_for. simpl. admit. }
    forward h4.
    { unfold adv_for. simpl. rewrite hd. admit. }
    forward h4.
    { unfold adv_for. simpl. rewrite hd. admit. }
    cbn beta in h4. rewrite GRing.addr0 in h4.
    (* Now we conclude *)
    eapply ler_trans. 1: exact h1.
    rewrite GRing.add0r.
    eapply ler_trans. 1: exact h2.
    clear hd h1 h2.
    eapply ler_trans.
    - eapply ler_add. 2: exact h3.
      auto.
    - clear h3.
      revert h4.
      unify_package_proofs.
      intro ineq.
      match goal with
      | |- context [ _ + ?x + _ ] =>
        set (x0 := x) in *
      end.
      rewrite GRing.addrCA.
      rewrite [X in _ <= X]GRing.addrAC.
      rewrite [X in _ <= X]GRing.addrC.
      eapply ler_add. 1: auto.
      clear x0.
      match goal with
      | |- context [ _ + ?x ] =>
        set (x0 := x) in *
      end.
      eapply ler_trans.
      1: eapply ler_add.
      2: exact ineq.
      1: auto.
      clear.
      rewrite 2!Advantage_E.
      (* It'd be nice to be able to rewrite with the following
        but I don't really know how to do it because of the needed
        dependency.
      *)
      Fail rewrite Advantage_link.
      eapply ler_refl.
      unfold AdvantageE.
      repeat change ({locpackage ?p }.(pack)) with p.
      package_before_rewrite.
      rewrite !link_assoc.
      package_after_rewrite.
      clear.
      f_equal.
      + rewrite distrC. f_equal. f_equal.
        * f_equal. f_equal. apply loc_package_ext.
          -- simpl. rewrite fsetUA. reflexivity.
          -- intro. reflexivity.
        * f_equal. f_equal. f_equal. apply loc_package_ext.
          -- simpl. rewrite fsetUA. reflexivity.
          -- intro. reflexivity.
      + f_equal. f_equal.
        * f_equal. f_equal. apply loc_package_ext.
          -- simpl. rewrite fsetUA. reflexivity.
          -- intro. reflexivity.
        * f_equal. f_equal. f_equal. apply loc_package_ext.
          -- simpl. rewrite fsetUA. reflexivity.
          -- intro. reflexivity.
  Admitted.

  (** TODO OLD BELOW **)

  (* Hopefully, we don't have to unfold these guys? *)

 (* INDCPA0 unfolded *)
  Definition LHS0 (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin (2^n)).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
      move => /= m_val'. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val.
      apply: ret ( r_val, m_val' ⊕ (PRF r_val k_val)).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
      { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
      move => tt. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
      move => /= m_val'. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val.
      apply: ret ( r_val, m_val' ⊕ (PRF r_val k_val)).
  Defined.

  (*EVAL0 inlined in MODCPA0 and unfolded  *)
  Definition RHS0 (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin (2^n)).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
      { apply: (putr _ key_location_in_INDCPA_location (Some  k_val)). apply: ret Datatypes.tt. }
      move => tt.
      exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
  Defined.

  Definition RHS0_swap (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin(2^n)).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. destruct option_k as [k_val |].
    - exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val.  apply: bind.
      { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
      move => tt.
      exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
  Defined.

  Definition RHS0_swap_swap  (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin (2^n)).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= m_val'. apply: ret m_val'. }
    move => /= m_val'. destruct option_k as [k_val |].
    - exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
      { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
      move => tt.
      exact: ret (r_val, (m_val' ⊕ (PRF r_val k_val))).
  Defined.

  (* Note duplicate in ElGamalStateProb *)
  (* TODO MOVE But where? *)
  Lemma eq_prog_semj_impl :
    ∀ L L' R R' A
      (p : program L _ A) (q : program R _ _)
      (p' : program L' _ A) (q' : program R' _ _),
      L = L' →
      R = R' →
      p ∙1 = p' ∙1 →
      q ∙1 = q' ∙1 →
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


  Lemma subset_key_rel : fsubset (fset [:: key_location ]) (fset [:: key_location ; table_location ]).
  Proof.
    apply /eqP. apply eq_fset => x.
    rewrite in_fsetU !in_fset. rewrite !in_cons.
    rewrite in_fset0. rewrite -orbA Bool.orb_false_r Bool.orb_false_l.
      by rewrite !orbA Bool.orb_diag.
  Qed.

  Lemma perfect_equivalence0 :
    ∀ (A : Adversary4Game [interface val #[i1] : chWords → chWords × chWords ])
      (Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                              A.π1 (IND_CPA_location ))
      (Hdisjoint2 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                              A.π1 (MOD_CPA_location :|: EVAL_location_tt)) ,
      (Pr (A ∘ IND_CPA false) true) =
      (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ (EVAL true)) true).
  Proof.
    intros A Hdisjoint1 Hdisjoint2.
    rewrite /IND_CPA.
    rewrite -link_assoc.
    apply: GRing.subr0_eq. apply: normr0_eq0.
    fold (@AdvantageE [interface val #[i1] : chWords → chWords × chWords]
                      (IND_CPA_pkg_ff ) (MOD_CPA_ff_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold IND_CPA_pkg_ff. unfold MOD_CPA_ff_pkg.
    unfold IND_CPA_opkg_ff. unfold MOD_CPA_ff.
    package_link_simplify.
    intros id h m.
    invert_interface_in h.
    repeat opackage_transport_simplify.
    package_pdef_simpl.
    unfold pdefS in m. simpl in m.
    change (Choice.sort (chElement ('fin (2^n)%N))) in m.
    suffices: ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ repr (LHS0 m) ≈ repr (RHS0 m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - unfold IND_CPA_location. reflexivity.
      - unfold IND_CPA_location. unfold MOD_CPA_location.
        rewrite fset0U. reflexivity.
      (* reflexivity. exact: MOD_CPA_location_rel_loc. *)
      - simpl. f_equal. extensionality v.
        destruct v.
        + cbn - [lookup_op]. f_equal.
        + cbn - [lookup_op]. f_equal.
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
      apply: rrewrite_eqDistrR.
      { apply: rsame_head => m'.
      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => a1 a2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
            by apply: rreflexivity_rule.
        ++ apply: rsamplerC' (U (mkpos i_words)) (k_val ← sample U (mkpos i_key) ;; ret k_val). } }
      move => s'. apply rcoupling_eq with (ψ := fun '(h1, h2) => h1 = h2). 2: by reflexivity.
      apply: rrewrite_eqDistrR.
      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => a1 a2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
            by apply: rreflexivity_rule.
        ++ apply: rsamplerC' (U (mkpos i_words)) (k_val ← sample U (mkpos i_key) ;; ret k_val). }
      move => s''. apply rcoupling_eq with (ψ := fun '(h1, h2) => h1 = h2). 2: by reflexivity.
      apply: rsame_head => k.
      apply: rrewrite_eqDistrL.
      { { apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => a1 a2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
            by apply: rreflexivity_rule.
        ++ apply: rsamplerC' (U (mkpos i_words)) (put key_location := Some k ;; ret Datatypes.tt). } }
      move => s'''. apply rcoupling_eq with (ψ := fun '(h1, h2) => h1 = h2). 2: by reflexivity.
      apply: rsame_head => m'.
      apply: rswap_ruleR. { move => bs bs' H. assumption. }
      ++ move => tt r. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
          by apply: rreflexivity_rule.
      ++ apply: rsamplerC (U (mkpos i_words)) (put key_location := Some k ;; ret Datatypes.tt).
  Qed.

 (*INDCPA1 unfolded *)
  Definition LHS1 (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin(2^n)).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => [k_val | ].
    - apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val.
      exact: ret (r_val, m ⊕ (PRF r_val k_val)).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
       { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
       move => tt. apply: bind.
      { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val.
       exact: ret (r_val, m ⊕ (PRF r_val k_val)).
  Defined.

  (* EVAL0 inlined in MODCPA1 *)
  Definition RHS1 (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0  ('fin (2^n) × 'fin(2^n)).
  Proof.
    apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
    move => /= r_val. apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => option_k. destruct option_k as [k_val |].
    - exact: ret (r_val, m ⊕ (PRF r_val k_val)).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
       { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
       move => tt.
     exact: ret (r_val, m ⊕ (PRF r_val k_val)).
  Defined.

  Definition RHS1_swap (m : ('fin (2^n)%N)) :
    program IND_CPA_location fset0 ('fin (2^n) × 'fin (2^n)).
  Proof.
    apply: bind.
    { apply: (getr _ key_location_in_INDCPA_location) => /= option_k. apply: ret option_k. }
    move => option_k. apply: bind.
    { apply: (sampler (U (mkpos i_words))) => /= r_val. apply: ret r_val. }
      move => /= r_val. destruct option_k as [k_val |].
    - exact: ret (r_val, m ⊕ (PRF r_val k_val)).
    - apply: bind.
      { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
      move => /= k_val. apply: bind.
       { apply: (putr _ key_location_in_INDCPA_location (Some k_val)). apply: ret Datatypes.tt. }
       move => tt.
     exact: ret (r_val, m ⊕ (PRF r_val k_val)).
  Defined.

  Lemma perfect_equivalence1 (A : Adversary4Game [interface val #[i1] : chWords → chWords × chWords])
      { Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                               A.π1 (IND_CPA_location ) }
      { Hdisjoint2 : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType))
                               A.π1 (MOD_CPA_location :|: EVAL_location_tt) } :
  (Pr (A ∘ IND_CPA true) true) = (Pr ((A ∘ MOD_CPA_tt_pkg) ∘ (EVAL true)) true).
  Proof.
    rewrite -link_assoc.
    apply: GRing.subr0_eq. apply: normr0_eq0.
    rewrite /IND_CPA.
    fold (@AdvantageE [interface val #[i1] : chWords → chWords × chWords]
                      (IND_CPA_pkg_tt) (MOD_CPA_tt_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
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
    unfold pdefS in m. simpl in m.
    change (Choice.sort (chElement ('fin (2^n)%N))) in m.
    suffices: ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ repr (LHS1 m) ≈ repr (RHS1 m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - rewrite /IND_CPA_location. reflexivity.
      - unfold MOD_CPA_location. rewrite fset0U. reflexivity.
      - simpl.  f_equal. extensionality v.
        cbn - [lookup_op].
        destruct v eqn:Hv.
        + cbn - [lookup_op]. reflexivity.
        + cbn - [lookup_op]. reflexivity.
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
      + apply: rrewrite_eqDistrR.
        { apply: rsame_head => k. apply: rswap_ruleR. { move => bs bs' H. assumption. }
        ++ move => tt r.
          apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
          apply: rreflexivity_rule.
        ++ apply: rsamplerC (U (mkpos i_words)) (put key_location := Some k ;; ret Datatypes.tt). }
      move => s. eapply rcoupling_eq with (ψ := (fun '(h1, h2) => h1 = h2)).  2: by reflexivity.
        apply: rswap_ruleR. { move => bs bs' H. assumption. }
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
    IND_CPA_location = MOD_CPA_location :|: EVAL_location_tt.
  Proof.
    rewrite /IND_CPA_location /MOD_CPA_location /EVAL_location_tt.
    rewrite fset0U. reflexivity.
  Qed.


  Theorem security_based_on_prf (Hprf : PRF_security) :
    ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords × chWords ],
    (* Rem.: this extra condition is annoying, but it comes from the fact
           that we write at some point link (link A MOD_CPA) EVAL_ff, which
           implies that EVAL_ff and A have disjoint memories *)
    ∀ Hdisjoint_extra : fdisjoint A.π1 EVAL_location_ff,
    ∀ Hdisjoint1 Hdisjoint2,
      (@Advantage _ IND_CPA A Hdisjoint1 Hdisjoint2) <=
      prf_epsilon (link A (MOD_CPA_ff_pkg)) + (@statistical_gap A + prf_epsilon (link A (MOD_CPA_tt_pkg))).
  Proof.
    rewrite /Advantage => A Hdisjoint_extra Hdisjoint1 Hdisjoint2.
    simpl (IND_CPA true).π1 in Hdisjoint2. simpl (IND_CPA false).π1 in Hdisjoint1.
    rewrite same_locations in Hdisjoint2.
    rewrite (@perfect_equivalence0 A Hdisjoint1 Hdisjoint2).
    rewrite (@perfect_equivalence1 A Hdisjoint1 Hdisjoint2).
    move: Hdisjoint2. rewrite fdisjointUr. move /andP => [Hdisjoint21 Hdisjoint22].
    simpl.
    assert (`|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL false) true -
     Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true| = prf_epsilon (A ∘ MOD_CPA_ff_pkg)) as H1.
    { assert (fdisjoint (A ∘ MOD_CPA_ff_pkg).π1 (EVAL false).π1) as Hdis1.
      { simpl. unfold MOD_CPA_location. rewrite fsetU0. assumption. }
      assert (fdisjoint (A ∘ MOD_CPA_ff_pkg).π1 (EVAL true).π1) as Hdis2.
      { simpl. unfold MOD_CPA_location. rewrite fsetU0. assumption. }
      apply (Hprf (A ∘ MOD_CPA_ff_pkg) Hdis1 Hdis2). }
    rewrite distrC /= in H1.
    rewrite -(GRing.subrK (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true) (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_tt) true)).
    unshelve eapply ler_trans.
    2: { rewrite -GRing.addrA. apply ler_norm_add. }
    rewrite H1. clear H1.
    assert (`|Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL false) true -
     Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true| = prf_epsilon (A ∘ MOD_CPA_tt_pkg)) as H2.
    { assert (fdisjoint (A ∘ MOD_CPA_tt_pkg).π1 (EVAL false).π1) as Hdis3.
      { simpl. unfold MOD_CPA_location. rewrite fsetU0. assumption. }
      assert (fdisjoint (A ∘ MOD_CPA_tt_pkg).π1 (EVAL true).π1) as Hdis4.
      { simpl. unfold MOD_CPA_location. rewrite fsetU0. assumption. }
      apply (Hprf (A ∘ MOD_CPA_tt_pkg) Hdis3 Hdis4). }
    apply ler_add.
    1: { apply lerr. }
    rewrite /= in H2.
    rewrite -(GRing.subrK (Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL_pkg_ff) true) (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true)).
    unshelve eapply ler_trans.
    2: { rewrite -GRing.addrA. apply ler_norm_add. }
    rewrite H2. clear H2.
    apply ler_add.
    2: { simpl. apply lerr. }
    rewrite /statistical_gap. simpl.
    rewrite distrC.
    apply lerr.
Qed.

End PRF_example.
