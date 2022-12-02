(**
  This formalises Theorem 3.6 from "The Joy of Cryptography" (p. 51).
  It is a simple 2-out-of-2 secret-sharing scheme with perfect security,
  based on XOR.

  It is fairly simple to understand. The hardest part is probably the definition
  of [plus] (XOR), which is not really necessary to understand the proof.

  The final statement ([unconditional_secrecy]) is equivalent to that of the
  books: The scheme achieves perfect secerery with up to two shares
  (non-inclusive).
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

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

Section SecretSharing_example.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := chFin (mkpos Word_N).

(**
  The first bit is a formalisation of [plus] (XOR).
  It is similar to the definitions in OTP.v and PRF.v, but it has been split
  into lemmas to hopefully be easier to read.
  It is still somewhat unwieldy though.
*)

(**
  Lemmas for the [plus] obligation.
*)
Lemma pow2_inj m:
  (2 ^ m)%N = BinNat.N.to_nat (BinNat.N.pow (BinNums.Npos (BinNums.xO 1%AC)) (BinNat.N.of_nat m)).
Proof.
  elim: m => [// | m IHm].
  rewrite expnSr Nnat.Nat2N.inj_succ BinNat.N.pow_succ_r' Nnat.N2Nat.inj_mul PeanoNat.Nat.mul_comm.
  by apply: f_equal2.
Qed.

Lemma log2_lt_pow2 w m:
  (w.+1 < 2^m)%N ->
  BinNat.N.lt (BinNat.N.log2 (BinNat.N.of_nat w.+1)) (BinNat.N.of_nat m).
Proof.
  move=> H.
  rewrite -BinNat.N.log2_lt_pow2.
  - rewrite /BinNat.N.lt Nnat.N2Nat.inj_compare PeanoNat.Nat.compare_lt_iff -pow2_inj Nnat.Nat2N.id.
    by apply /ltP.
  - rewrite Nnat.Nat2N.inj_succ.
    by apply: BinNat.N.lt_0_succ.
Qed.

#[program] Definition plus (w k: Word): Word :=
  @Ordinal _ (BinNat.N.to_nat (BinNat.N.lxor
    (BinNat.N.of_nat (nat_of_ord w))
    (BinNat.N.of_nat (nat_of_ord k)))) _.
Next Obligation.
  move: w k => [[|w] Hw] [[|k] Hk].
  1-3: by rewrite /= ?Pnat.SuccNat2Pos.id_succ.
  move: (log2_lt_pow2 _ _ Hw) => H1.
  move: (log2_lt_pow2 _ _ Hk) => H2.
  move: (BinNat.N.max_lub_lt _ _ _ H1 H2) => Hm.
  case: (BinNat.N.eq_dec (BinNat.N.lxor (BinNat.N.of_nat w.+1) (BinNat.N.of_nat k.+1)) BinNat.N0) => H0.
  1: by rewrite H0 expn_gt0.
  move: (BinNat.N.log2_lxor (BinNat.N.of_nat w.+1) (BinNat.N.of_nat k.+1)) => Hbound.
  move: (BinNat.N.le_lt_trans _ _ _ Hbound Hm).
  rewrite -BinNat.N.log2_lt_pow2.
  2: by apply BinNat.N.neq_0_lt_0.
  rewrite /BinNat.N.lt Nnat.N2Nat.inj_compare PeanoNat.Nat.compare_lt_iff -pow2_inj.
  by move /ltP.
Qed.

Notation "m ⊕ k" := (plus m k) (at level 70).

(**
  Some lemmas for [plus] itself.
*)
Lemma plus_comm m k:
  (m ⊕ k) = (k ⊕ m).
Proof.
  apply: ord_inj.
  case: m => m ? /=.
  by rewrite BinNat.N.lxor_comm.
Qed.

Lemma plus_assoc m l k:
  ((m ⊕ l) ⊕ k) = (m ⊕ (l ⊕ k)).
Proof.
  apply: ord_inj.
  case: m => m ? /=.
  rewrite !Nnat.N2Nat.id.
  by rewrite BinNat.N.lxor_assoc.
Qed.

Lemma plus_involutive m k:
  (m ⊕ k) ⊕ k = m.
Proof.
  rewrite plus_assoc.
  apply: ord_inj.
  case: m => m ? /=.
  rewrite Nnat.N2Nat.id.
  rewrite BinNat.N.lxor_nilpotent.
  rewrite BinNat.N.lxor_0_r.
  by rewrite Nnat.Nat2N.id.
Qed.

#[local] Open Scope package_scope.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

(**
  We can't use sequences directly in [choice_type] so instead we use a map from
  natural numbers to the type.
*)
Definition chSeq t := chMap 'nat t.

Notation " 'seq t " := (chSeq t) (in custom pack_type at level 2).
Notation " 'seq t " := (chSeq t) (at level 2): package_scope.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition shares: nat := 0.

Definition SHARE_pkg_tt:
  package fset0 [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'seq 'word ] :=
  [package
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'nat): 'seq 'word {
      if size (domm U) >= 2 then ret emptym
      else
      s0 <$ uniform (2^n) ;;
      let s1 := s0 ⊕ ml in
      let sh := [fmap (0, s0) ; (1, s1)] in
      ret (fmap_of_seq (pmap sh (domm U)))
    }
  ].

Definition SHARE_pkg_ff:
  package fset0 [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'seq 'word ] :=
  [package
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'nat): 'seq 'word {
      if size (domm U) >= 2 then ret emptym
      else
      s0 <$ uniform (2^n) ;;
      let s1 := s0 ⊕ mr in
      let sh := [fmap (0, s0) ; (1, s1)] in
      ret (fmap_of_seq (pmap sh (domm U)))
    }
  ].

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

Definition SHARE := mkpair SHARE_pkg_tt SHARE_pkg_ff.

Lemma SHARE_equiv:
  SHARE true ≈₀ SHARE false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  case m => [[ml mr] U].
  case: (_ (domm U)) => {U} [|a U] /=.
  1: by apply: rreflexivity_rule.
  case: U => [|b U] /=.
  2: by apply: rreflexivity_rule.
  case: a => [|[|a]] /=.
  1,3: by apply: rreflexivity_rule.
  apply: r_uniform_bij => [|s0].
  1: {
    exists (fun x => x ⊕ (ml ⊕ mr)) => x.
    all: by apply: plus_involutive.
  }
  rewrite plus_assoc plus_involutive.
  by apply: rreflexivity_rule.
Qed.

(**
  This corresponds to Theorem 3.6 from "The Joy of Cryptography".
*)
Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'seq 'word ]
    A_export A ->
  Advantage SHARE A = 0%R.
Proof.
  move=> vA.
  rewrite Advantage_E Advantage_sym.
  by rewrite SHARE_equiv ?fdisjoints0.
Qed.

End SecretSharing_example.
