(******************************************************************************)
(*                             Secret Sharing                                 *)
(*                                                                            *)
(* Formalization of Theorem 3.6 from "The Joy of Cryptography" (p. 51).       *)
(* It is a simple 2-out-of-2 secret-sharing scheme with perfect security,     *)
(* based on XOR. Messages are n-bit words, and the scheme works by letting    *)
(* the first share to be a random word, and the second share be the first     *)
(* share XOR'ed with the message.                                             *)
(*                                                                            *)
(* At the beginning we prove some properties for the plus operator, such as   *)
(* associativity or involutive.                                               *)
(* The final statement ([unconditional_secrecy]) is equivalent to that of     *)
(* the books: The scheme achieves perfect security with up to two shares      *)
(* (non-inclusive).                                                           *)
(*                                                                            *)
(* * Section SecretSharing_example                                            *)
(*    Word == type for the words in the protocol                              *)
(*   'word == notation for Word                                               *)
(*    plus == receives two Words and returns the XOR of them                  *)
(*   m ⊕ k == XOR of words m and k                                            *)
(*  'set t == local choice_type for sets                                      *)
(******************************************************************************)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
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
Import BinNat.
Import BinNums.
Import Nnat.
Import BinPosDef.

Section SecretSharing_example.

Variable (n: nat).

Definition Word_N: nat := 2^n.

(* We define words to belong to the finite type of size Word_N                *)
Definition Word: choice_type := chFin (mkpos Word_N).

(******************************************************************************)
(*******************Definiton of the [plus] obligation.************************)
(******************************************************************************)

Lemma pow2_inj m:
  (2 ^ m)%nat = N.to_nat (2 ^ (N.of_nat m)).
Proof.
  elim: m => [// | m IHm].
  rewrite expnSr Nat2N.inj_succ N.pow_succ_r'.
  rewrite N2Nat.inj_mul PeanoNat.Nat.mul_comm.
  by apply: f_equal2.
Qed.

Lemma log2_lt_pow2 w m:
  (w.+1 < 2^m)%nat -> ((N.log2 (N.of_nat w.+1)) < (N.of_nat m))%N.
Proof.
  move=> H.
  rewrite -N.log2_lt_pow2.
  - rewrite /N.lt N2Nat.inj_compare PeanoNat.Nat.compare_lt_iff.
    rewrite -pow2_inj Nat2N.id.
    by apply /ltP.
  - rewrite Nat2N.inj_succ.
    by apply: N.lt_0_succ.
Qed.

#[program] Definition plus (w k: Word): Word :=
  @Ordinal _ (N.to_nat (N.lxor
    (N.of_nat (nat_of_ord w))
    (N.of_nat (nat_of_ord k)))) _.
Next Obligation.
  (* Case analysis on w and k *)
  move: w k => [[|w] Hw] [[|k] Hk];

  (* Discharge the trivial cases where w or k equals 0 *)
  try by rewrite /= ?Pnat.SuccNat2Pos.id_succ.

  (* max(log2 (w+1), log2 (k+1) < n) *)
  move: (log2_lt_pow2 _ _ Hw) => H1.
  move: (log2_lt_pow2 _ _ Hk) => H2.
  move: (N.max_lub_lt _ _ _ H1 H2) => Hm.

  (* Case analysis on the decidable equality lxor (w+1) (k+1) = 0 *)
  case: (N.eq_dec (N.lxor (N.of_nat w.+1) (N.of_nat k.+1)) N0) => H0.

  (* lxor (w+1) (k+1) <> 0 *)
  1: by rewrite H0 expn_gt0.
  (* lxor (w+1) (k+1) <> 0 *)
  move => {H1 H2}.
  move: (N.log2_lxor (N.of_nat w.+1) (N.of_nat k.+1)) => Hbound.
  move: (N.le_lt_trans _ _ _ Hbound Hm) => {Hm Hbound}.
  rewrite -N.log2_lt_pow2.

  (* Process the trivial case 0 < lxor (w+1) (k+1) *)
  2: by apply N.neq_0_lt_0.
  (* Convert from the N type to nat so we can use decidability on < *)
  rewrite /N.lt N2Nat.inj_compare PeanoNat.Nat.compare_lt_iff -pow2_inj.
  by move /ltP.
Qed.

Notation "m ⊕ k" := (plus m k) (at level 70).

(******************************************************************************)
(******************Some lemmas for [plus] itself.******************************)
(******************************************************************************)

Lemma plus_assoc m l k:
  ((m ⊕ l) ⊕ k) = (m ⊕ (l ⊕ k)).
Proof.
  apply: ord_inj.
  case: m => m ? /=.
  rewrite !N2Nat.id.
  by rewrite N.lxor_assoc.
Qed.

Lemma plus_involutive m k:
  (m ⊕ k) ⊕ k = m.
Proof.
  rewrite plus_assoc.
  apply: ord_inj.
  case: m => m ? /=.
  rewrite N2Nat.id N.lxor_nilpotent.
  by rewrite N.lxor_0_r Nat2N.id.
Qed.

#[local] Open Scope package_scope.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

(* We can't use sets directly in [choice_type] so instead we use a map to     *)
(* units. We can then use [domm] to get the domain, which is a set.           *)

Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition shares: nat := 0.

(******************************************************************************)
(********************Definition of the games.**********************************)
(******************************************************************************)

Definition SHARE_pkg_tt:
  package [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'list 'word ] :=
  [package emptym ;
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'nat): 'list 'word {
      if size (domm U) >= 2 then ret [::]
      else
      s0 <$ uniform (2^n) ;;
      let s1 := s0 ⊕ ml in
      let sh := [fmap (0, s0) ; (1, s1)] in
      ret (pmap sh (domm U))
    }
  ].

Definition SHARE_pkg_ff:
  package [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'list 'word ] :=
  [package emptym ;
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'nat): 'list 'word {
      if size (domm U) >= 2 then ret [::]
      else
      s0 <$ uniform (2^n) ;;
      let s1 := s0 ⊕ mr in
      let sh := [fmap (0, s0) ; (1, s1)] in
      ret (pmap sh (domm U))
    }
  ].

Definition SHARE b := if b then SHARE_pkg_tt else SHARE_pkg_ff.

(******************************************************************************)
(************Proof that the games are equivalent.******************************)
(******************************************************************************)

Lemma SHARE_equiv:
  SHARE true ≈₀ SHARE false.
Proof.
  (**
    Since the games have no state, we don’t need to maintain an invariant, and
    only need to ensure the games have the same output distribution.
  *)
  apply: eq_rel_perf_ind_eq.

  (* Create a goal for each procedure, one in this case *)
  simplify_eq_rel m.

  (* We can weaken the postcondition*)
  apply rpost_weaken_rule with eq.
  2: by move=> [? ?] [? ?] [].

  (* Unpack m as ml, mr and U *)
  case m => [[ml mr] U].

  (* Case distinction over the set domm U *)
  case: (_ (domm U)) => {U} [|a U] /=.
  (* domm U = ∅ *)
  1: by apply: rreflexivity_rule.
  (* domm U != ∅ *)
  (* Case distinction over the set U *)
  case: U => [|b U].
  (* U != ∅ *)
  2: by apply: rreflexivity_rule.
  (* U = ∅ *)
  (* Here we distinguish the cases when a = 0, 1 or 2*)
  case: a => [|[|a]].
  (*
    If a = 0 then both games return the same value and
    if a >= 2 we are in an impossible case since we know that a can
    only be 0 or 1.
  *)
  1,3: apply: rreflexivity_rule.
  (* U = {1} *)
  (* We sample in the same way to get s0*)
  apply: r_uniform_bij => [|s0].
  (* We know prove that s0r = s0l ⊕ ml ⊕ mr is a bijection *)
  1: {
    exists (fun x => x ⊕ (ml ⊕ mr)) => x.
    all: by apply: plus_involutive.
  }
  (* Because of the bijection, they must have the same output distribution *)
  rewrite plus_assoc. rewrite plus_involutive.
  by apply: rreflexivity_rule.
Qed.

(******************************************************************************)
(********Proof to the Theorem 3.6 from "The Joy of Cryptography".**************)
(******************************************************************************)

Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[shares]: ('word × 'word) × 'set 'nat → 'list 'word ]
    A_export A ->
  Advantage SHARE A = 0%R.
Proof.
  move=> vA.
  (*Express the Advantage in terms of the games and the adversary *)
  rewrite Advantage_E Advantage_sym.
  rewrite SHARE_equiv //; fmap_solve.
Qed.

End SecretSharing_example.
