(**
  This formalises Claim 5.10 from "The Joy of Cryptography" (p. 111).
  It shows how to work with loops.

  The one part we cannot prove is the
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

Section SymmRatchet_example.

(**
  We can't use sequences directly in [choice_type] so instead we use a map from
  natural numbers to the type.
*)
Definition chSeq t := chMap 'nat t.

Notation " 'seq t " := (chSeq t) (in custom pack_type at level 2).
Notation " 'seq t " := (chSeq t) (at level 2): package_scope.

(**
  This function is equivalent to [fmap_of_seq], but its definition is simpler,
  which makes it possible to prove that [unzip2] cancels it.
  This is useful since each iteration of a loop has to convert between the
  actual [seq] and the [chSeq] we can actually use in SSProve.
*)
Definition seq_to_chseq {T} (s: seq T) :=
  mkfmap (zip (iota 0 (size s)) s).

Lemma unzip2_seq_to_chseq {T} (s: seq T):
  unzip2 (seq_to_chseq s) = s.
Proof.
  rewrite mkfmapK ?unzip2_zip ?unzip1_zip ?size_iota //.
  rewrite (@eq_sorted _ _ ltn).
  1: by apply: iota_ltn_sorted.
  move=> a b.
  by rewrite /Ord.lt /= ltn_neqAle Bool.andb_comm.
Qed.

Definition tt: 'unit := Datatypes.tt.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := 'fin Word_N.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Context (PRG: Word -> Word * Word).
Context (enc: Word -> Word -> Word).

Definition ctxt: nat := 0.
Definition query: nat := 1.
Definition attack: nat := 2.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

(**
  A [map_loop] is like the [map] function, but it can be used directly as [code]
  in SSProve. This makes it possible to use features from SSProve inside it,
  like sampling random values, calling an [#import]ed function, and even reading
  or writing memory.

  Alternatively, one can think of it as a for-loop that writes to the [i]th
  location of an array on index [i].

  It takes a sequence [s] to loop over, a state [a] and a function which returns
  a mapped value, and a new [a] to be used in the next iteration of the loop.

  It returns a pair of the mapped sequence as a [chSeq] (since SSProve cannot
  work directly with [seq]), and the final state [a].
*)
Fixpoint map_loop {T} {U A: choice_type} (s: seq T) (a: A) (c: T -> A -> raw_code (U × A)):
  raw_code (('seq U) × A) :=
  match s with
  | [::]    => ret (emptym, a)
  | t :: s' =>
    ua1 ← c t a ;;
    ua2 ← map_loop s' ua1.2 c ;;
    ret (seq_to_chseq (ua1.1 :: unzip2 ua2.1), ua2.2)
  end.

(**
  This is a proof that a loop is valid code, as long as the loop body is valid
  for all input values.
*)
Lemma map_loop_valid {T} {U A: choice_type} {L I} (s: seq T) (a: A) (c: T -> A -> raw_code (U × A)):
  (forall t a', ValidCode L I (c t a')) ->
  ValidCode L I (map_loop s a c).
Proof.
  move=> H.
  elim: s => [|t s IHs] /= in a*.
  - by apply: valid_ret.
  - apply: valid_bind => ua1 /=.
    apply: valid_bind => ua2.
    by apply: valid_ret.
Qed.

(**
  We add the validity proof to the [ssprove_valid_db] database, which lets
  SSProve pick up on it automatically.
*)
Hint Extern 1 (ValidCode ?L ?I (map_loop ?s ?a ?c)) =>
  eapply map_loop_valid ;
  intro
  : typeclass_instances ssprove_valid_db.

(**
  The next proof tells SSProve how to link code with a [map_loop]. Specifically,
  it should link any functions called inside the loop body.
*)
Lemma code_link_map_loop {T} {U A: choice_type} (s: seq T) (a: A) (c: T -> A -> raw_code (U × A)) p:
  code_link (map_loop s a c) p = map_loop s a (fun t a => code_link (c t a) p).
Proof.
  elim: s => [// | t s IHs] /= in a*.
  rewrite code_link_bind.
  f_equal.
  apply: boolp.funext => ua1 /=.
  by rewrite code_link_bind IHs.
Qed.

(**
  We also add this to a database to help the [ssprove_code_simpl] tactic
  automatically simplify loops.
*)
Hint Extern 50 (_ = code_link (map_loop _ _ _) _) =>
  rewrite code_link_map_loop
  : ssprove_code_simpl.

Definition CTXT_pkg_tt:
  package fset0
    [interface]
    [interface #val #[ctxt]: 'word → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'word {
      k <$ uniform Word_N ;;
      ret (enc k m)
    }
  ].

Definition CTXT_pkg_ff:
  package fset0
    [interface]
    [interface #val #[ctxt]: 'word → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'word {
      c <$ uniform Word_N ;;
      ret c
    }
  ].

Definition CTXT := mkpair CTXT_pkg_tt CTXT_pkg_ff.

(**
  We only define security of the stretched PRG. It is not currently possible to
  prove this is secure from a simple PRG definition, because the number of
  iterations depends on the input.

  StretchPRG.v contains a proof of a single iteration, and a technique similar
  to the one in [PRFPRG.v] could be used to prove a fixed number of iterations,
  but not a variable number. So, while we can argue informally that they are
  indistinguishable, we cannot (yet) prove it inside SSProve, so instead we
  leave it as an assumption.
*)
Definition GEN_STRETCH_pkg_tt:
  package fset0 [interface]
    [interface #val #[query]: 'nat → ('seq 'word) × 'word ] :=
  [package
    #def #[query] (k: 'nat): ('seq 'word) × 'word {
      s0 <$ uniform Word_N ;;
      @map_loop _ 'word _ (iota 0 k) s0 (fun _ si =>
        ret (PRG si)
      )
    }
  ].

Definition GEN_STRETCH_pkg_ff:
  package fset0 [interface]
    [interface #val #[query]: 'nat → ('seq 'word) × 'word ] :=
  [package
    #def #[query] (k: 'nat): ('seq 'word) × 'word {
      t ← @map_loop _ 'word _ (iota 0 k) tt (fun _ _ =>
        ti <$ uniform Word_N ;;
        ret (ti, tt)
      ) ;;
      sn <$ uniform Word_N ;;
      ret (t.1, sn)
    }
  ].

Definition GEN_STRETCH := mkpair GEN_STRETCH_pkg_tt GEN_STRETCH_pkg_ff.

(**
  The rest of the games are similar to the ones in the book.
*)
Definition ATTACK_pkg_tt:
  package fset0 [interface]
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ] :=
  [package
    #def #[attack] (m: 'seq 'word): ('seq 'word) × 'word {
      s0 <$ uniform Word_N ;;
      @map_loop _ 'word _ (unzip2 m) s0 (fun mi si =>
        let xy := PRG si in
        ret (enc xy.1 mi, xy.2)
      )
    }
  ].

Definition ATTACK_pkg_ff:
  package fset0 [interface]
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ] :=
  [package
    #def #[attack] (m: 'seq 'word): ('seq 'word) × 'word {
      c ← @map_loop _ 'word _ (unzip2 m) tt (fun _ _ =>
        ci <$ uniform Word_N ;;
        ret (ci, tt)
      ) ;;
      sn <$ uniform Word_N ;;
      ret (c.1, sn)
    }
  ].

Definition ATTACK := mkpair ATTACK_pkg_tt ATTACK_pkg_ff.

Definition ATTACK_GEN_pkg:
  package fset0
    [interface #val #[query]: 'nat → ('seq 'word) × 'word ]
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ] :=
  [package
    #def #[attack] (m: 'seq 'word): ('seq 'word) × 'word {
      #import {sig #[query]: 'nat → ('seq 'word) × 'word } as query ;;
      ts ← query (size m) ;;
      c ← @map_loop _ 'word _ (zip (unzip2 ts.1) (unzip2 m)) tt (fun tm _ =>
        let (ti, mi) := (tm.1, tm.2) in
        ret (enc ti mi, tt)
      ) ;;
      ret (c.1, ts.2)
    }
  ].

Definition ATTACK_HYB_pkg:
  package fset0 [interface]
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ] :=
  [package
    #def #[attack] (m: 'seq 'word): ('seq 'word) × 'word {
      c ← @map_loop _ 'word _ (unzip2 m) tt (fun mi _ =>
        ti <$ uniform Word_N ;;
        ret (enc ti mi, tt)
      ) ;;
      sn <$ uniform Word_N ;;
      ret (c.1, sn)
    }
  ].

Definition ATTACK_CTXT_pkg:
  package fset0
  [interface #val #[ctxt]: 'word → 'word ]
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ] :=
  [package
    #def #[attack] (m: 'seq 'word): ('seq 'word) × 'word {
      #import {sig #[ctxt]: 'word → 'word } as ctxt ;;
      c ← @map_loop _ 'word _ (unzip2 m) tt (fun mi _ =>
        ci ← ctxt mi ;;
        ret (ci, tt)
      ) ;;
      sn <$ uniform Word_N ;;
      ret (c.1, sn)
    }
  ].

Lemma ATTACK_equiv_true:
  ATTACK true ≈₀ ATTACK_GEN_pkg ∘ GEN_STRETCH true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  simplify_linking.
  ssprove_code_simpl.
  ssprove_sync_eq=> s0.
  erewrite bind_cong.
  2: by [].
  2: {
    apply: boolp.funext => x.
    erewrite (@code_link_map_loop _ 'word _ (zip _ _) tt) => /=.
    erewrite bind_cong.
    1,2: by [].
    apply: boolp.funext => y.
    by rewrite {1}(lock (y.1)).
  }
  rewrite -(bind_ret _ (map_loop (unzip2 m) s0 _)).
  erewrite bind_cong.
  2: by [].
  2: {
    apply: boolp.funext => x.
    rewrite {1}(surjective_pairing x).
    by rewrite {1}(lock x.1).
  }
  move: (@locked _) => /= X.
  ssprove_code_simpl.
  rewrite -(size_map snd) -/unzip2.
  move: 0 (unzip2 m) => {m} a m.
  elim: m => [|mi m IHm] /= in X a s0*.
  1: by apply: rreflexivity_rule.
  rewrite (lock seq_to_chseq).
  ssprove_code_simpl.
  case: (PRG s0) => [ti si] /=.
  rewrite -lock.
  erewrite (bind_cong _ _ (@map_loop _ 'word _ (iota a.+1 (size m)) si _)).
  2: by [].
  2: {
    apply: boolp.funext => x.
    by rewrite unzip2_seq_to_chseq.
  }
  ssprove_code_simpl.
  by specialize (IHm (fun x => X (seq_to_chseq (enc ti mi :: unzip2 x)))).
Qed.

Lemma ATTACK_HYB_equiv_1:
  ATTACK_GEN_pkg ∘ GEN_STRETCH false ≈₀ ATTACK_HYB_pkg.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  simplify_linking.
  rewrite cast_fun_K.
  ssprove_code_simpl.
  ssprove_swap_lhs 0.
  ssprove_swap_rhs 0.
  ssprove_sync_eq=> sn.
  erewrite bind_cong.
  2: by [].
  2: {
    apply: boolp.funext => x.
    erewrite (@code_link_map_loop _ 'word _ (zip _ _) tt) => /=.
    erewrite bind_cong.
    1,2: by [].
    apply: boolp.funext => y.
    by rewrite {1}(lock (y.1)).
  }
  erewrite (bind_cong _ _ (map_loop (unzip2 m) tt _)).
  2: by [].
  2: {
    apply: boolp.funext => x.
    rewrite {1}(surjective_pairing x).
    by rewrite {1}(lock x.1).
  }
  rewrite -(size_map snd) -/unzip2.
  move: 0 (unzip2 m) (@locked _) => {m} a m X.
  elim: m => [|mi m IHm] /= in X a*.
  1: by apply: rreflexivity_rule.
  rewrite (lock seq_to_chseq).
  ssprove_code_simpl.
  ssprove_sync_eq=> ci.
  rewrite -lock.
  erewrite (bind_cong _ _ (@map_loop _ 'word _ (iota a.+1 (size m)) tt _)).
  2: by [].
  2: {
    apply: boolp.funext => x.
    rewrite unzip2_seq_to_chseq.
    by [].
  }
  ssprove_code_simpl.
  specialize (IHm (fun s => X (seq_to_chseq (enc ci mi :: unzip2 s)))).
  by simpl in IHm.
Qed.

Lemma ATTACK_HYB_equiv_2:
  ATTACK_HYB_pkg ≈₀ ATTACK_CTXT_pkg ∘ CTXT true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  simplify_linking.
  ssprove_code_simpl.
  ssprove_swap_lhs 0.
  ssprove_swap_rhs 0.
  ssprove_sync_eq=> sn.
  rewrite (@code_link_map_loop _ 'word _ (unzip2 m) tt _) /=.
  simplify_linking.
  by apply: rreflexivity_rule.
Qed.

Lemma ATTACK_equiv_false:
  ATTACK_CTXT_pkg ∘ CTXT false ≈₀ ATTACK false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  simplify_linking.
  ssprove_code_simpl.
  ssprove_swap_lhs 0.
  ssprove_swap_rhs 0.
  ssprove_sync_eq=> sn.
  rewrite (@code_link_map_loop _ 'word _ (unzip2 m) tt _) /=.
  simplify_linking.
  by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the stretched PRG, i.e. the chance by
  which an adversary can distinguish the PRG from truly random numbers.
  Negligible by assumption.
*)
Definition prg_epsilon := Advantage GEN_STRETCH.

(**
  The advantage an adversary can gain over the CPA-secure encryption, i.e. the
  chance by which an adversary can distinguish a ciphertext of a known message
  from a random ciphertext.
  Negligible by assumption.
*)
Definition cpa_epsilon := Advantage CTXT.

Lemma forward_secrecy_based_on_prg LA A:
  ValidPackage LA
    [interface #val #[attack]: 'seq 'word → ('seq 'word) × 'word ]
    A_export A ->
  Advantage ATTACK A <=
  prg_epsilon (A ∘ ATTACK_GEN_pkg) +
  cpa_epsilon (A ∘ ATTACK_CTXT_pkg).
Proof.
  move=> vA.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (ATTACK true) [::
    ATTACK_GEN_pkg ∘ GEN_STRETCH true ;
    ATTACK_GEN_pkg ∘ GEN_STRETCH false ;
    pack ATTACK_HYB_pkg ;
    ATTACK_CTXT_pkg ∘ CTXT true ;
    ATTACK_CTXT_pkg ∘ CTXT false
  ] (ATTACK false) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite ATTACK_equiv_true ?fdisjointUr ?fdisjoints0 // GRing.add0r.
  rewrite ATTACK_HYB_equiv_1 ?fdisjointUr ?fdisjoints0 // GRing.addr0.
  rewrite ATTACK_HYB_equiv_2 ?fdisjointUr ?fdisjoints0 // GRing.addr0.
  rewrite ATTACK_equiv_false ?fdisjointUr ?fdisjoints0 // GRing.addr0.
  rewrite /prg_epsilon /cpa_epsilon !Advantage_E -!Advantage_link.
  by rewrite (Advantage_sym (GEN_STRETCH true)) (Advantage_sym (CTXT true)).
Qed.

End SymmRatchet_example.
