(**
  This formalises Claim 6.3 from "The Joy of Cryptography" (p. 111).
  It shows how to work with variable length proofs.

  It is fairly complete. One thing that is missing is the final step, which is
  proving the last hybrid is perfectly indistinguishable from [GEN false],
  which, to my knowledge, cannot (yet) be formalised in SSProve, so instead we
  make it a hypothesis of the final statement [security_based_on_prf].
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

Section PRFGEN_example.

Variable (n: nat).

Context(Hpos: 0 < n).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := 'fin Word_N.

#[program]
Definition zero: Word := @Ordinal _ 0 _.
Next Obligation.
  by apply: PositiveExp2.
Qed.

#[program]
Definition one: Word := @Ordinal _ 1 _.
Next Obligation.
  rewrite /Word_N.
  move: Hpos.
  case: n => [// | n'] _.
  by rewrite expnS leq_pmulr // PositiveExp2.
Qed.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Context (PRF: Word -> Word -> Word).

Definition k_loc: Location := (0, 'option 'word).
Definition T_loc: Location := (1, chMap 'word 'word).
Definition count_loc: Location := (2, 'nat).
Definition query: nat := 3.
Definition lookup: nat := 4.

Definition EVAL_locs_tt := [fmap k_loc].
Definition EVAL_locs_ff := [fmap T_loc].

Definition kgen: raw_code 'word :=
  k_init ← get k_loc ;;
  match k_init with
  | None =>
      k <$ uniform Word_N ;;
      #put k_loc := Some k ;;
      ret k
  | Some k => ret k
  end.

Lemma kgen_valid {L I}:
  fhas L k_loc ->
  ValidCode L I kgen.
Proof.
  move=> H.
  apply: valid_getr => [// | [k|]].
  1: by apply: valid_ret.
  apply: valid_sampler => k.
  apply: valid_putr => //.
  by apply: valid_ret => //.
Qed.

Hint Extern 1 (ValidCode ?L ?I kgen) =>
  eapply kgen_valid ; [ fmap_solve ]
  : typeclass_instances ssprove_valid_db.

Definition EVAL_pkg_tt:
  package
    [interface]
    [interface #val #[lookup]: 'word → 'word ] :=
  [package EVAL_locs_tt ;
    #def #[lookup] (m: 'word): 'word {
      k ← kgen ;;
      ret (PRF k m)
    }
  ].

Definition EVAL_pkg_ff:
  package
    [interface]
    [interface #val #[lookup]: 'word → 'word ] :=
  [package EVAL_locs_ff ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          r <$ uniform Word_N ;;
          #put T_loc := setm T m r ;;
          ret r
      | Some r => ret r
      end
    }
  ].

Definition EVAL b := if b then EVAL_pkg_tt else EVAL_pkg_ff.

Definition GEN_pkg_tt:
  package [interface]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package emptym ;
    #def #[query] (_: 'unit): 'word × 'word {
      s <$ uniform Word_N ;;
      ret (PRF s zero, PRF s one)
    }
  ].

Definition GEN_pkg_ff:
  package [interface]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package emptym ;
    #def #[query] (_: 'unit): 'word × 'word {
      x <$ uniform Word_N ;;
      y <$ uniform Word_N ;;
      ret (x, y)
    }
  ].

Definition GEN b := if b then GEN_pkg_tt else GEN_pkg_ff.

Definition GEN_HYB_locs := [fmap count_loc ].

(**
  Defining the hybrid proofs is surprisingly simple: We can just take [i] as a
  parameter, and we can use it in the package.

  We diverge slightly from the book: The first hybrid is [GEN_HYB_pkg 0] rather
  than [GEN_HYB_pkg 1]. This makes the proofs simpler, since all choices of [i]
  are valid.
*)
Definition GEN_HYB_pkg i:
  package
    [interface]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package GEN_HYB_locs ;
    #def #[query] (_: 'unit): 'word × 'word {
      count ← get count_loc ;;
      #put count_loc := count.+1 ;;
      if count < i then
        x <$ uniform Word_N ;;
        y <$ uniform Word_N ;;
        ret (x, y)
      else
        s <$ uniform Word_N ;;
        ret (PRF s zero, PRF s one)
    }
  ].

Definition GEN_HYB_EVAL_pkg i:
  package
    [interface #val #[lookup]: 'word → 'word ]
    [interface #val #[query]: 'unit → 'word × 'word ] :=
  [package GEN_HYB_locs ;
    #def #[query] (_: 'unit): 'word × 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      count ← get count_loc ;;
      #put count_loc := count.+1 ;;
      if count < i then
        x <$ uniform Word_N ;;
        y <$ uniform Word_N ;;
        ret (x, y)
      else if count == i then
        x ← lookup zero ;;
        y ← lookup one ;;
        ret (x, y)
      else
        s <$ uniform Word_N ;;
        ret (PRF s zero, PRF s one)
    }
  ].

Lemma GEN_equiv_true:
  GEN true ≈₀ GEN_HYB_pkg 0.
Proof.
  apply eq_rel_perf_ind_ignore with [fmap count_loc].
  1: fmap_solve.
  simplify_eq_rel m.
  apply: r_get_remember_rhs => count.
  apply: r_put_rhs.
  ssprove_sync=> s.
  ssprove_restore_mem;
    last by apply: r_ret.
  by ssprove_invariant.
Qed.

(**
  The proofs are fairly simple. The main trick is to realise that [k] is
  uninitialised when [count <= i].
*)
Lemma GEN_GEN_HYB_equiv i:
  GEN_HYB_pkg i ≈₀ GEN_HYB_EVAL_pkg i ∘ EVAL true.
Proof.
  apply eq_rel_perf_ind with (
    (heap_ignore [fmap k_loc]) ⋊
    couple_rhs count_loc k_loc
      (fun count k => count <= i -> k = None)
    ).
  1: ssprove_invariant => //.
  simplify_eq_rel m.
  ssprove_code_simpl.
  apply: r_get_vs_get_remember => count.
  case: (eq_dec count i) => Heq.
  - rewrite Heq eq_refl ltnn /=.
    ssprove_swap_rhs 0.
    apply: r_get_remember_rhs => k.
    ssprove_rem_rel 0%N => Hinv.
    rewrite Hinv //.
    apply: r_put_vs_put.
    ssprove_sync=> s.
    eapply r_transR; [ apply: r_put_get |].
    apply: r_put_rhs.
    ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant.
    intros h h'. Check h'.
    by rewrite subSnn in h'.
  - move /eqP /negPf in Heq.
    rewrite Heq /=.
    destruct (count < i) eqn:Hlt.
    all: apply: r_put_vs_put.
    all: ssprove_sync=> x.
    1: ssprove_sync=> y.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    + rewrite eqnE 2!subn_eq0 ltnW //. auto.
    + rewrite eqnE 2!subn_eq0 Hlt //.
Qed.

(**
  This proof is very similar to the previous proof, except it is [T] that is
  uninitialised when [count <= i].
*)
Lemma GEN_GEN_HYB_EVAL_equiv i:
  GEN_HYB_EVAL_pkg i ∘ EVAL false ≈₀ GEN_HYB_pkg i.+1.
Proof.
  apply eq_rel_perf_ind with (
    (heap_ignore [fmap T_loc]) ⋊
    couple_lhs count_loc T_loc
      (fun count T => count <= i -> T = emptym)
    ).
  1: ssprove_invariant => //=; fmap_solve.
  simplify_eq_rel m.
  ssprove_code_simpl.
  apply: r_get_vs_get_remember => count.
  case: (eq_dec count i) => Heq.
  - rewrite Heq eq_refl ltnn ltnSn /=.
    ssprove_swap_lhs 0.
    apply: r_get_remember_lhs => T.
    ssprove_rem_rel 0%N => Hinv.
    rewrite Hinv //=.
    apply: r_put_vs_put.
    ssprove_sync=> x.
    eapply r_transL; [ apply: r_put_get |].
    apply: r_put_lhs.
    rewrite setmE /=.
    ssprove_sync=> y.
    apply: r_put_lhs.
    ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant.
    intros h h'. Check h'.
    by rewrite subSnn in h'.
  - move /eqP /negPf in Heq.
    rewrite Heq /=.
    destruct (count < i) eqn:Hlt.
    all: apply: r_put_vs_put.
    1: rewrite ltnW //.
    2: rewrite ltnS leq_eqVlt Heq Hlt /=.
    all: ssprove_sync => x.
    1: ssprove_sync => y.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    + rewrite eqnE 2!subn_eq0 ltnW //. auto.
    + rewrite eqnE 2!subn_eq0 Hlt //.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRF, i.e. the chance by
  which an adversary can distinguish the PRF from a truly random function.
  Negligible by assumption.
*)
Definition prf_epsilon := Advantage EVAL.

(**
  First we prove a bound on the hybrid packages. Since [q] can be any number
  the bound is a sum of [prf_epsilon], and the proof is by induction.
*)
Theorem hyb_security_based_on_prf LA A q:
  ValidPackage LA
    [interface #val #[query]: 'unit → 'word × 'word ]
    A_export A ->
  fseparate LA EVAL_locs_tt ->
  fseparate LA EVAL_locs_ff ->
  fseparate LA GEN_HYB_locs ->
  AdvantageE (GEN_HYB_pkg 0) (GEN_HYB_pkg q) A <=
  \sum_(i < q) prf_epsilon (A ∘ GEN_HYB_EVAL_pkg i).
Proof.
  move=> vA d1 d2 d3.
  elim: q => [|q IHq].
  1: by rewrite big_ord0 /AdvantageE GRing.subrr normr0.
  ssprove triangle (GEN_HYB_pkg 0) [::
    pack (GEN_HYB_pkg q) ;
    GEN_HYB_EVAL_pkg q ∘ EVAL true ;
    GEN_HYB_EVAL_pkg q ∘ EVAL false
  ] (GEN_HYB_pkg q.+1) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite -> GEN_GEN_HYB_equiv by ssprove_valid.
  rewrite -> GEN_GEN_HYB_EVAL_equiv by ssprove_valid.
  rewrite 2!GRing.addr0 big_ord_recr lerD //.
  by rewrite /prf_epsilon Advantage_E Advantage_link Advantage_sym.
Qed.

(**
  The final statement requires a proof that [A ∘ GEN_HYB_pkg q] and [A ∘ GEN false]
  are perfectly indistinguishable. The [q] for which this holds depends on the
  adversary (and might not exist for some adversaries). We sidestep this issue
  by making it a hypothesis.
*)
Theorem security_based_on_prf LA A q:
  ValidPackage LA
    [interface #val #[query]: 'unit → 'word × 'word ]
    A_export A ->
  fseparate LA EVAL_locs_tt ->
  fseparate LA EVAL_locs_ff ->
  fseparate LA GEN_HYB_locs ->
  AdvantageE (GEN_HYB_pkg q) (GEN false) A = 0 ->
  Advantage GEN A <= \sum_(i < q) prf_epsilon (A ∘ GEN_HYB_EVAL_pkg i).
Proof.
  move=> vA d1 d2 d3 GEN_equiv_false.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (GEN true) [::
    pack (GEN_HYB_pkg 0) ;
    pack (GEN_HYB_pkg q)
  ] (GEN false) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite -> GEN_equiv_true by ssprove_valid.
  rewrite -> GEN_equiv_false by ssprove_valid.
  rewrite GRing.add0r GRing.addr0 hyb_security_based_on_prf //.
Qed.

End PRFGEN_example.
