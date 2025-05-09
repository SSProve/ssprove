(**
  This formalises Claim 10.4 from "The Joy of Cryptography" (p. 188).
  Most of it is fairly straight forward, the longest part being
  [TAG_GUESS_equiv_3].

  It would also be nice to formalise Claim 10.3 (p. 186), but its argument
  depends on the adversary only having polynomial time, and how to formulate
  that is unclear.

  The final statement ([security_based_on_prf]) is similar to that of PRF.v,
  stating that the advantage is bounded by a [prf_epsilon] and a
  [statistical_gap]. It would be particularly nice to simply state that it is
  negligible in [n].
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

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Section PRFMAC_example.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := chFin (mkpos Word_N).

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

#[local] Open Scope package_scope.

Definition k_loc: Location := (0, 'option 'word).
Definition T_loc: Location := (1, chMap 'word 'word).
Definition S_loc: Location := (2, 'set ('word × 'word)).
Definition lookup: nat := 3.
Definition encrypt: nat := 4.
Definition gettag: nat := 5.
Definition checktag: nat := 6.
Definition guess: nat := 7.

Context (PRF: Word -> Word -> Word).

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
  eapply kgen_valid ;
  solve [ fmap_solve ] 
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

Definition GUESS_locs := [fmap T_loc].

Definition GUESS_pkg_tt:
  package
    [interface]
    [interface
      #val #[lookup]: 'word → 'word ;
      #val #[guess]: 'word × 'word → 'bool ] :=
  [package GUESS_locs ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          t <$ uniform Word_N ;;
          #put T_loc := setm T m t ;;
          ret t
      | Some t => ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'word): 'bool {
      T ← get T_loc ;;
      r ← match getm T m with
      | None =>
          r <$ uniform Word_N ;;
          #put T_loc := setm T m r ;;
          ret r
      | Some r => ret r
      end ;;
      ret (t == r)
    }
  ].

Definition GUESS_pkg_ff:
  package
    [interface]
    [interface
      #val #[lookup]: 'word → 'word ;
      #val #[guess]: 'word × 'word → 'bool ] :=
  [package GUESS_locs ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          t <$ uniform Word_N ;;
          #put T_loc := setm T m t ;;
          ret t
      | Some t => ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'word): 'bool {
      T ← get T_loc ;;
      ret (Some t == getm T m)
    }
  ].

Definition GUESS b := if b then GUESS_pkg_tt else GUESS_pkg_ff.

Definition TAG_locs_tt := [fmap k_loc].
Definition TAG_locs_ff := [fmap k_loc; S_loc].

Definition TAG_pkg_tt:
  package
    [interface]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package TAG_locs_tt ;
    #def #[gettag] (m: 'word): 'word {
      k ← kgen ;;
      ret (PRF k m)
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      k ← kgen ;;
      ret (t == PRF k m)
    }
  ].

Definition TAG_pkg_ff:
  package
    [interface]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package TAG_locs_ff ;
    #def #[gettag] (m: 'word): 'word {
      S ← get S_loc ;;
      k ← kgen ;;
      let t := PRF k m in
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      S ← get S_loc ;;
      ret ((m, t) \in domm S)
    }
  ].

Definition TAG b := if b then TAG_pkg_tt else TAG_pkg_ff.

Definition TAG_EVAL_locs_ff := [fmap S_loc].

Definition TAG_EVAL_pkg_tt:
  package
    [interface #val #[lookup]: 'word → 'word ]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package emptym ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      t ← lookup m ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      r ← lookup m ;;
      ret (t == r)
    }
  ].

Definition TAG_EVAL_pkg_ff:
  package
    [interface #val #[lookup]: 'word → 'word]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package TAG_EVAL_locs_ff ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      S ← get S_loc ;;
      t ← lookup m ;;
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      S ← get S_loc ;;
      ret ((m, t) \in domm S)
    }
  ].

Definition TAG_GUESS_locs := [fmap S_loc ].

Definition TAG_GUESS_pkg:
  package
    [interface
      #val #[lookup]: 'word → 'word ;
      #val #[guess]: 'word × 'word → 'bool ]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package TAG_GUESS_locs ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      S ← get S_loc ;;
      t ← lookup m ;;
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      #import {sig #[guess]: 'word × 'word → 'bool } as guess ;;
      r ← guess (m, t) ;;
      ret r
    }
  ].

Lemma TAG_equiv_true:
  TAG true ≈₀ TAG_EVAL_pkg_tt ∘ EVAL true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: case: m => [m t].
  all: simplify_linking.
  all: simplify_linking.
  all: ssprove_sync_eq.
  all: case => [k|].
  all: by apply: rreflexivity_rule.
Qed.

Lemma TAG_EVAL_equiv_true:
  TAG_EVAL_pkg_tt ∘ EVAL false ≈₀ TAG_GUESS_pkg ∘ GUESS true.
Proof.
  apply eq_rel_perf_ind_ignore with ([fmap S_loc]).
  1: fmap_solve.
  simplify_eq_rel m.
  2: case: m => [m t].
  all: simplify_linking.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  2: {
    apply: (@r_reflexivity_alt _ [fmap T_loc]) => [l H|l H' H].
    1,2: fmap_invert H; ssprove_invariant.
  }
  1: apply: r_get_remember_rhs => S.
  ssprove_sync=> T.
  case (getm T _) => [t|].
  2: ssprove_sync=> t.
  2: ssprove_sync.
  all: apply: r_put_rhs.
  all: ssprove_restore_mem;
    last by apply: r_ret.
  all: by ssprove_invariant.
Qed.

(**
  The first function ([gettag]) is exactly the same in both packages.
  It turns out, however, to be pretty complicated since we need to prove the
  invariant holds.
*)
Lemma TAG_EVAL_equiv_false:
  TAG_GUESS_pkg ∘ GUESS false ≈₀ TAG_EVAL_pkg_ff ∘ EVAL false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs T_loc S_loc
      (fun T S => forall m t,
        ((m, t) \in domm S) = (Some t == getm T m))
  ).
  1: {
    ssprove_invariant=> /=.
    move=> m t.
    by rewrite domm0 in_fset0 get_empty_heap emptymE.
  }
  simplify_eq_rel m.
  2: case: m => [m t].
  all: simplify_linking.
  all: simplify_linking.
  - apply: r_get_vs_get_remember => S.
    apply: r_get_vs_get_remember => T.
    destruct (getm T m) as [t|] eqn:Heqt.
    all: rewrite Heqt /=.
    + apply: r_put_vs_put.
      ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> s0 s1 [[[[Hinv _] H1] _] H2] m' t'.
      rewrite get_set_heap_eq get_set_heap_neq // domm_set in_fsetU in_fset1.
      case: (eq_dec (m', t') (m, t)) => Heq.
      * case: Heq => [-> ->].
        by rewrite H2 Heqt /= !eq_refl.
      * move /eqP /negPf in Heq.
        by rewrite Heq -H1 Hinv.
    + ssprove_sync=> k.
      apply: (r_rem_couple_rhs T_loc S_loc) => Hinv.
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> m' k'.
      rewrite domm_set in_fsetU in_fset1 setmE.
      case: (eq_dec (m', k') (m, k)) => Heq.
      1: {
        case: Heq => [-> ->].
        by rewrite !eq_refl /= eq_refl.
      }
      move /eqP /negPf in Heq.
      rewrite Heq /=.
      rewrite xpair_eqE in Heq.
      case: (eq_dec m' m) => Heqm.
      * rewrite Heqm eq_refl /= in Heq*.
        by rewrite Heq Hinv Heqt.
      * move /eqP /negPf in Heqm.
        by rewrite Heqm Hinv.
  - ssprove_code_simpl.
    ssprove_code_simpl_more.
    apply: r_get_remember_lhs => T.
    apply: r_get_remember_rhs => S.
    apply: (r_rem_couple_rhs T_loc S_loc) => [|Hinv].
    1: by apply: (Remembers_rhs_from_tracked_lhs _).
    rewrite Hinv.
    ssprove_forget_all.
    by apply: r_ret.
Qed.

Lemma TAG_equiv_false:
  TAG_EVAL_pkg_ff ∘ EVAL true ≈₀ TAG false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: case: m => [m t].
  all: simplify_linking.
  all: ssprove_sync_eq=> S.
  1: ssprove_sync_eq.
  1: case => [k|].
  all: by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRF, i.e. the chance by
  which an adversary can distinguish the PRF from a truly random function.
  Negligible by assumption.
*)
Definition prf_epsilon := Advantage EVAL.

(**
  The advantage an adversary can gain in the [GUESS] game.
  This is negligible, but not yet provable in SSProve.
*)
Definition statistical_gap :=
  AdvantageE (TAG_GUESS_pkg ∘ GUESS true) (TAG_GUESS_pkg ∘ GUESS false).

Theorem security_based_on_prf LA A:
  ValidPackage LA
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ]
    A_export A ->
  fseparate LA EVAL_locs_tt ->
  fseparate LA EVAL_locs_ff ->
  fseparate LA GUESS_locs ->
  fseparate LA TAG_locs_tt ->
  fseparate LA TAG_locs_ff ->
  fseparate LA TAG_EVAL_locs_ff ->
  fseparate LA TAG_GUESS_locs ->
  Advantage TAG A <=
  prf_epsilon (A ∘ TAG_EVAL_pkg_tt) +
  statistical_gap A +
  prf_epsilon (A ∘ TAG_EVAL_pkg_ff).
Proof.
  move=> vA d1 d2 d3 d4 d5 d6 d7.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (TAG true) [::
    TAG_EVAL_pkg_tt ∘ EVAL true   ;
    TAG_EVAL_pkg_tt ∘ EVAL false  ;
    TAG_GUESS_pkg ∘ GUESS true  ;
    TAG_GUESS_pkg ∘ GUESS false ;
    TAG_EVAL_pkg_ff ∘ EVAL false  ;
    TAG_EVAL_pkg_ff ∘ EVAL true
  ] (TAG false) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite -> TAG_equiv_true by ssprove_valid.
  rewrite -> TAG_EVAL_equiv_true by ssprove_valid.
  rewrite -> TAG_EVAL_equiv_false by ssprove_valid.
  rewrite -> TAG_equiv_false by ssprove_valid.
  rewrite GRing.add0r 3!GRing.addr0 Advantage_sym.
  by rewrite /prf_epsilon /statistical_gap !Advantage_E !Advantage_link.
Qed.

End PRFMAC_example.
