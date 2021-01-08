(** Tactics to help write packages

  In this module we define handy tactics to deal with obligations generated
  by packages operations and packages in general.

  - in_fset_auto
    This tactic should solve goals of the form
    x \in S
    where S is a concrete finite set that contains x.

  - inseq_try
    This tactic should solve goals of the form
    x \in S
    where S is a sequence that contains x syntactically.

  - inset_try
    Similar to inseq_try but for fset.
    It is slightly stronger than in_fset_auto in that it also works in case
    the mem predicate doesn't compute in itself.

  - package_obtac
    This tactic can be used as an obligation tactic for Program or Equations
    mode.
    It can be set with
    Obligation Tactic := package_obtac.

  - program fold
    This tactic can be used to fold raw programs together with their validity
    proof to program syntax.

**)

From mathcomp Require Import ssreflect ssrbool eqtype seq.
From extructures Require Import ord fset.
From Crypt Require Export pkg_core_definition pkg_composition pkg_notation
  RulesStateProb.

Require Equations.Prop.DepElim.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Ltac in_fset_auto :=
  rewrite extructures.fset.in_fset ; reflexivity.

(* Succeeds for x \in S if S contains syntactically x, S seq *)
Ltac inseq_try :=
  apply/orP ; first [
    left ; apply/eqP ; reflexivity
  | right ; inseq_try
  ].

Ltac inset_try :=
  rewrite in_fset ; inseq_try.

Ltac package_obtac :=
  (* Or try (Tactics.program_simpl; fail); simpl ? *)
  Tactics.program_simplify ;
  CoreTactics.equations_simpl ;
  try Tactics.program_solve_wf ;
  try in_fset_auto ;
  try inset_try.

Module PackageTactics (π : RulesParam).

  Include (PackageNotation π).
  Include (DerivedRules π).

  (* Ltac program_fold_one :=
    lazymatch goal with
    | context [ exist _ (_ret x) h ] =>
      rewrite fold_ret
    | context [ exist _ (_opr o x k) h ] =>
      rewrite fold_opr *)

  Ltac program_fold :=
    rewrite ?fold_ret ?fold_opr ?fold_getr ?fold_putr ?fold_sampler.

  Tactic Notation "program" "fold" :=
    program_fold.

End PackageTactics.