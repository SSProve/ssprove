(** Tactics to help write packages

  In this module we define handy tactics to deal with obligations generated
  by packages operations.

  - in_fset_auto
    This tactic should solve goals of the form
    x \in S
    where S is a concrete finite set that contains x.

  - package_obtac
    This tactic can be used as an obligation tactic for Program or Equations
    mode.
    It can be set with
    Obligation Tactic := package_obtac.

**)

From mathcomp Require Import ssreflect.
From extructures Require Import ord fset.

Require Equations.Prop.DepElim.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Ltac in_fset_auto :=
  rewrite extructures.fset.in_fset ; reflexivity.

Ltac package_obtac :=
  (* Or try (Tactics.program_simpl; fail); simpl ? *)
  Tactics.program_simplify ;
  CoreTactics.equations_simpl ;
  try Tactics.program_solve_wf ;
  try in_fset_auto.