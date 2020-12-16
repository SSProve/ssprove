(* Definition of tactics to help write packages *)

From Coq Require Import Utf8.
From mathcomp Require Import choice seq ssreflect.
From extructures Require Import ord fset fmap.

Require Equations.Prop.DepElim.
From Equations Require Import Equations.

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

(* Obligation Tactic := package_obtac. *)