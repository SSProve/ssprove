(** Tactics to help prove things abouve packages

  TODO

**)

From mathcomp Require Import ssreflect ssrbool eqtype seq eqtype choice.
From extructures Require Import ord fset.
From Crypt Require Import Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb pkg_rhl.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

Require Equations.Prop.DepElim.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Module PackageUserUtil (π : RulesParam).

  Include (PackageRHL π).

End PackageUserUtil.