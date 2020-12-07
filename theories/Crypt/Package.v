From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings Rules
  StateTransfThetaDens StateTransformingLaxMorph FreeProbProg.
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.


From Crypt Require Import pkg_preamble.
From Crypt Require Import pkg_chUniverse.
From Crypt Require Import pkg_core_definition.
From Crypt Require Import pkg_laws.
From Crypt Require Import pkg_rhl.



Module PackageTheory (π : ProbRulesParam).

  Export π.
  Module PKG_TH := (CorePackageTheory π).
  Import PKG_TH.
  Module PKG_LAWS := (PackageLaws π).
  Import PKG_LAWS.
  Module PKG_RHL := (PackageRHL π).
  Import PKG_RHL.


End PackageTheory.
