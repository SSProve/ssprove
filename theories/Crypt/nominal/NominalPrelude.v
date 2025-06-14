Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.



Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.

From extructures Require Import ffun fperm.

From SSProve.Crypt Require Import
  Nominal Fresh Pr Share Sep.

Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.



Create HintDb disj_db.
#[export] Hint Resolve disj_equi2 disj_equi2' : disj_db.
#[export] Hint Resolve equi_share_link equi_share_par : disj_db.
#[export] Hint Resolve disj_ID_r disj_ID_l : disj_db.

Ltac ssprove_separate_solve :=
  auto with disj_db nocore.

Ltac ssprove_separate_once :=
  (rewrite -> share_link_sep_link by ssprove_separate_solve)
  || (rewrite -> share_par_sep_par by ssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac ssprove_separate :=
  repeat ssprove_separate_once.


Create HintDb ssprove_into_share.
Hint Rewrite <- @share_link_sep_link : ssprove_into_share.
Hint Rewrite <- @share_par_sep_par : ssprove_into_share.

Ltac ssprove_share_once :=
  ((rewrite_strat innermost hints ssprove_into_share)
    ; try ssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac ssprove_share :=
  repeat ssprove_share_once.
