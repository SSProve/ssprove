(** KEM-DEM example *)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl pkg_notation Package Prelude pkg_notation.
Set Warnings "-custom-entry-overriden".
From Crypt Require Import package_instance.
Set Warnings "custom-entry-overriden".

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Import PackageNotation.

#[local] Open Scope ring_scope.

Definition i_key (l : nat) := l.

Definition GEN := 0%N.
Definition SET := 1%N.
Definition GET := 2%N.

Definition key n `{Positive n} : Location := ('fin n ; 0%N).

Definition KEY n `{Positive n} :
  package
    (fset [:: key n ])
    [interface]
    [interface
      val #[ GEN ] : 'unit → 'fin n ;
      val #[ SET ] : ('fin n) → 'unit ;
      val #[ GET ] : 'unit → 'fin n
    ] :=
  [package
    def #[ GEN ] (_ : 'unit) : ('fin n) {
      (* assert k = ⊥ ;; *)
      k ← sample U (i_key n) ;;
      ret k
    } ;
    def #[ SET ] (k : ('fin n)) : 'unit {
      (* assert k = ⊥ ;; *)
      put (key n) := k ;;
      ret Datatypes.tt
    } ;
    def #[ GET ] (_ : 'unit) : ('fin n) {
      (* assert k ≠ ⊥ ;; *)
      k ← get (key n) ;;
      ret k
    }
  ].