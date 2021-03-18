(** Useful instance of packages with uniform distributions and assert

  This module provides an instance to the functor for use in the examples.
  This is a temporary measure pending the removal of functors in packages.

  This also introduces useful lemmata and rules as well as syntax for uniform
  distributions and assert.

  When the large-scale refactoring is concluded, this file should go away,
  its contents distributed, mainly in pkg_rhl.

*)

From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.
From Crypt Require Import Prelude Package RulesStateProb SubDistr
  UniformStateProb.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.
Set Keyed Unification.

(* Empty instance for probE *)
Inductive probEmpty : Type → Type :=.

Module genparam <: RulesParam.

  Definition probE : Type → Type := probEmpty.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intros T v. inversion v.
  Defined.

End genparam.

Module Rules := DerivedRulesUniform genparam.
Export Rules.

Module Package := Package_Make myparamU.
Export Package.