Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import fperm.
From SSProve.Crypt Require Import Nominal.

Definition equality_after_nominal (left right : nat) : bool := left == right.

From SSProve.Crypt Require Import NominalPrelude.

Definition equality_after_prelude (left right : nat) : bool := left == right.

From Stdlib Require Import Setoids.Setoid Classes.Morphisms.

Section AlphaRewriting.
Context {carrier : actionType} (permutation : {fperm atom}).
Variables left right : carrier.

Example alpha_rename :
  alpha left right -> alpha (rename permutation left) (rename permutation right).
Proof.
  intros equivalent.
  setoid_rewrite equivalent.
  reflexivity.
Qed.
End AlphaRewriting.
