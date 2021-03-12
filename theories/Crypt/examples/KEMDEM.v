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

#[local] Open Scope ring_scope.

Inductive probEmpty : Type → Type := .

Module genparam <: RulesParam.

  Definition probE : Type → Type := probEmpty.

  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes → choiceType.
  Proof.
    intro v. contradiction.
  Defined.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intros T v. inversion v.
  Defined.

End genparam.

(* TODO *)
Variant Index := i_todo.

Module Uparam <: UniformParameters.

  Definition Index : Type := Index.

  Definition i0 : Index := i_todo.

  Definition fin_family : Index → finType :=
    λ i,
      match i with
      | i_todo => [finType of 'Z_2]
      end.

  Definition F_w0 : ∀ i, fin_family i.
  Proof.
    unfold fin_family.
    case. exact 0.
  Defined.

End Uparam.

Module Rules := DerivedRulesUniform genparam Uparam.