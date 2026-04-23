(******************************************************************************)
(*             Decisional Diffie-Hellman Assumption (DDH)                     *)
(*                                                                            *)
(*  Used in the formalization of El Gamal (ElGamal.v). For more details, see  *)
(*  the ./README.md.                                                          *)
(******************************************************************************)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.

From Stdlib Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.

Module Type GroupParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].

End GroupParam.

Module Type DDHParams.
  Parameter Space : finType.
End DDHParams.

Module DDH (DDHP : DDHParams) (GP : GroupParam).

  Import DDHP.
  Import GP.

  Definition SAMPLE := 0%N.

  Definition chGroup : choice_type := 'fin #|gT|.

  Definition i_space := #|Space|.
  Definition chElem : choice_type := 'fin #|Space|.

  Notation " 'group " := (chGroup) (in custom pack_type at level 2).

  Definition DDH_E := [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ].

  Definition DDH_real :
    package [interface] DDH_E :=
      [package emptym ;
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          ret (fto (g^+ a), (fto (g^+ b), fto (g^+(a * b))))
        }
      ].

  Definition DDH_ideal :
    package [interface] DDH_E :=
      [package emptym ;
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          c ← sample uniform i_space ;;
          ret (fto (g^+a), (fto (g^+b), fto (g^+c)))
        }
      ].

  Definition DDH b : game DDH_E := if b then DDH_real else DDH_ideal.

  Definition ϵ_DDH := Advantage DDH.

End DDH.
