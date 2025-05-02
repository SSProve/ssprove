From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.

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
  Parameter Space_pos : Positive #|Space|.
End DDHParams.

Module DDH (DDHP : DDHParams) (GP : GroupParam).

  Import DDHP.
  Import GP.

  Definition SAMPLE := 0%N.

  #[local] Existing Instance Space_pos.

  Definition GroupSpace : finType := gT.
  #[local] Instance GroupSpace_pos : Positive #|GroupSpace|.
  Proof.
    apply /card_gt0P; by exists g.
  (* Needs to be transparent to unify with local positivity proof? *)
  Defined.

  Definition chGroup : choice_type := 'fin #|GroupSpace|.

  Definition i_space := #|Space|.
  Definition chElem : choice_type := 'fin #|Space|.

  Notation " 'group " := (chGroup) (in custom pack_type at level 2).

  Definition secret_loc1 : Location := (33, chElem).
  Definition secret_loc2 : Location := (34, chElem).
  Definition secret_loc3 : Location := (35, chElem).

  Definition DDH_locs :=
    [fmap secret_loc1 ; secret_loc2 ; secret_loc3].

  Definition DDH_real :
    package DDH_locs [interface]
      [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ] :=
      [package
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          #put secret_loc1 := a ;;
          #put secret_loc2 := b ;;
          ret (fto (g^+ a), (fto (g^+ b), fto (g^+(a * b))))
        }
      ].

  Definition DDH_E := [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ].

  Definition DDH_ideal :
    package DDH_locs [interface] DDH_E :=
      [package
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          c ← sample uniform i_space ;;
          #put secret_loc1 := a ;;
          #put secret_loc2 := b ;;
          #put secret_loc3 := c ;;
          ret (fto (g^+a), (fto (g^+b), fto (g^+c)))
        }
      ].

  Definition DDH :
    loc_GamePair [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ] :=
    λ b,
      if b then {locpackage DDH_real } else {locpackage DDH_ideal }.

  Definition ϵ_DDH := Advantage DDH.

End DDH.
