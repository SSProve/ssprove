(******************************************************************************)
(*                Discrete Logarithm Problem (DL)                             *)
(*                                                                            *)
(*  For more details, see the ./README.md.                                    *)
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

#[local] Open Scope package_scope.
#[local] Open Scope group_scope.

Import GroupScope GRing.Theory.

Module Type GroupParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].

End GroupParam.

Module Type DLParams.
  Parameter Space : finType.
End DLParams.

Module DL (DLP : DLParams) (GP : GroupParam).

  Import DLP.
  Import GP.

  Definition set_up := 0%N.
  Definition guess := 1%N.

  Definition GroupSpace : finType := gT.
  Definition chGroup : choice_type := 'fin #|GroupSpace|.

  Definition i_space := #|Space|.
  Definition chElem : choice_type := 'fin #|Space|.

  Notation " 'group " := (chGroup) (in custom pack_type at level 2).
  Notation " 'elem " := (chElem) (in custom pack_type at level 2).

  Definition secret_loc := mkloc 33 (None : option chElem).

  Definition DL_loc : Locations := [ fmap secret_loc ].

  Definition DL_E := [
        interface
            #val #[ set_up ] : 'unit → 'group ;
            #val #[ guess ] : 'elem → 'bool
  ].

  Definition DL_real :
    package [interface] DL_E :=
      [package DL_loc ;
        #def #[ set_up ] (_ : 'unit) : 'group
        {
            a ← sample uniform i_space ;;
            #put secret_loc := Some a ;;
            ret (fto (g ^+ a))
        } ;

        #def #[ guess ] (y: 'elem) : 'bool
        {
            o_x ← get secret_loc ;;
            match o_x with
            | Some x => ret (x == y)
            | _ => ret false
            end
        }
      ].

  Definition DL_ideal :
    package [interface] DL_E :=
      [package DL_loc;
        #def #[ set_up ] (_ : 'unit) : 'group
        {
            a ← sample uniform i_space ;;
            #put secret_loc := Some a ;;
            ret (fto (g ^+ a))
        } ;
        #def #[ guess ] (y: 'elem) : 'bool
        {
            ret false
        }
      ].

  Definition DL b : game DL_E := if b then DL_real else DL_ideal.

  Definition ϵ_DL := Advantage DL.

End DL.
