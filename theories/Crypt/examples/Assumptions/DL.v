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

Module Type DLParams.
  Parameter Space : finType.
  Parameter Space_pos : Positive #|Space|.
End DLParams.

Module DL (DLP : DLParams) (GP : GroupParam).

  Import DLP.
  Import GP.

  Definition set_up := 0%N.
  Definition guess := 1%N.

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

  Definition secret_loc : Location := (33, chElem).

  Definition DL_loc : Locations := [ fmap secret_loc ].

  Definition DL_E := [
        interface 
            #val #[ set_up ] : 'unit → 'group ;
            #val #[ guess ] : 'group → 'bool
  ].

  Definition DL_real :
    package [interface] DL_E :=
      [package DL_loc ;
        #def #[ set_up ] (_ : 'unit) : 'group
        {
            a ← sample uniform i_space ;;
            #put secret_loc := a ;;
            ret (fto (g^+ a))
        } ;

        #def #[ guess ] (y: 'group) : 'bool
        {
            x ← get secret_loc ;;
            ret(fto (g^+x) == y)
        }
      ].

  Definition DL_ideal :
    package [interface] DL_E :=
      [package DL_loc;
        #def #[ set_up ] (_ : 'unit) : 'group
        {
            a ← sample uniform i_space ;;
            #put secret_loc := a ;;
            ret (fto (g^+ a))
        } ;
        #def #[ guess ] (y: 'group) : 'bool
        {
            ret(false)
        }
      ].

  Definition DL b : game DL_E := if b then DL_real else DL_ideal.

  Definition ϵ_DL := Advantage DL.

End DL.
