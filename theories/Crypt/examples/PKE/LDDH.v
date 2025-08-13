Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  fingroup reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve Require Import NominalPrelude.
From SSProve.Crypt.examples.PKE Require Import CyclicGroup.

Import PackageNotation.
#[local] Open Scope package_scope.

Import Num.Def Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import GroupScope.

#[local] Open Scope F_scope.

Section LDDH.

  Context (G : CyclicGroup).

  Definition GETA := 50%N.
  Definition GETBC := 51%N.

  (* Lazy DDH *)

  Definition I_LDDH :=
    [interface
      [ GETA  ] : { 'unit ~> 'el G } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G }
    ].

  Definition mga_loc : Location := (3, 'option 'el G).

  Definition LDDH bit :
    game I_LDDH :=
    [package [fmap mga_loc ] ;
      [ GETA ] 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc := Some ('g ^ a) ;;
        ret ('g ^ a)
      } ;
      [ GETBC ] 'tt {
        ga ← getSome mga_loc ;;
        #put mga_loc := None ;;
        b ← sample uniform #|exp G| ;;
        if bit then
          ret ('g ^ b, ga ^ b)
        else
          c ← sample uniform #|exp G| ;;
          ret ('g ^ b, 'g ^ c)
      }
    ].

End LDDH.
