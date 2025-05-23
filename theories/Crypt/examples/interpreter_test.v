Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Crypt Require Import Prelude choice_type Package.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Test.
  Import PackageNotation.
  #[local] Open Scope package_scope.

  #[local] Definition loc : Location :=  (1, 'nat)%N.
  #[local] Definition locs : Locations := [fmap loc].

  #[local] Definition test_prog_sub (x : nat):
    code emptym [interface] 'nat :=
    {code
       k ← sample uniform 20 ;;
       let y := (x + k)%N in
       ret y
    }.

  #[local] #[program] Definition test_prog (x : nat):
    code locs [interface] 'nat :=
    {code
       k ← test_prog_sub x ;;
       #put loc := k ;;
       k' ← get loc ;;
       ret k'
    }.
  Next Obligation.
    ssprove_valid.
  Defined.

  Goal (nat_ch (ch_nat 'unit tt) 'unit) = Some tt.
    vm_compute.
    reflexivity.
  Qed.
  Goal (Run sampler (test_prog 2) 54) = Some 16.
    simpl. vm_compute.
    reflexivity.
  Qed.

  Lemma interpretation_test1:
    ∀ seed input,
      (Run sampler (test_prog input) seed) = Some (input + seed %% 20)%N.
  Proof.
    done.
  Qed.

  #[local] Definition E :=
    [interface
       #val #[ 0 ] : 'nat → 'nat
    ].

  #[local] Definition test_pack:
    package [interface] E :=
    [package locs ;
       #def #[ 0 ] (x : 'nat) : 'nat
       {
         k ← sample uniform 20 ;;
         let y := (x + k)%N in
         #put loc := y ;;
         y' ← get loc ;;
         ret y'
       }
    ].

End Test.
