(*
  OTP example with abstract xor
*)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect reals.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.

Section OTP_example.

  Context (n : nat).
  Context (n_pos : Positive n).
  Definition M := 'fin n.
  Definition K := M.
  Context (xor : M -> M -> M).
  Notation "m ⊕ k" := (xor m k) (at level 70).
  Context (bij_xor : forall m, bijective (xor m)).

  Definition Enc {L : {fset Location}} (m : M) (k : K) :
    code L [interface] M :=
    {code
       ret (m ⊕ k)
    }.

  Definition KeyGen {L : {fset Location}} (u : unit) :
    code L [interface] M :=
    {code
       k <$ uniform n ;;
       ret k
    }.
  Definition enc : nat := 0.

  Definition OT_IND_CPA_location : {fset Location} := fset0.

  Definition OT_IND_CPA_real :
    package
      OT_IND_CPA_location
      [interface]
      [interface #val #[enc] : {M} → {M} ]
    :=
    [package
       #def #[enc] (msg : {M}) : {M} {
            k ← KeyGen tt ;;
            c ← (Enc msg k) ;;
            ret c
       }
    ].


  Definition OT_IND_CPA_ideal :
    package
      OT_IND_CPA_location
      [interface]
      [interface #val #[enc] : {M} → {M} ]
    :=
    [package
       #def #[enc] (msg : {M}) : {M} {
            k ← KeyGen tt ;;
            m' <$ uniform n ;;
            c ← (Enc m' k) ;;
            ret c
       }
    ].

  Definition OT_IND_CPA_ideal_alt :
    package
      OT_IND_CPA_location
      [interface]
      [interface #val #[enc] : {M} → {M} ]
    :=
    [package
       #def #[enc] (msg : {M}) : {M} {
            c <$ uniform n ;;
            ret c
       }
    ].

  Definition OT_IND_CPA : loc_GamePair [interface #val #[enc] : {M} → {M} ] :=
    λ b, if b
        then {locpackage OT_IND_CPA_real }
        else {locpackage OT_IND_CPA_ideal_alt }.

  Lemma IND_CPA_ideal_real :
    OT_IND_CPA false ≈₀ OT_IND_CPA true.
  Proof.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    apply rsymmetry.
    apply r_uniform_bij with (1 := (bij_xor m)) ; intro key.
    now apply r_ret.
  Qed.

End OTP_example.
