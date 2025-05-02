(*********************************************************************)
(* This file is distributed under the terms of the MIT License       *)
(*                                                                   *)
(* Copyright (C) 2016 IMDEA Software Institute                       *)
(* Copyright (C) 2016 Inria                                          *)
(* Copyright (C) 2017 École Polytechnique                            *)
(* Copyright (C) 2017 Universidade do Minho                          *)
(* Copyright (C) 2017 Universidade do Porto                          *)
(* Copyright (C) 2021 Max Planck Institute for Security and Privacy  *)
(* Copyright (C) Jasmin contributors (see AUTHORS)                   *)
(*********************************************************************)

(* ** Machine word *)

(* ** Imports and settings *)

From HB Require Import structures.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ word.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Crypt Require Import jasmin_util.
Require Import (* strings *) ZArith (* utils *).
(* Import Utf8. *)
(* Import word_ssrZ. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------- *)
Variant wsize :=
  | U8
  | U16
  | U32
  | U64
  | U128
  | U256.

(* Size in bits of the elements of a vector. *)
Variant velem := VE8 | VE16 | VE32 | VE64.

Coercion wsize_of_velem (ve: velem) : wsize :=
  match ve with
  | VE8 => U8
  | VE16 => U16
  | VE32 => U32
  | VE64 => U64
  end.

(* Size in bits of the elements of a pack. *)
Variant pelem :=
| PE1 | PE2 | PE4 | PE8 | PE16 | PE32 | PE64 | PE128.

Variant signedness :=
  | Signed
  | Unsigned.

(* -------------------------------------------------------------------- *)
Scheme Equality for wsize.

Lemma wsize_axiom : Equality.axiom wsize_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_wsize_dec_bl internal_wsize_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build wsize wsize_axiom.

Definition wsizes :=
  [:: U8 ; U16 ; U32 ; U64 ; U128 ; U256 ].

Lemma wsize_fin_axiom : Finite.axiom wsizes.
Proof. by case. Qed.

(* ** Comparison
 * -------------------------------------------------------------------- *)
Definition wsize_cmp s s' :=
  match s, s' with
  | U8, U8 => Eq
  | U8, (U16 | U32 | U64 | U128 | U256)  => Lt
  | U16, U8 => Gt
  | U16, U16 => Eq
  | U16, (U32 | U64 | U128 | U256) => Lt
  | U32, (U8 | U16) => Gt
  | U32, U32 => Eq
  | U32, (U64 | U128 | U256) => Lt
  | U64, (U8 | U16 | U32) => Gt
  | U64, U64 => Eq
  | U64, ( U128 | U256) => Lt
  | U128, (U8 | U16 | U32 | U64) => Gt
  | U128, U128 => Eq
  | U128, U256 => Lt
  | U256, (U8 | U16 | U32 | U64 | U128) => Gt
  | U256, U256 => Eq
  end.

#[export]
Instance wsizeO : Cmp wsize_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> [] [] [] //= ? [].
  by move=> [] [].
Qed.

Lemma wsize_le_U8 s: (U8 <= s)%CMP.
Proof. by case: s. Qed.

Lemma wsize_ge_U256 s: (s <= U256)%CMP.
Proof. by case s. Qed.

#[global]Hint Resolve wsize_le_U8 wsize_ge_U256: core.

(* -------------------------------------------------------------------- *)
Definition check_size_8_64 sz := assert (sz ≤ U64)%CMP ErrType.
Definition check_size_8_32 sz := assert (sz ≤ U32)%CMP ErrType.
Definition check_size_16_32 sz := assert ((U16 ≤ sz) && (sz ≤ U32))%CMP ErrType.
Definition check_size_16_64 sz := assert ((U16 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_32_64 sz := assert ((U32 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_128_256 sz := assert ((U128 ≤ sz) && (sz ≤ U256))%CMP ErrType.
