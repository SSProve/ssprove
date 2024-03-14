(* ** Machine word *)

(* ** Imports and settings *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From Crypt Require Import jasmin_util.
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



(* -------------------------------------------------------------- *)
Definition nat7   : nat := 7.
Definition nat15  : nat := nat7.+4.+4.
Definition nat31  : nat := nat15.+4.+4.+4.+4.
Definition nat63  : nat := nat31.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat127 : nat := nat63.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat255 : nat := nat127.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.

Definition wsize_size_minus_1 (s: wsize) : nat :=
  match s with
  | U8   => nat7
  | U16  => nat15
  | U32  => nat31
  | U64  => nat63
  | U128 => nat127
  | U256 => nat255
  end.

Coercion nat_of_wsize (sz : wsize) :=
  (wsize_size_minus_1 sz).+1.

(* -------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac elim_div :=
   unfold Z.div, Z.modulo;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
     end; unfold Remainder.

Coercion nat_of_pelem (pe: pelem) : nat :=
  match pe with
  | PE1 => 1
  | PE2 => 2
  | PE4 => 4
  | PE8 => nat_of_wsize U8
  | PE16 => nat_of_wsize U16
  | PE32 => nat_of_wsize U32
  | PE64 => nat_of_wsize U64
  | PE128 => nat_of_wsize U128
  end.

Definition word sz : comRingType := (wsize_size_minus_1 sz).+1.-word.

Global Opaque word.

Definition wsize_log2 sz : nat :=
  match sz with
  | U8 => 0
  | U16 => 1
  | U32 => 2
  | U64 => 3
  | U128 => 4
  | U256 => 5
  end.

Local Open Scope Z_scope.

Definition wunsigned {s} (w: word s) : Z :=
  urepr w.

Definition wsigned {s} (w: word s) : Z :=
  srepr w.

Definition wrepr s (z: Z) : word s :=
  mkword (wsize_size_minus_1 s).+1 z.

Lemma word_ext n x y h h' :
  x = y ->
  @mkWord n x h = @mkWord n y h'.
Proof. by move => e; apply/val_eqP/eqP. Qed.

Lemma wunsigned_inj sz : injective (@wunsigned sz).
Proof. by move => x y /eqP /val_eqP. Qed.

Lemma wunsigned1 ws :
  @wunsigned ws 1 = 1%Z.
Proof. by case: ws. Qed.

Lemma wrepr_unsigned s (w: word s) : wrepr s (wunsigned w) = w.
Proof. by rewrite /wrepr /wunsigned ureprK. Qed.

Lemma wrepr_signed s (w: word s) : wrepr s (wsigned w) = w.
Proof. by rewrite /wrepr /wsigned sreprK. Qed.

Lemma wunsigned_repr s z :
  wunsigned (wrepr s z) = z mod modulus (wsize_size_minus_1 s).+1.
Proof. done. Qed.
