(* ** Machine word *)

(* ** Imports and settings *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ word.
From Crypt Require Import jasmin_util jasmin_wsize.
Require Import (* strings *) ZArith (* utils *).
(* Import Utf8. *)
(* Import word_ssrZ. *)
Export jasmin_wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Ltac elim_div :=
   unfold Z.div, Z.modulo;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
     end; unfold Remainder.

Definition wsize_log2 sz : nat :=
  match sz with
  | U8 => 0
  | U16 => 1
  | U32 => 2
  | U64 => 3
  | U128 => 4
  | U256 => 5
  end.

Definition wbase (s: wsize) : Z :=
  modulus (wsize_size_minus_1 s).+1.

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

Lemma wunsigned_range sz (p: word sz) :
  0 <= wunsigned p < wbase sz.
Proof. by have /iswordZP := isword_word p. Qed.
