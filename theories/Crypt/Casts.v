Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrbool ssrnat choice fintype eqtype all_algebra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Coq Require Import ZArith.
From extructures Require Import ord fmap.
From SSProve.Crypt Require Import Prelude.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_util.


From HB Require Import structures.

HB.instance Definition _ nbits :=
  [Ord of (word nbits) by <:].

HB.instance Definition _ nbits :=
  [Choice of (word nbits) by <:].



(**
  Note for any of these types it would also be okay to write the cast, e.g., [(nat:choiceType)%type],
  directly in the term.
  This (backward-compatibility) file just made porting to mathcomp 2.1.0 easier.
  Just delete as soon as all references to the below casts are gone from the code base.
 *)

Definition unit_choiceType : choiceType := Datatypes.unit.
Definition nat_choiceType : choiceType := nat.
Definition int_choiceType : choiceType := Z.
Definition bool_choiceType : choiceType := bool.
Definition prod_choiceType (A B: choiceType) : choiceType := prod A B.
Definition fmap_choiceType (A: ordType) (B: choiceType) : choiceType := {fmap A -> B}.
Definition option_choiceType (A: choiceType) : choiceType := option A.
Definition fin_choiceType (p: positive) : choiceType := ordinal p.(pos).
Definition word_choiceType (nbits : wsize) : choiceType := word nbits.
Definition list_choiceType (A : choiceType) : choiceType := list A.

Definition sum_choiceType (A B: choiceType) : choiceType := (A + B)%type.

Definition unit_ordType: ordType := Datatypes.unit.
Definition nat_ordType: ordType := nat.
Definition int_ordType: ordType := Z.
Definition bool_ordType: ordType := bool.
Definition prod_ordType (A B: ordType) : ordType := prod A B.
Definition fmap_ordType (A B: ordType) : ordType := {fmap A -> B}.
Definition option_ordType (A: ordType) : ordType := option A.
Definition fin_ordType (p: positive) : ordType := ordinal p.(pos).
Definition word_ordType (nbits : wsize) : ordType := word nbits.
Definition list_ordType (A : ordType) : ordType := list A.


Definition sum_ordType (A B: ordType) : ordType := (A + B)%type.


Definition prod_finType (A B: finType) : finType := prod A B.
