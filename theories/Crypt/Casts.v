Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ word.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fmap.
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

Definition unit_choiceType : choiceType := unit.
Definition bool_choiceType : choiceType := bool.
Definition prod_choiceType (A B: choiceType) : choiceType := prod A B.
Definition prod_finType (A B: finType) : finType := prod A B.
