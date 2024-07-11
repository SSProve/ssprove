Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrbool ssrnat choice fintype.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fmap.
From SSProve.Crypt Require Import Prelude.

From HB Require Import structures.


(**
  Note for any of these types it would also be okay to write the cast, e.g., [(nat:choiceType)%type],
  directly in the term.
  This (backward-compatibility) file just made porting to mathcomp 2.1.0 easier.
  Just delete as soon as all references to the below casts are gone from the code base.
 *)

Definition unit_choiceType : choiceType := Datatypes.unit.
Definition nat_choiceType : choiceType := nat.
Definition bool_choiceType : choiceType := bool.
Definition prod_choiceType (A B: choiceType) : choiceType := prod A B.
Definition fmap_choiceType (A: ordType) (B: choiceType) : choiceType := {fmap A -> B}.
Definition option_choiceType (A: choiceType) : choiceType := option A.
Definition fin_choiceType (p: positive) : choiceType := ordinal p.(pos).
Definition sum_choiceType (A B: choiceType) : choiceType := (A + B)%type.

Definition unit_ordType: ordType := Datatypes.unit.
Definition nat_ordType: ordType := nat.
Definition bool_ordType: ordType := bool.
Definition prod_ordType (A B: ordType) : ordType := prod A B.
Definition fmap_ordType (A B: ordType) : ordType := {fmap A -> B}.
Definition option_ordType (A: ordType) : ordType := option A.
Definition fin_ordType (p: positive) : ordType := ordinal p.(pos).
Definition sum_ordType (A B: ordType) : ordType := (A + B)%type.


Definition prod_finType (A B: finType) : finType := prod A B.
