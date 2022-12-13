Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool
  ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
Set Warnings "-notation-overridden".
From Jasmin Require Import expr.
Set Warnings "notation-overridden".
From Jasmin Require Import x86_instr_decl x86_extra.
From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.

Set Bullet Behavior "Strict Subproofs".
(* Set Default Goal Selector "!". *) (* I give up on this for now. *)

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import micromega.Lia.
From mathcomp.word Require Import word ssrZ.
From JasminSSProve Require Import aes_jazz jasmin_utils.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality.

Notation call fn := (translate_call _ fn _).

Section Hacspec.

  Lemma foo id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
      JKEY_COMBINE id0 rcon rkey temp2
      ≈
      is_state (key_combine rcon rkey temp2)
      ⦃ fun '(v0, _) '(v1, _) =>
          exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                   /\ (o1, o2) = v1 ⦄.
  Proof.
    unfold translate_call, translate_call_body.
    Opaque translate_call.

    simpl.
    unfold sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single.
    simpl.

  Admitted.


  Lemma bar id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
      JKEY_EXPAND id0 rcon rkey temp2
      ≈
      key_expand (wrepr U8 rcon) rkey temp2
      ⦃ fun '(v0, _) '(v1, _) =>
          exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                   /\ (o1, o2) = v1 ⦄.
  Proof.
    Transparent translate_call.
    unfold translate_call, translate_call_body.
    Opaque translate_call.
    simpl.
Admitted.
