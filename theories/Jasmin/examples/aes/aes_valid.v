Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect seq.
Set Warnings "notation-overridden,ambiguous-paths".

From JasminSSProve Require Import jasmin_translate aes_utils aes_jazz.
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.
From Crypt Require Import Axioms ChoiceAsOrd pkg_core_definition choice_type Prelude.

From extructures Require Import fset ord.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope positive_scope.

Ltac fix_lvals1 := clear_fset; eapply valid_translate_write_lvals1.
Ltac fix_lvals2 := clear_fset; eapply valid_translate_write_lvals2.

Lemma JRCON_valid id0 :
  ∑ L, forall I j, ValidCode (fset L) I (JRCON id0 j).
Proof.
  eexists.
  intros I j.
  unfold JRCON.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  simpl. unfold ValidCode.
  repeat match goal with
         | |- context[BinInt.Z.eqb _ _] => rewrite ?coerce_to_choice_type_K; destruct (BinInt.Z.eqb _ _)
         | |- valid_code _ _ _ => constructor
         | |- is_true (_ \in _) => solve [ tr_auto_in_fset | esolve_in ]
         | _ => intros
         end.
  Unshelve. exact [::].
Defined.

Definition JRCON_locs id0 : {fset Location} := fset (JRCON_valid id0).π1.

Lemma JKEY_EXPAND_valid id0 :
  ∑ L, forall I rcon rkey temp2, ValidCode (fset L) I (JKEY_EXPAND id0 rcon rkey temp2).
Proof.
  eexists.
  intros rcon rkey temp2.
  unfold JRCON.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  simpl. unfold ValidCode.
  repeat match goal with
         | |- valid_code _ _ _ => constructor
         | |- is_true (_ \in _) => solve [ tr_auto_in_fset | esolve_in ]
         | _ => intros
         end.
  Unshelve. exact [::].
Defined.

Definition JKEY_EXPAND_locs id0 : {fset Location} := fset (JKEY_EXPAND_valid id0).π1.

Lemma JKEYS_EXPAND_valid id0 :
  ∑ L, forall I rkey, ValidCode (fset L) I (JKEYS_EXPAND id0 rkey).
Proof.
  eexists.
  intros.
  unfold JAES.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  (* Opaque translate_for. *)
  Opaque translate_call.
  simpl.
  unfold translate_for.
  rewrite !coerce_typed_code_K.

  Ltac fix_rcon := clear_fset; eapply (JRCON_valid _).π2.
  Ltac fix_key_expand := clear_fset; eapply (JKEY_EXPAND_valid _).π2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  until_call.
  1: fix_rcon.
  eapply valid_bind.
  1: fix_lvals1.

  until_call.
  1: fix_key_expand.
  eapply valid_bind.
  1: fix_lvals2.

  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor.
  Unshelve. exact [::].
Defined.

Definition JKEYS_EXPAND_locs id0 : {fset Location} := fset (JKEYS_EXPAND_valid id0).π1.

Lemma JAES_ROUNDS_valid id0 :
  ∑ L, forall I rkeys m, ValidCode (fset L) I (JAES_ROUNDS id0 rkeys m).
Proof.
  eexists.
  intros.
  unfold JAES.
  unfold get_translated_static_fun.
  unfold translate_prog_static.
  unfold translate_funs_static.
  unfold translate_call_body.
  Opaque translate_for.
  Opaque translate_call.
  simpl.

  rewrite !coerce_typed_code_K.
  until_call.
  constructor.
  Unshelve. exact [::].
Defined.

Definition JAES_ROUNDS_locs id0 : {fset Location} := fset (JAES_ROUNDS_valid id0).π1.

Lemma JAES_valid id0 :
  ∑ L, forall I key m, ValidCode (fset L) I (JAES id0 key m).
Proof.
  eexists.
  unfold JAES.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  Opaque translate_for.
  Opaque translate_call.
  simpl.

  until_call.
  1: clear_fset.
  1: eapply (JKEYS_EXPAND_valid _).π2.
  eapply valid_bind.
  1: clear_fset.
  1: eapply valid_translate_write_lvals1.
  until_call.

  1: clear_fset.
  1: eapply (JAES_ROUNDS_valid _).π2.
  eapply valid_bind.
  1: clear_fset.
  1: eapply valid_translate_write_lvals1.
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor.
  Unshelve. exact [::].
Defined.

Definition JAES_locs id0 : {fset Location} := fset (JAES_valid id0).π1.

Lemma JXOR_valid id0 :
  ∑ L, forall I a1 a2, ValidCode (fset L) I (JXOR id0 a1 a2).
Proof.
  eexists.
  unfold JXOR.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  Opaque translate_for.
  Opaque translate_call.
  simpl.

  until_call.
  constructor.
  Unshelve. exact [::].
Defined.

Definition JXOR_locs id0 : {fset Location} := fset (JXOR_valid id0).π1.

Lemma JENC_valid id0 :
  ∑ L, forall I n k m, ValidCode (fset L) I (JENC id0 n k m).
Proof.

  unfold JENC.
  unfold get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  Opaque translate_for.
  Opaque translate_call.
  simpl.

  eexists.
  intros.
  until_call.

  1: clear_fset.
  1: eapply (JAES_valid _).π2.
  eapply valid_bind.
  1: clear_fset; eapply valid_translate_write_lvals1.
  until_call.
  1: clear_fset; eapply (JXOR_valid _).π2.
  eapply valid_bind.
  1: clear_fset; eapply valid_translate_write_lvals1.
  constructor; [solve [ tr_auto_in_fset | esolve_in ]| ].
  constructor.
  Unshelve. exact [::].
Defined.

Definition JENC_locs id0 : {fset Location} := fset (JENC_valid id0).π1.
