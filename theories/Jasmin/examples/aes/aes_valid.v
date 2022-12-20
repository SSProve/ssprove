From JasminSSProve Require Import jasmin_translate.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq word word.ssrZ.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From JasminSSProve Require Import aes_jazz jasmin_utils.
From Jasmin Require Import expr sem.

Import JasminNotation JasminCodeNotation.

Require Import String.
Local Open Scope string.

Local Open Scope positive_scope.

Ltac esolve_in :=
  rewrite in_fset; apply/xseq.InP;
  repeat lazymatch goal with
    | |- List.In _ (_ :: _) => eapply List.in_cons
    | |- _ => eapply List.in_eq
    end.

Ltac tr_inseq_try :=
  apply/orP ; first [ left ; rewrite translate_var_eq eq_refl ; reflexivity
                    | right ; tr_inseq_try ].

Ltac tr_inset_try :=
  rewrite in_fset ; tr_inseq_try.

Ltac tr_auto_in_fset :=
  eauto ;
  try tr_inset_try.

Ltac until_call :=
  simpl; repeat match goal with
           | |- ValidCode _ _ _ => red
           | |- valid_code _ _ (_ ← translate_call _ _ _ _ _ ;; _) => eapply valid_bind
           | |- valid_code _ _ (_ ← (x ← _ ;; _) ;; _) => rewrite bind_assoc
           | |- _ => constructor; [solve [ tr_auto_in_fset | esolve_in ]| ]; intros
           | |- _ -> _ => intros
           end.

Lemma valid_code_cons {A} a l I (c : raw_code A) :
  valid_code (fset l) I c -> valid_code (fset (a :: l)) I c.
Proof.
  intros.
  induction c; econstructor.
  - apply inversion_valid_opr in H as []. easy.
  - intros. apply H0. apply inversion_valid_opr in H as []. easy.
  - apply inversion_valid_getr in H as []. rewrite in_fset in_cons. apply/orP; right. rewrite -in_fset. easy.
  - intros. apply H0. apply inversion_valid_getr in H as []. easy.
  - apply inversion_valid_putr in H as []. rewrite in_fset in_cons. apply/orP; right. rewrite -in_fset. easy.
  - apply inversion_valid_putr in H as []. apply IHc. easy.
  - intros. apply H0. eapply inversion_valid_sampler. easy.
Qed.

Lemma valid_code_catC {A} l1 l2 I (c : raw_code A) :
  valid_code (fset (l1 ++ l2)) I c -> valid_code (fset (l2 ++ l1)) I c.
Proof. by rewrite !fset_cat fsetUC. Qed.

Lemma valid_code_cat_r {A} l1 l2 I (c : raw_code A) :
  valid_code (fset l1) I c -> valid_code (fset (l1 ++ l2)) I c.
Proof.
  intros.
  induction l2.
  - rewrite cats0. easy.
  - apply valid_code_catC. simpl. apply valid_code_cons. apply valid_code_catC. easy.
Qed.

Lemma valid_code_cat_l {A} l1 l2 I (c : raw_code A) :
  valid_code (fset l2) I c -> valid_code (fset (l1 ++ l2)) I c.
Proof. intros; apply valid_code_catC. apply valid_code_cat_r. easy. Qed.

Lemma valid_translate_write_lvals1 I id0 (v : var_i) vs :
  valid_code (fset [:: translate_var id0 v]) I (translate_write_lvals [::] id0 [:: (Lvar v)] vs) .
Proof.
  destruct vs.
  - constructor.
  - constructor.
    1: auto_in_fset.
    constructor.
Qed.

Lemma valid_translate_write_lvals2 I id0 (v1 v2 : var_i) vs :
  valid_code (fset [:: translate_var id0 v1 ; translate_var id0 v2]) I (translate_write_lvals [::] id0 [:: (Lvar v1) ; (Lvar v2)] vs) .
Proof.
  destruct vs.
  - constructor.
  - constructor.
    1: auto_in_fset.
    destruct vs.
    + constructor.
    + constructor.
      1: auto_in_fset.
      constructor.
Qed.

Ltac clear_fset :=
  repeat match goal with
    | |- ValidCode _ _ _ => red
    | |- valid_code (fset (_ :: _)) _ _ => eapply valid_code_cons
    | |- valid_code (fset (_ ++ _)) _ _ => eapply valid_code_cat_l
    end; eapply valid_code_cat_r.

Ltac fix_lvals1 := clear_fset; eapply valid_translate_write_lvals1.
Ltac fix_lvals2 := clear_fset; eapply valid_translate_write_lvals2.

(* Definition Jvars {A} : raw_code -> {fset Location}. *)

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
