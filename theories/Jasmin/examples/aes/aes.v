Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra zify.
From mathcomp.word Require Import word ssrZ.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 ZArith micromega.Lia List.

From Jasmin Require Import expr xseq waes word x86_instr_decl x86_extra.
From JasminSSProve Require Import jasmin_utils jasmin_translate word aes_jazz aes_utils aes_spec.

From Relational Require Import OrderEnrichedCategory.
From Crypt Require Import Prelude Package ChoiceAsOrd choice_type.

From extructures Require Import ord fset fmap.

Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.
Import AesNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!". 

Local Open Scope Z.

Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

Lemma rcon_E id0 pre i :
  (pdisj pre id0 fset0) ->
  (forall s0 s1, pre (s0, s1) -> (1 <= i < 11)%Z) ->
  ⊢ ⦃ fun '(s0, s1) => pre (s0, s1) ⦄ JRCON id0 i
    ≈ ret tt
    ⦃ fun '(v0, s0) '(v1, s1) => pre (s0, s1) /\ exists o, v0 = [('int ; o)] /\ o = wunsigned (rcon i) ⦄.
Proof.
  unfold JRCON.
  unfold get_translated_static_fun.
  intros Hpdisj H.
  simpl_fun.
  repeat setjvars.
  repeat match goal with
         | |- context[(?a =? ?b)%Z] => let E := fresh in destruct (a =? b)%Z eqn:E; [rewrite ?Z.eqb_eq in E; subst|]
         | |- _ => simpl; ssprove_contract_put_get_lhs; rewrite !coerce_to_choice_type_K
         end.
  all: ssprove_code_simpl; rewrite !coerce_to_choice_type_K; eapply r_put_lhs; ssprove_contract_put_get_lhs; eapply r_put_lhs; eapply r_ret.
  all: intros; destruct_pre; split_post; [ pdisj_apply Hpdisj | rewrite coerce_to_choice_type_K; eexists; split; eauto ].
  destruct (i =? 10)%Z eqn:E. 
  - rewrite Z.eqb_eq in E. subst. reflexivity.
  - apply H in H13. lia.
Qed.

Arguments nat_of_wsize : simpl never.
Arguments wsize_size_minus_1 : simpl never.

Lemma key_expand_aux rcon rkey temp2 rcon_ :
  word.toword rcon_ = rcon ->
  word.subword 0 U32 temp2 = word.word0 ->
  ((rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     (rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)) ⊕ wpshufd_128 (wAESKEYGENASSIST rkey (wrepr U8 rcon)) (wunsigned (wpack U8 2 [3; 3; 3; 3])) =
    key_expand rkey rcon_.
Proof.
      Set Printing Implicit.
  intros.
  subst.
  unfold key_expand.
  apply (wcat_eq U32 4). 
  intros [[ | [ | [ | [ | i]]]] j]; simpl; unfold tnth; simpl.
  - rewrite !subword_xor; auto.
    rewrite mul0n.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    simpl.
    rewrite !subword_u.
    simpl.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpack.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !wshr0.
    rewrite !subword_make_vec_32_0_32_128.
    simpl.
    unfold wAESKEYGENASSIST.
    rewrite subword_wshr; auto. 
    rewrite subword_make_vec_32_3_32_128.
    simpl.
    rewrite !wxorA.
    f_equal.
    unfold wpshufd1.
    simpl.
    rewrite wshr0.
    rewrite -wxorA.
    rewrite wxor_involutive.
    rewrite wxor_0_l.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor; auto.
    rewrite !subword_make_vec_32_1_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr; auto.
    rewrite !addn0.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    rewrite subword_wshr; auto.
    simpl.
    rewrite addn0.
    rewrite !wxorA.
    f_equal.
    rewrite H0.
    rewrite wxor_0_l.
    f_equal.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor; auto.
    rewrite !subword_make_vec_32_2_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr; auto.
    rewrite !addn0.
    rewrite !subword_xor; auto.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpshufd1.
    rewrite subword_wshr; auto.
    simpl.
    rewrite addn0.
    rewrite !wxorA.
    f_equal.
    rewrite H0.
    rewrite wxor_0_l.
    f_equal.
    f_equal.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor; auto.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr; auto.
    rewrite !addn0.
    rewrite !subword_xor; auto.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_2_32_128.
    unfold wpshufd1.
    rewrite subword_wshr; auto.
    simpl.
    rewrite !wxorA.
    f_equal.
    rewrite wxorC.
    rewrite !wxorA.
    f_equal.
    rewrite subword_wshr; auto.
    rewrite addn0.
    f_equal.
    rewrite wror_substitute.
    rewrite wxorC.
    rewrite wxorA.
    f_equal.
    f_equal.
    rewrite wreprI.
    reflexivity.
    all: auto.
  - lia.
Qed.

Lemma key_expand_aux2 rkey temp2 :
  word.subword 0 U32 temp2 = word.word0 ->
  word.subword 0 U32
    (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
       (word.wxor rkey (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey))) = word.word0.
Proof.
  intros.
  unfold lift2_vec.
  rewrite !make_vec_ws.
  rewrite subword_make_vec_32_0_32_128. simpl.
  unfold wpshufd1. simpl.
  rewrite subword_wshr; auto. simpl.
  rewrite addn0.
  rewrite subword_u.
  rewrite subword_make_vec_32_0_32_128. simpl.
  rewrite subword_u.
  unfold wpshufd1. simpl.
  rewrite subword_wshr; auto.
Qed.

Lemma key_expand_E pre id0 rcon rkey temp2 rcon_ :
  pdisj pre id0 fset0 →
  word.toword rcon_ = rcon →
  (forall s0 s1, pre (s0, s1) -> word.subword 0 U32 temp2 = word.word0) →
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
    JKEY_EXPAND id0 rcon rkey temp2
    ≈ ret tt
    ⦃ λ '(v0, s0) '(v1, s1),
      pre (s0, s1) ∧
        ∃ o1 o2,
          v0 = [ ('word U128 ; o1) ; ('word U128 ; o2) ] ∧
            o1 = key_expand rkey rcon_ ∧
            word.subword 0 U32 o2 = word.word0
    ⦄.
Proof.
  unfold JKEY_EXPAND, get_translated_static_fun.
  intros disj Hrcon Htemp2.
  simpl_fun. simpl.
  repeat setjvars.
  repeat clear_get.
  unfold sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single.
  simpl.
  rewrite !zero_extend_u.
  rewrite !coerce_to_choice_type_K.
  repeat eapply r_put_lhs.
  eapply r_ret.
  intros s0 s1 Hpre.
  destruct_pre; split_post.
  - pdisj_apply disj.
  - eexists _, _. intuition auto.
    + apply key_expand_aux; eauto. 
    + apply key_expand_aux2; eauto. 
Qed.

Lemma keyExpansion_E pre id0 rkey :
  (pdisj pre id0 [fset rkeys]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JKEYS_EXPAND id0 rkey
    ≈
    keyExpansion rkey
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ exists o, v0 = [( 'array ; o)] /\ to_arr U128 (mkpos 11) o = v1 ⦄.
Proof.
  intros disj.
  unfold JKEYS_EXPAND, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  Opaque translate_call.
  Opaque wrange.
  Opaque for_loop.

  simpl. simpl_fun.
  repeat setjvars.
  repeat clear_get.
  ssprove_code_simpl.
  ssprove_code_simpl_more.

  eapply r_put_lhs.
  eapply r_get_remember_lhs. intros v.
  eapply r_put_lhs.
  eapply r_put_lhs.

  unfold keyExpansion.
  eapply r_put_rhs.
  eapply r_get_remember_rhs. intros v0.
  eapply r_put_rhs.

  eapply r_bind.
  - simpl.
    eapply rpre_weaken_rule.
    + eapply translate_for_rule with
        (I := fun i => fun '(h0, h1) => pre (h0, h1)
                                        /\ word.subword 0 U32 (get_heap h0 temp2) = word.word0
                                        /\ (get_heap h0 key = chArray_get U128 (get_heap h0 rkeys) (i - 1) 16)
                                        /\ (forall j, (0 <= j < i) -> (to_arr U128 (mkpos 11) (get_heap h0 rkeys)) j = (get_heap h1 aes_spec.rkeys) j)
                                        /\ (forall j, (j < 0) \/ (11 <= j) -> get_heap h1 aes_spec.rkeys j = None)).

      (* the two following bullets are small assumptions of the translate_for rule *)
      * intros. simpl. solve_preceq.
      * lia.
      (* Inductive step of the for loop rule, we have to prove the bodies are equivalent and imply the successor predicate *)
      * intros i s_id Hs_id ile.
        ssprove_code_simpl.

        eapply r_get_remember_lhs. intros.

        (* Now we apply the correctnes of rcon *)
        eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).
        ** eapply rcon_E with (id0 := (s_id~1)%positive) (i:=x).
           (* We have to prove the precond is disjoint from the variables of rcon, i.e. any variables stored locally in rcon does not change the precond *)
           *** split.
               (* rcon_correct does not use any variables on the rhs *)
               2: { easy. }
               intros s0 s1 l a vr s_id' Hl Hs_id' H.
               assert (id0_preceq : id0 ⪯ s_id'). {
                 etransitivity. 1: eapply preceq_I. etransitivity. 1: eassumption. etransitivity. 1: eapply preceq_I. eassumption.
               }
               assert (id0_neq : id0 <> s_id'). {
                 apply prec_neq. eapply prec_preceq_trans. 1: eapply preceq_prec_trans. 1: etransitivity. 1: eapply preceq_I. 1: eassumption. 1: eapply prec_I. assumption.
               }
               intros. destruct_pre. split_post.
               { eapply disj; eauto. }
               { sheap. assumption. }
               { sheap. assumption. }
               { sheap. assumption. }
               { assumption. }
               { rewrite set_heap_commut; auto. 
                 apply injective_translate_var2. assumption. }
               { simpl. sheap. reflexivity. }
           (* this is an assumption of rcon_correct *)
           *** intros; destruct_pre. fold round. sheap. rewrite coerce_to_choice_type_K. lia.
        (* we continue after the rcon call *)
        ** intros a0 a1.
           simpl; ssprove_code_simpl.
           (* we need to know the value of a0 here *)
           eapply rpre_weak_hypothesis_rule; intros.
           destruct_pre; simpl.
           fold rcon.
           repeat clear_get.
           eapply r_put_lhs with (pre := λ '(s0',s1'), _ ).
           eapply r_get_remember_lhs. intros x1.
           eapply r_get_remember_lhs. intros x2.
           sheap.

           eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).

           (* First we apply correctness of key_expandP *)
           *** (* Here the rewrite is necessary. How should correctness be phrased in general such that this is not important? *)
               rewrite !coerce_to_choice_type_K.
               eapply key_expand_E with (id0 := (s_id~0~1)%positive) (rcon := (wunsigned (aes_spec.rcon i))) (rkey := x1) (temp2 := x2) (rcon_ := aes_spec.rcon i).
               (* again, we have to prove that our precond does not depend key_expand locations *)
               { split.
                 (* key_expandP also does not use variables on the rhs *)
                 2: { easy. }
                 intros s0 s1 l a vr s_id' Hl Hs_id' H1.
                 assert (id0_preceq : id0 ⪯ s_id'). {
                 etransitivity. 1: eapply preceq_I. etransitivity. 1: eassumption. etransitivity. 1: eapply preceq_O. etransitivity. 1: eapply preceq_I. eassumption.
                 }
                 assert (id0_neq : id0 <> s_id'). {
                   apply prec_neq. eapply prec_preceq_trans. 1: eapply preceq_prec_trans. 1: etransitivity. 1: eapply preceq_I. 1: eassumption. 1: eapply prec_O. etransitivity. 1: eapply prec_I. assumption.
                 }
                 destruct_pre. sheap. split_post.
                 { eapply disj; eauto. }
                 { sheap; assumption. }
                 { sheap; assumption. }
                 { sheap; assumption. }
                 { assumption. }
                 { reflexivity. }
                 { simpl. sheap. reflexivity. }
                 { eexists. eauto. }
                 { rewrite set_heap_commut; [ | neq_loc_auto ].
                   rewrite [set_heap _ _ a](set_heap_commut); [ | neq_loc_auto ].
                   reflexivity. }
                 { simpl. sheap. reflexivity. }
                 { simpl. sheap. reflexivity. }
               }
               (* this is an assumption of key_expandP, true by definition of rcon *)
               { reflexivity. }
               { intros. destruct_pre. sheap. assumption. }
           (* we continue after the call *)
           *** intros.
               eapply rpre_weak_hypothesis_rule.
               intros; destruct_pre. simpl.
               rewrite !zero_extend_u.

               eapply r_put_lhs with (pre := λ '(s0',s1'), _).
               eapply r_put_lhs.
               eapply r_get_remember_lhs. intros x2.
               eapply r_get_remember_lhs. intros x3.
               eapply r_get_remember_lhs. intros x4.
               eapply r_put_lhs.
               eapply r_get_remember_rhs. intros x5.
               eapply r_put_rhs.
               eapply r_ret.

               sheap.
               rewrite !coerce_to_choice_type_K.
               rewrite !zero_extend_u.
               intros s6 s7 H24.

               destruct_pre.
               sheap.

               split_post.
               (* here we prove that the invariant is preserved after a single loop, assuming it holds before *)
               { pdisj_apply disj. }
               { assumption. }
               { replace (Z.succ i - 1) with i by lia.
                 rewrite chArray_get_set_eq.
                 reflexivity. }
               { intros j Hj.
                 destruct (Z.eq_dec i j).

                 (* i = j *)
                 - subst. simpl.
                   pose proof to_arr_set_eq.
                   simpl.
                   rewrite to_arr_set_eq. 2: lia.
                   rewrite setmE. rewrite eq_refl.

                   f_equal. unfold getmd. rewrite -H41. 2: lia. rewrite getm_to_arr. 2: lia.
                   f_equal. rewrite !get_set_heap_neq in H33. 2-3: neq_loc_auto. rewrite -H33. assumption.

                 (* i <> j *)
                 - rewrite to_arr_set_neq. 2-3: lia.
                   rewrite setmE.
                   assert (@eq bool (@eq_op Z_ordType j i) false). 1: apply/eqP; auto.
                   rewrite H3.
                   apply H41. lia. }
               { intros j Hj.

                 rewrite setmE.
                 (* why do I have to set printing off to realize this? Shouldn't j == i always mean the same on the same type? *)
                 assert (@eq_op (Ord.eqType Z_ordType) j i = false). 1: apply/eqP; lia.
                 rewrite H3.
                 apply H43.
                 assumption. }
    (* the next bullet is the proof that the invariant of the for loop is true at the beginning (this goal is generated by pre_weaken rule and translate_for) *)
    + intros s0 s1 H.
      destruct_pre.
      sheap.

      rewrite !coerce_to_choice_type_K.
      rewrite !zero_extend_u.

      split_post.
      (* prove that pre is preserved *)
      * pdisj_apply disj.
      (* first invariant *)
      * simpl. unfold tr_app_sopn_tuple. simpl. rewrite subword_word0. reflexivity.
      (* second invariant *)
      * rewrite chArray_get_set_eq. reflexivity.
      (* third invariant *)
      * intros j Hj. assert (j = 0) by lia. subst.
        rewrite to_arr_set_eq. 1: rewrite setmE; rewrite eq_refl; reflexivity. lia.
      * intros. rewrite setmE.
        (* Set Printing All. *)
        replace (_ == _) with false.
        1: apply emptymE. symmetry. apply/eqP. lia.
  (* after for loop *)
  - intros a0 a1.
    simpl.
    eapply r_get_remember_lhs with (pre := fun '(s0, s1) => _). intros x.
    eapply r_get_remember_rhs. intros x0.
    eapply r_ret.
    intros s0 s1 H.
    destruct_pre. split_post.
    (* prove the final post conditions: pre and that the values of rkeys agree *)
    + assumption.
    + eexists. split. 1: reflexivity.
      eapply eq_fmap. intros j.
      simpl.
      destruct ((0 <=? j) && (j <? 11)) eqn:E.
      (* within bounds, this follows from the precondition *)
      * rewrite !coerce_to_choice_type_K. apply H4. lia.
      * rewrite -> getm_to_arr_None' by lia.
        rewrite H6; auto. 
        lia.
Qed.

Lemma aes_rounds_E pre id0 rkeys msg :
  (pdisj pre id0 [fset state]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JAES_ROUNDS id0 rkeys msg
    ≈
    aes_rounds (to_arr U128 (mkpos 11) rkeys) msg
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ exists o, v0 = [ ('word U128 ; o) ] /\ o = v1 ⦄.
Proof.
  unfold JAES_ROUNDS, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  intros disj.

  Opaque translate_call.
  Opaque wrange.
  Opaque for_loop.

  simpl. simpl_fun.
  repeat setjvars.
  ssprove_code_simpl.
  ssprove_code_simpl_more.
  unfold aes_rounds.

  repeat clear_get.
  do 4 eapply r_put_lhs.
  eapply r_put_rhs.

  eapply r_bind.
  - eapply translate_for_rule_weaken with
      (I := fun i => fun '(h0, h1) => pre (h0, h1)
                                /\ get_heap h0 state = get_heap h1 aes_spec.state
                                /\ get_heap h0 rkeys0 = rkeys).
    + intros; destruct_pre.
      rewrite !zero_extend_u.
      rewrite !coerce_to_choice_type_K.
      sheap.
      split_post.
      * pdisj_apply disj.
      * rewrite getmd_to_arr; auto. lia.
      * reflexivity.
    + intros. simpl. auto with preceq.
    + lia.
    + intros.
      repeat (eapply r_get_remember_lhs; intros).
      eapply r_put_lhs.
      eapply r_get_remember_rhs; intros.
      eapply r_put_rhs.
      eapply r_ret.
      intros s0 s1 Hpre; destruct_pre.
      unfold tr_app_sopn_tuple.
      simpl.
      rewrite !zero_extend_u.
      rewrite !coerce_to_choice_type_K.
      sheap.
      split_post.
      * pdisj_apply disj.
      * rewrite -> H12.
        rewrite wAESENC_wAESENC_.
        rewrite getmd_to_arr; auto.
        lia.
      * reflexivity.
  - intros a0 a.
    eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x.
    eapply r_get_remember_lhs. intros x0.
    eapply r_put_lhs.
    eapply r_get_remember_lhs. intros x1.

    eapply r_get_remember_rhs. intros x2.
    eapply r_put_rhs.
    eapply r_get_remember_rhs. intros x3.
    eapply r_ret.

    intros s0 s1 Hpre; destruct_pre.
    rewrite !coerce_to_choice_type_K.
    rewrite !zero_extend_u.
    sheap.
    split_post.
    + pdisj_apply disj.
    + unfold tr_app_sopn_tuple.
      simpl.
      rewrite !zero_extend_u.
      rewrite -> H6.
      rewrite getmd_to_arr; try lia.
      rewrite wAESENCLAST_wAESENCLAST_.
      eexists. split.
      * reflexivity.
      * simpl.
        rewrite zero_extend_u.
        reflexivity.
Qed.

Lemma aes_E pre id0 k m :
  (pdisj pre id0 [fset rkeys ; state]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JAES id0 k m
    ≈
    Caes k m
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ exists o, v0 = [ ('word U128 ; o )] /\ v1 = o ⦄.
Proof.
  unfold JAES, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
  intros disj.

  simpl. simpl_fun.
  repeat setjvars.
  ssprove_code_simpl.
  repeat clear_get.
  unfold Caes.

  eapply r_put_lhs.
  eapply r_put_lhs.
  eapply r_bind.
  - rewrite !zero_extend_u.
    eapply keyExpansion_E.
    split.
    + intros s0 s1 l a vr s_id' Hl Hs_id' H.
      assert (id0_preceq : id0 ⪯ s_id'). {
        etransitivity. 1: eapply preceq_I. eassumption.
      }
      assert (id0_neq : id0 <> s_id'). {
        apply prec_neq. eapply prec_preceq_trans. 1: eapply prec_I. eassumption.
      }
      destruct_pre. split_post.
      * eapply disj; eauto. 
      * reflexivity.
      * rewrite set_heap_commut. 2: neq_loc_auto. rewrite [set_heap (set_heap H2 _ _) _ _]set_heap_commut. 1: reflexivity.
        neq_loc_auto. 
    + intros; destruct_pre; split_post.
      * eapply disj.
        ** move: H. rewrite in_fset in_cons=>/orP [];[|easy] => /eqP ->. solve_in.
        ** eassumption.
      * reflexivity.
      * reflexivity.
  - intros.
    eapply rpre_weak_hypothesis_rule.
    Opaque aes_rounds.
    intros; destruct_pre.
    simpl.
    rewrite !coerce_to_choice_type_K.
    fold rkeys. clear_get.

    eapply r_put_lhs with (pre := fun _ => _).
    eapply r_get_remember_lhs. intros.
    (* this is a very brute force way of remembering the value of 'in', should be done differently *)
    eapply rpre_weak_hypothesis_rule.
    intros; destruct_pre. sheap.
    eapply r_bind.
    + eapply aes_rounds_E.
      split.
      * intros s0 s1 l a vr s_id' Hl Hs_id' H.
        assert (id0_preceq : id0 ⪯ s_id'). {
          etransitivity. 1: eapply preceq_O. etransitivity. 1: eapply preceq_I. eassumption.
        }
        assert (id0_neq : id0 <> s_id'). {
          apply prec_neq. eapply prec_preceq_trans. 1: etransitivity. 1: eapply prec_O. 1: eapply prec_I. eassumption.
        }
        destruct_pre. sheap. split_post.
        ** eapply disj; eauto.
        ** reflexivity.
        ** reflexivity.
        ** eexists. eauto.
        ** rewrite set_heap_commut.
           1: rewrite [set_heap (set_heap _ _ _) _ a]set_heap_commut.
           1: rewrite [set_heap (set_heap _ _ _) _ a]set_heap_commut.
           1: reflexivity.
           all: neq_loc_auto.
        ** simpl. sheap. reflexivity.
      * intros; destruct_pre; split_post.
        ** eapply disj.
           *** move: H. rewrite in_fset in_cons=>/orP []. 1: move=> /eqP ->; solve_in.
               simpl. clear -l. easy.
           *** eassumption.
        ** reflexivity.
        ** reflexivity.
        ** eexists. eauto.
        ** reflexivity.
        ** simpl. sheap. reflexivity.
    + intros.
      eapply rpre_weak_hypothesis_rule.
      intros; destruct_pre.
      simpl. fold out. clear_get.
      eapply r_put_lhs with (pre := fun _ => _).
      eapply r_ret.
      intros.
      destruct_pre; sheap; split_post.
      * pdisj_apply disj.
      * eexists.
        split; [reflexivity|].
        simpl.
        rewrite !zero_extend_u.
        reflexivity.
Qed.
