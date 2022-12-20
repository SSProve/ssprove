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

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality Hacspec_Lib.
Open Scope hacspec_scope.

Notation call fn := (translate_call _ fn _).

Section Hacspec.

  (* NB: this redefines neq_loc_auto, which helps some tactics, since checking for inequality by computation is not feasible for translated variables *)
  Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

  Ltac destruct_pre :=
    repeat
      match goal with
      | [ H : set_lhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : set_rhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : _ /\ _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : (_ ⋊ _) _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : exists _, _ |- _ ] =>
          let o := fresh in
          destruct H as [o]
      end; simpl in *; subst.

  Lemma det_jkey id0 rcon rkey temp2 : deterministic (JKEY_COMBINE id0 rcon rkey temp2).
  Proof.
    unfold translate_call, translate_call_body.
    Opaque translate_call.
    simpl.

    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
    Transparent translate_call.
  Defined.

  Lemma det_key_combine rcon rkey temp2 : deterministic (is_state (key_combine rcon rkey temp2)).
  Proof.
    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
  Defined.

  Lemma unfold_det_run : forall {A : choiceType} c [h : @deterministic A c] s, @det_run A c h s = match h with
                                                                                             | deterministic_ret x => (x, s)
                                                                                             | deterministic_get ℓ k hk => det_run (k (get_heap s ℓ)) (h := hk _) s
                                                                                             | deterministic_put ℓ v k hk => det_run k (h := hk) (set_heap s ℓ v)
                                                                                             end.
  Proof. destruct h ; reflexivity. Qed.

  Ltac bind_jazz_hac :=
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] =>
        eapply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) _) ; [ rewrite !zero_extend_u | intros ]
    end.
    
  (* match goal with *)
  (* | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] => *)
  (*     apply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ Q _) ; [ | intros ; unfold pre_to_post ] *)
  (* end. *)

  Ltac remove_get_in_lhs :=
    eapply better_r_get_remind_lhs ;
    unfold Remembers_lhs , rem_lhs ;
    [ intros ? ? k ;
      destruct_pre ;
      repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq ;
      reflexivity | ].

  Notation JVSHUFPS i rkey temp1 temp2 := (trc VSHUFPS i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]).

  Lemma wpshufd_eq :
    forall (rkey : 'word U128)  (i : nat),
      i < 4 ->
      wpshufd1 rkey (wrepr U8 255) i =
        is_pure (vpshufd1 rkey (Hacspec_Lib_Pre.repr 255) (Hacspec_Lib_Pre.repr i)).
  Proof.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      unfold Hacspec_Lib_Pre.repr.
      unfold wrepr.
      unfold toword at 1, mkword at 2.
      unfold Hacspec_Lib_Pre.from_uint_size, Hacspec_Lib_Pre.Z_uint_sizeable, Hacspec_Lib_Pre.unsigned, wunsigned.
      unfold Hacspec_Lib_Pre.int_mul, mul_word.
      rewrite !mkwordK.
      rewrite (Zmod_small _ (modulus nat127.+1)) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      rewrite (Zmod_small _ (modulus (wsize_size_minus_1 U32).+1)) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      f_equal.
      rewrite (Zmod_small _ (modulus U32)) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      f_equal.
      unfold wunsigned.
      unfold Hacspec_Lib_Pre.usize_shift_right.
      unfold wshr.
      unfold urepr, val, word_subType.
      Set Printing Coercions.
      unfold toword, mkword.
      unfold lsr.
      unfold mkword.
      simpl.
      Compute modulus nat7.+1.
      rewrite (Zmod_small) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      rewrite (Zmod_small _ (modulus nat31.+1)) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      f_equal.
      f_equal.
      Opaque Nat.mul.
      cbn.
      replace (2 mod (modulus (nat_of_wsize U32)))%Z with 2%Z by reflexivity.
      cbn.
      rewrite (Zmod_small) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      rewrite (Zmod_small) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      rewrite (Zmod_small) ; [ | destruct i as [ | [ | [ | [] ]]] ; easy ].
      lia.
      Transparent Z.mul.
      Transparent Nat.mul.
  Qed.

  Lemma wpshufd_eq_state :
    forall {H} (rkey : 'word U128)  (i : nat),
      i < 4 ->
⊢ ⦃ H ⦄
     ret (wpshufd1 rkey (wrepr U8 255) i) ≈
     is_state (vpshufd1 rkey (Hacspec_Lib_Pre.repr 255) (Hacspec_Lib_Pre.repr i))
       ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    rewrite wpshufd_eq ; [ | apply H0 ].
    now apply r_ret.
  Qed.


  Ltac match_wpshufd1_vpshufd1 :=
    (let w := fresh in
     let y := fresh in
     let b := fresh in
     set (w := wpshufd1 _ _ _) ;
     set (y := fun _ : Hacspec_Lib_Pre.int32 => _) ;
     set (b := vpshufd1 _ _ _);
     let k := fresh in
     let l := fresh in
     match goal with
     | [ |- context [ ⊢ ⦃ ?P ⦄ ?lhs ≈ _ ⦃ _ ⦄ ] ] => set (k := P) ; set (l := lhs)
     end ;
     pattern (w) in l ;
     subst l ;
     apply (@r_bind _ _ _ _ (ret w) (prog (is_state b)) _ y _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ k (h0, h1))) ; subst w y b ; hnf).

  Lemma Z_lor_pow2 : (forall (x y : Z) (k : nat), (0 <= x < 2 ^ k)%Z -> (0 <= y < 2 ^ k)%Z -> (0 <= Z.lor x y < 2 ^ k)%Z).
  Proof.
    clear.
    intros.

    split.
    apply Z.lor_nonneg ; easy.
    destruct x as [ | x | x ].
    - apply H0.
    - destruct y as [ | y | y ].
      + apply H.
      + destruct H as [_ ?].
        destruct H0 as [_ ?].
        apply Z.log2_lt_pow2 in H ; [ | easy ].
        apply Z.log2_lt_pow2 in H0 ; [ | easy ].
        apply Z.log2_lt_pow2 ; [ easy | ].
        rewrite (Z.log2_lor) ; [ | easy | easy ].
        apply Z.max_lub_lt ; easy.
      + easy.
    - easy.
  Qed.

  Lemma num_smaller_if_modulus_smaller : (forall {WS} (x : 'word WS) z, (modulus WS < z)%Z -> (0 <= x < z)%Z).
  Proof.
        clear.
        cbn.
        intros.
        destruct x.
        pose (ssrbool.elimT (iswordZP _ _) i).
        split. easy.
        unfold word.toword.
        destruct a.
        eapply Z.lt_trans ; [ apply H1 | apply H].
  Qed.

  Lemma shift_left_4_byte_ok :
    (forall i (a : 'word U32),
        i < 4 ->
        (0 <= Z.shiftl (wunsigned a) (Z.of_nat (i * 32)) <
           modulus (wsize_size_minus_1 U128).+1)%Z).
  Proof.
    clear.
    destruct a.
    unfold wunsigned, urepr, val, word_subType, word.toword.
    split. apply Z.shiftl_nonneg. lia.
    apply (ssrbool.elimT (iswordZP _ _)) in i0.
    destruct i0.
    rewrite Z.shiftl_mul_pow2 ; [ | lia].
    eapply Z.lt_le_trans.
    rewrite <- (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat _) toword) ; [ | lia ].
    apply H1.
    destruct i as [ | [ | [ | [ | []] ]] ] ; easy.
  Qed.

  Lemma key_combined_eq id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
        JKEY_COMBINE id0 rcon rkey temp2
        ≈
        is_state (key_combine rcon rkey temp2)
        ⦃ fun '(v0, _) '(v1, _) =>
            exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                     /\ (o1, o2) = v1 ⦄.
  Proof.
    set (JKEY_COMBINE _ _ _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    (* unfold ssprove_jasmin_prog in r. *)
    simpl in r.

    subst r.
    rewrite !zero_extend_u.
    unfold key_combine.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    remove_get_in_lhs.
    bind_jazz_hac ; [ shelve | ].

    do 5 (apply better_r_put_lhs ; do 2 remove_get_in_lhs ; bind_jazz_hac ; [shelve | ]).
    apply better_r_put_lhs ; do 2 remove_get_in_lhs ; apply r_ret.

    intros.
    destruct_pre.
    eexists.
    eexists.
    split ; [ reflexivity | ].
    cbn.
    rewrite !zero_extend_u.
    reflexivity.

    Unshelve.
    {
      (* rewrite !zero_extend_u. *)

      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.
      unfold asm_opI.
      unfold asm_op_instr.
      unfold semi, arch_extra.get_instr_desc.
      unfold instr_desc, _asm_op_decl, instr_desc_op, _asm, x86_extra.
      unfold x86_sem.x86.
      unfold x86_op_decl.
      unfold x86_instr_desc.
      unfold id_semi.
      unfold Ox86_VPSHUFD_instr.
      unfold ".1".
      unfold x86_VPSHUFD.
      unfold wpshufd.

      set (totce _) at 2.
      cbn in t.
      unfold totce in t.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      unfold totce.
      subst t.
      unfold ".π2".

      unfold wpshufd_128.
      unfold iota.
      unfold map.
      (* set (wpshufd1 _ _ _). *)
      (* set (wpshufd1 _ _ _). *)
      (* set (wpshufd1 _ _ _). *)
      unfold vpshufd.

      match_wpshufd1_vpshufd1.

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).
      replace (wrepr _ _) with (wrepr U8 255) by (rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).
      apply (@wpshufd_eq_state _ rkey 0 ltac:(easy)).
      intros.

      match_wpshufd1_vpshufd1.

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).
      replace (wrepr _ _) with (wrepr U8 255) by (rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).
      eapply (@wpshufd_eq_state _ rkey 1 ltac:(easy)).
      intros.

      match_wpshufd1_vpshufd1.

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).
      replace (wrepr _ _) with (wrepr U8 255) by (rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).
      eapply (@wpshufd_eq_state _ rkey 2 ltac:(easy)).
      intros.

      match_wpshufd1_vpshufd1.

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).
      replace (wrepr _ _) with (wrepr U8 255) by (rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).
      eapply (@wpshufd_eq_state _ rkey 3 ltac:(easy)).
      intros.

      apply r_ret.
      intros.
      destruct H as [? [? [? [? []]]]].
      subst.
      subst H2.
      clear -H7.
      split ; [ | eexists ; apply H7 ].

      apply word_ext.

      unfold wcat_r.

      unfold ".|".
      unfold "_ shift_left _".
      unfold Hacspec_Lib_Pre.shift_left_.
      unfold Hacspec_Lib_Pre.int_or.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.from_uint_size.
      unfold Hacspec_Lib_Pre.usize.
      unfold Hacspec_Lib_Pre.Z_uint_sizeable.
      unfold Hacspec_Lib_Pre.unsigned.
      unfold cast_int.
      unfold lift_to_both0 , lift_to_both, is_pure.
      unfold word.wor, wor.
      unfold wshl, lsl.
      unfold wrepr, wunsigned, urepr, val, word_subType, mkword, toword.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.nat_uint_sizeable.
      unfold Hacspec_Lib_Pre.repr.
      unfold wrepr.
      unfold mkword.
      unfold toword.
      unfold Hacspec_Lib_Pre.unsigned.

      rewrite !Zmod_small.

      all: try easy.
      all: try (apply num_smaller_if_modulus_smaller ; easy).

      2: apply (shift_left_4_byte_ok 3) ; easy.
      2: apply (shift_left_4_byte_ok 2) ; easy.
      2: apply (shift_left_4_byte_ok 1) ; easy.

      setoid_rewrite <- Z.lor_assoc.
      setoid_rewrite <- Z.lor_assoc.
      f_equal.

      symmetry.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite !Z.shiftl_lor.
      f_equal.
      f_equal.
      rewrite Z.lor_0_r.
      reflexivity.

      destruct a₁, a₁0, a₁1, a₁2.
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      apply (ssrbool.elimT (iswordZP _ _)) in i, i0, i1, i2.
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        repeat apply Z.mul_nonneg_nonneg ; easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply i | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in i0 ; [ | easy].
        apply i0.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in i1 ; [ | easy].
        apply i1.
        easy.

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in i2 ; [ | easy].
        apply i2.
        easy.
      }
    }
    {

      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.
      unfold asm_opI.
      unfold asm_op_instr.
      unfold semi, arch_extra.get_instr_desc.
      unfold instr_desc, _asm_op_decl, instr_desc_op, _asm, x86_extra.
      unfold x86_sem.x86.
      unfold x86_op_decl.
      unfold x86_instr_desc.
      unfold id_semi.
      unfold Ox86_VPSHUFD_instr.
      unfold ".1".
      unfold x86_VPSHUFD.
      unfold wpshufd.

      set (totce _) at 2.
      cbn in t.
      unfold totce in t.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      unfold totce.
      subst t.
      unfold ".π2".

      unfold wshufps_128.
      unfold lift2_vec.
      unfold make_vec.
      rewrite map2E.
      unfold zip.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.
      unfold sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single.

      unfold vshufps.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ temp2) with temp2.
      2:{
        destruct temp2.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 16)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 16) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ temp2) with temp2.
      2:{
        destruct temp2.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 16)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 16) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ rcon) with rcon.
      2:{
        destruct rcon.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 16)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 16) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.
      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ rcon) with rcon.
      2:{
        destruct rcon.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 16)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 16) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      apply r_ret.

      intros.
      destruct H as [? [? [? [? [? [[]]]]]]].
      subst.
      split.
      2:{
        unfold H2.
        exists x. easy.
      }

      apply word_ext.
      unfold wcat_r.

      unfold ".|".
      unfold "_ shift_left _".
      unfold Hacspec_Lib_Pre.shift_left_.
      unfold Hacspec_Lib_Pre.int_or.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.from_uint_size.
      unfold Hacspec_Lib_Pre.usize.
      unfold Hacspec_Lib_Pre.Z_uint_sizeable.
      unfold Hacspec_Lib_Pre.unsigned.
      unfold cast_int.
      unfold lift_to_both0 , lift_to_both, is_pure.
      unfold word.wor, wor.
      unfold wshl, lsl.
      unfold wrepr, wunsigned, urepr, val, word_subType, mkword, toword.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.nat_uint_sizeable.
      unfold Hacspec_Lib_Pre.repr.
      unfold wrepr.
      unfold mkword.
      unfold toword.
      unfold Hacspec_Lib_Pre.unsigned.

      rewrite !Zmod_small.

      all: try easy.
      all: try (apply (num_smaller_if_modulus_smaller) ; easy).

      setoid_rewrite <- Z.lor_assoc.
      setoid_rewrite <- Z.lor_assoc.
      f_equal.

      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.

      rewrite !Z.shiftl_lor.
      f_equal.

      apply (shift_left_4_byte_ok 3) ; easy.
      apply (shift_left_4_byte_ok 2) ; easy.
      apply (shift_left_4_byte_ok 1) ; easy.


      destruct a₁0, a₁1, a₁2, a₁3.
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        repeat apply Z.mul_nonneg_nonneg ; easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
      }
      {
        destruct a₁0, a₁1, a₁2, a₁3.
rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        easy.

        apply (Z_lor_pow2 (toword2 * _)%Z _ nat127.+1).

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
        easy.
      }
      }
      {
        destruct a₁0, a₁1, a₁2, a₁3.
rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        repeat apply Z.mul_nonneg_nonneg ; easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
      }
      }
    }
    {
      cbn.
      apply r_ret.
      intros.
      split.
      reflexivity.
      apply H.
    }
    {
      (* TODO: Next vshufs *)
          {

      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.
      unfold asm_opI.
      unfold asm_op_instr.
      unfold semi, arch_extra.get_instr_desc.
      unfold instr_desc, _asm_op_decl, instr_desc_op, _asm, x86_extra.
      unfold x86_sem.x86.
      unfold x86_op_decl.
      unfold x86_instr_desc.
      unfold id_semi.
      unfold Ox86_VPSHUFD_instr.
      unfold ".1".
      unfold x86_VPSHUFD.
      unfold wpshufd.

      set (totce _) at 2.
      cbn in t.
      unfold totce in t.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      unfold totce.
      subst t.
      unfold ".π2".

      unfold wshufps_128.
      unfold lift2_vec.
      unfold make_vec.
      rewrite map2E.
      unfold zip.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.
      unfold sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single.

      unfold vshufps.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ a₁0) with a₁0.
      2:{
        destruct a₁0.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 140) by now do 3 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).

      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 140)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 140) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ a₁0) with a₁0.
      2:{
        destruct a₁0.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 140) by now do 3 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 140)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 140) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ a₁1) with a₁1.
      2:{
        destruct a₁1.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 140) by now do 3 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 140)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 140) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.
      match_wpshufd1_vpshufd1.

      set (ret _).
      simpl in r.
      subst r.
      rewrite !zero_extend_u.
      replace (word.subword _ _ a₁1) with a₁1.
      2:{
        destruct a₁1.
        cbn.
        apply word_ext.
        cbn.
        rewrite Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (wpack U8 2 _) with (wrepr U8 140) by now do 3 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      replace (Hacspec_Lib_Pre.pub_u8
                (is_pure
                   (lift_to_both0
                      (is_pure (lift_to_both0 (Hacspec_Lib_Pre.usize 140)))))) with (Hacspec_Lib_Pre.repr (WS := U8) 140) by reflexivity.

      apply r_ret.
      intros.
      split ; [ | assumption ].
      remove_T_ct.
      Opaque Z.mul.
      clear.
      intros.
      unfold vpshufd1.
      unfold wpshufd1.
      simpl.
      apply word_ext.
      f_equal.
      simpl.
      rewrite Zmod_mod.
      unfold Hacspec_Lib_Pre.shift_right_, wshr, lsr, Hacspec_Lib_Pre.unsigned, wunsigned ; rewrite mkwordK.
      f_equal.

      intros.

      apply r_ret.

      intros.
      destruct H as [? [? [? [? [? [[]]]]]]].
      subst.
      split.
      2:{
        unfold H2.
        exists x. easy.
      }

      apply word_ext.
      unfold wcat_r.

      unfold ".|".
      unfold "_ shift_left _".
      unfold Hacspec_Lib_Pre.shift_left_.
      unfold Hacspec_Lib_Pre.int_or.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.from_uint_size.
      unfold Hacspec_Lib_Pre.usize.
      unfold Hacspec_Lib_Pre.Z_uint_sizeable.
      unfold Hacspec_Lib_Pre.unsigned.
      unfold cast_int.
      unfold lift_to_both0 , lift_to_both, is_pure.
      unfold word.wor, wor.
      unfold wshl, lsl.
      unfold wrepr, wunsigned, urepr, val, word_subType, mkword, toword.
      unfold Hacspec_Lib_Pre.repr.
      unfold Hacspec_Lib_Pre.nat_uint_sizeable.
      unfold Hacspec_Lib_Pre.repr.
      unfold wrepr.
      unfold mkword.
      unfold toword.
      unfold Hacspec_Lib_Pre.unsigned.

      rewrite !Zmod_small.

      all: try easy.
      all: try (apply (num_smaller_if_modulus_smaller) ; easy).

      setoid_rewrite <- Z.lor_assoc.
      setoid_rewrite <- Z.lor_assoc.
      f_equal.

      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.

      rewrite !Z.shiftl_lor.
      f_equal.

      apply (shift_left_4_byte_ok 3) ; easy.
      apply (shift_left_4_byte_ok 2) ; easy.
      apply (shift_left_4_byte_ok 1) ; easy.


      destruct a₁2, a₁3, a₁4, a₁5.
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        repeat apply Z.mul_nonneg_nonneg ; easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
      }
      {
        destruct a₁2, a₁3, a₁4, a₁5.
rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        easy.

        apply (Z_lor_pow2 (toword2 * _)%Z _ nat127.+1).

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
        easy.
      }
      }
      {
        destruct a₁2, a₁3, a₁4, a₁5.
        rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      destruct (ssrbool.elimT (iswordZP _ _) i).
      destruct (ssrbool.elimT (iswordZP _ _) i0).
      destruct (ssrbool.elimT (iswordZP _ _) i1).
      destruct (ssrbool.elimT (iswordZP _ _) i2).
      split.
      {
        apply Z.lor_nonneg. split. easy.
        apply Z.lor_nonneg. split. apply Z.mul_nonneg_nonneg ; easy.
        apply Z.lor_nonneg. split. repeat apply Z.mul_nonneg_nonneg ; easy.
        repeat apply Z.mul_nonneg_nonneg ; easy.
      }
      {
        rewrite <- !Z.mul_assoc.
        rewrite <- !Z.pow_add_r ; try easy.
        simpl.

        apply (Z_lor_pow2 toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply H0 | easy].

        apply (Z_lor_pow2 (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        apply (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in H6  ; [ | easy].
        apply H6.
        easy.

        apply (Z_lor_pow2 (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword1) in H9 ; [ | easy].
        apply H9.
        easy.

        split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword2) in H11 ; [ | easy].
        apply H11.
        easy.
      }
      }
    }
    }
    {
      apply r_ret.
      solve_post_from_pre.
    }
    {
      apply r_ret.
      solve_post_from_pre.
    }
    (* Cleanup *)
    Transparent translate_call.
  Qed.

    Ltac bind_jazz_bind :=    
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?y ?g ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
        let yv := fresh in
        let gv := fresh in
        let av := fresh in
        let fv := fresh in
        set l
        ; set (yv := y)
        ; set (gv := g)
        ; set (av := a)
        ; set (fv := f)
        ; apply (r_bind (ret yv) (av) (fun x => putr l x gv) fv P (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) Q) ; [ | intros ]
        ; subst yv gv av fv ; hnf
    end.

  Lemma key_expand_eq id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
      JKEY_EXPAND id0 rcon rkey temp2
      ≈
      key_expand (wrepr U8 rcon) rkey temp2
      ⦃ fun '(v0, _) '(v1, _) =>
          exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                   /\ (o1, o2) = v1 ⦄.
  Proof.
    set (JKEY_EXPAND _ _ _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    simpl in r.
    subst r.
    rewrite !zero_extend_u.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    do 2 remove_get_in_lhs.
    bind_jazz_hac ; [shelve | ].

    apply better_r_put_lhs.
    do 3 remove_get_in_lhs.

    (* Unfold next call *)
    Transparent translate_call.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?s ≈ _ ⦃ ?Q ⦄ ] ] =>
        let H := fresh in
        set (H := s)
        ; unfold translate_call, translate_call_body in H
        ; simpl in H
        ; unfold tr_app_sopn, sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single in H
        ; simpl in H
        ; subst H
        ; rewrite !zero_extend_u
    end.
    Opaque translate_call.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    remove_get_in_lhs.
    unfold key_combine.

    rewrite !zero_extend_u.

    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.
    
    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.

    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.

    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.

    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.

    setoid_rewrite bind_assoc ; bind_jazz_bind ; [shelve | ].
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.
    rewrite !zero_extend_u.
    apply better_r_put_lhs.
    apply better_r_put_lhs.
    do 2 remove_get_in_lhs.

    apply r_ret.
    intros.
    eexists.
    eexists.
    split.
    reflexivity.
    simpl.
    rewrite !T_ct_id.
    rewrite !zero_extend_u.
    reflexivity.

    Unshelve.
    {
      (* Keygen assist *)
      admit.
    }
    {
      (* wpshufd_128 _ 255 *)
      admit.
    }
    {
      (* wshufps_128 _ 16 *)
      admit.
    }
    {
      (* xor *)
      apply r_ret.
      solve_post_from_pre.
    }

    Transparent translate_call.
Admitted.
