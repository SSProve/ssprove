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
        eapply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) _) ; [ | intros ; unfold pre_to_post ]
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

  Lemma wpshupfd_eq :
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
    bind_jazz_hac.
    (* match goal with *)
    (* | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] => *)
    (*     eapply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) _) ; [ | intros ; unfold pre_to_post ] *)
    (* end. *)

    {

      (* apply forget_precond. *)
      rewrite !zero_extend_u.

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

      do 4 (set (w := wpshufd1 _ _ _) ;
            set (y := fun _ : Hacspec_Lib_Pre.int32 => _) ;
            set (b := vpshufd1 _ _ _);
            let k := fresh in
            match goal with
            | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ _ ⦃ _ ⦄ ] ] => set (k := P)
            end ;
            apply (@r_bind _ _ _ _ (ret w) (prog (is_state b)) (fun w => ret (wrepr U128 (wcat_r [_ ; _ ; _ ; _]))) y _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ k (h0, h1))) ; [ apply r_ret ; intros ; subst w ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K  ;cbn ; rewrite! zero_extend_u ; now rewrite wpshupfd_eq | intros ; subst w y b ; hnf  ]).

      apply r_ret.
      intros.
      destruct H3 as [? [? [? [? []]]]].
      subst.
      subst H.
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
      unfold lift_to_both0 , lift_to_both, is_pure.
      unfold word.wor, wor.
      unfold wshl, lsl.
      unfold wrepr, wunsigned, urepr, val, word_subType, mkword, toword.
      unfold wrepr.
      unfold mkword.
      unfold toword.
      unfold Hacspec_Lib_Pre.unsigned.
      rewrite !Zmod_small.
      rewrite <- Z.lor_assoc.
      rewrite <- Z.lor_assoc.
      f_equal.
      symmetry.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite <- Z.lor_comm.
      rewrite <- Z.lor_assoc.
      rewrite Z.shiftl_lor.
      rewrite Z.shiftl_lor.
      rewrite Z.shiftl_lor.
      rewrite Z.shiftl_lor.
      rewrite Z.shiftl_lor.
      rewrite Z.shiftl_lor.
      f_equal.
      f_equal.
      rewrite Z.lor_0_r.
      reflexivity.

      all: try easy.

      destruct a₁2.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁2.
      split. apply Z.shiftl_nonneg. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      rewrite Z.shiftl_mul_pow2 ; [ | easy].
      rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 96)) toword) in H0 ; [ | easy].
      apply H0.
      
      cbn.
      destruct a₁2.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].


      cbn.
      destruct a₁1.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁1.
      split. apply Z.shiftl_nonneg. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      rewrite Z.shiftl_mul_pow2 ; [ | easy].
      rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 64)) toword) in H0 ; [ | easy].
      eapply Z.lt_trans ; [ apply H0 | easy ].
      
      cbn.
      destruct a₁1.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁0.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁0.
      split. apply Z.shiftl_nonneg. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      rewrite Z.shiftl_mul_pow2 ; [ | easy].
      rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword) in H0 ; [ | easy].
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁0.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

      cbn.
      destruct a₁.
      split. lia.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct i.
      eapply Z.lt_trans ; [ apply H0 | easy ].

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

        assert (forall (x y : Z) (k : nat), (0 <= x < 2 ^ k)%Z -> (0 <= y < 2 ^ k)%Z -> (0 <= Z.lor x y < 2 ^ k)%Z).
        {
          clear.
          intros.

          split.
          apply Z.lor_nonneg ; easy.
          destruct x as [ | x | x ].
          - apply H0.
          - destruct y as [ | y | y ].
            + apply H.
            + simpl in *.
              admit.
            + easy.
          - easy.
        }

        apply (H toword _ nat127.+1). split ; [ easy | ].
        eapply Z.lt_trans ; [apply i | easy].

        apply (H (toword0 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].
        eapply Z.lt_le_trans.
        rewrite (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat (Pos.to_nat 32)) toword0) in i0 ; [ | easy].
        apply i0.
        easy.

        apply (H (toword1 * _)%Z _ nat127.+1). split ; [ apply Z.mul_nonneg_nonneg ; easy | ].

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
  Admitted.

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
