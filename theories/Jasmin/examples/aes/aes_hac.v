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

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality Hacspec_Lib Hacspec_Lib_Pre.
Open Scope hacspec_scope.

Notation call fn := (translate_call _ fn _).

#[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq.

From Hacspec Require Import Hacspec_Lib.


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

  Theorem shiftr_bounds : forall x y z,
      (0 <= y)%Z ->
      (0 <= x < modulus (z+Z.to_nat y))%Z ->
      (0 <= Z.shiftr x y < modulus z)%Z.
  Proof.
    intros.
    rewrite Z.shiftr_div_pow2.
    2:{ cbn. lia. }
    assert (modulus (z + Z.to_nat y) / 2 ^ y = modulus z)%Z.
    {
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id ; [ | assumption].

      rewrite <- Z.pow_sub_r ; [ now rewrite Z.add_simpl_r | lia | ].
      split. assumption.
      lia.
    }
    split.
    - apply Z_div_nonneg_nonneg ; lia.
    - apply (Z.div_lt_upper_bound).
      lia.
      eapply Z.lt_le_trans.
      apply H0.
      rewrite Z.mul_comm.
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite <- Z.pow_add_r.
      cbn.
      rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id.
      lia.
      cbn. lia.
      cbn. lia.
      cbn. lia.
  Qed.

  Theorem shiftl_bounds : forall x y z,
      (le y z) ->
      (0 <= x < modulus (z - y))%Z ->
      (0 <= Z.shiftl x y < modulus z)%Z.
  Proof.
    intros.
    rewrite Z.shiftl_mul_pow2.
    2:{ cbn. lia. }
    assert (modulus (z - y) * 2 ^ y = modulus z)%Z.
    {
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite <- Z.pow_add_r ; [ | lia | cbn ; lia ].
      f_equal.
      rewrite Nat2Z.inj_sub.
      rewrite Z.sub_simpl_r.
      reflexivity.
      apply H.
    }
    split.
    - apply Z.mul_nonneg_nonneg ; lia.
    - rewrite <- H1.
      rewrite <- (Z.mul_lt_mono_pos_r).
      lia.
      cbn.
      lia.
  Qed.

  Theorem shiftr_smaller : forall x y n,
      (0 <= y)%Z ->
      (0 <= x < modulus (n + Z.to_nat y))%Z ->
      Z.shiftr x y = (Z.shiftr x y mod modulus n)%Z.
  Proof.
    intros.
    rewrite Zmod_small.
    2:{
      apply shiftr_bounds.
      - apply H.
      - apply H0.
    }
    reflexivity.
  Qed.

  Notation JVSHUFPS i rkey temp1 temp2 := (trc VSHUFPS i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]).

  Lemma wpshufd1_eq :
    forall (rkey : 'word U128)  (i : nat) (n : nat),
      i < 4 ->
      (* (Z.of_nat n mod modulus nat7.+1 < modulus (2 + 2 * i))%Z -> *)
      wpshufd1 rkey (wrepr U8 n) i =
        is_pure (vpshufd1 rkey (Hacspec_Lib_Pre.repr n) (Hacspec_Lib_Pre.repr i)).
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
    unfold Hacspec_Lib_Pre.usize_shift_right.
    unfold wshr.
    unfold lsr.
    rewrite !mkwordK.
    rewrite <- Zmult_mod.
    setoid_rewrite Zmod_mod.
    rewrite <- Zmult_mod.
    rewrite Z2Nat.id ; [ | destruct i as [ | [ | [ | [] ]]] ; try easy ].
    rewrite (Zmod_small _ (modulus nat127.+1)).
    2:{
      cbn.
      rewrite Zmod_small.
      2:{
        replace (4 mod modulus nat31.+1)%Z with (modulus 2) by reflexivity.
        split.
        - apply Z.mul_nonneg_nonneg ; [ easy | ].
          apply (ssrbool.elimT (iswordZP _ _) (mkword_proof _ _)).
        - replace (modulus nat31.+1) with (32 * modulus (32 - 5))%Z by reflexivity.
          rewrite <- (Z.mul_lt_mono_pos_l) ; [ | easy].
          eapply Z.lt_trans ; [ apply (ssrbool.elimT (iswordZP _ _) (mkword_proof _ _)) ; easy | easy ].
      }
      {
        replace (4 mod modulus nat31.+1)%Z with (modulus 2) by reflexivity.
        split.
        - apply Z.mul_nonneg_nonneg ; [ easy | ].
          apply (ssrbool.elimT (iswordZP _ _) (mkword_proof _ _)).
        - replace (modulus nat127.+1) with (32 * modulus (128 - 5))%Z by reflexivity.
          rewrite <- (Z.mul_lt_mono_pos_l) ; [ | easy].
          eapply Z.lt_trans ; [ apply (ssrbool.elimT (iswordZP _ _) (mkword_proof _ _)) ; easy | easy ].
      }
    }

    symmetry.
    replace ((2 * Z.of_nat i) mod modulus U32)%Z with (2 * Z.of_nat i)%Z by by (destruct i as [ | [ | [ | [] ]]] ; easy).
    rewrite Zmod_small.
    2:{
      cbn.
      replace (4 mod modulus nat31.+1)%Z with (modulus 2) by reflexivity.
      split.
      - apply Z.mul_nonneg_nonneg  ; [ easy | ].
        apply Z_mod_nonneg_nonneg ; [ | easy ].
        apply Z_mod_nonneg_nonneg ; [ | easy ].
        apply Z.shiftr_nonneg.
        apply Z_mod_nonneg_nonneg ; [ | easy ].
        apply Z_mod_nonneg_nonneg ; [ | easy ].
        lia.
      - replace (modulus nat31.+1)%Z with (32 * modulus (32 - 5))%Z at 3 by reflexivity.
        apply Z.mul_lt_mono_pos_l ; [ easy | ].
        eapply Z.lt_trans.
        apply Z.mod_pos_bound.
        easy.
        easy.
    }

    cbn.
    f_equal.
    f_equal.
    rewrite Zmod_small.
    {
      symmetry.
      rewrite Zmod_small.
      {
        symmetry.
        f_equal.
        {
          rewrite Zmod_small ; [ reflexivity | ].
          split ; [ apply Z_mod_nonneg_nonneg ; [ lia | easy ] | ].
          eapply Z.lt_trans.
          apply Z.mod_pos_bound.
          destruct i as [ | [ | [ | [] ]]] ; easy.
          easy.
        }
        destruct i as [ | [ | [ | [] ]]] ; easy.
      }
      apply shiftr_bounds. lia.
      split.
      apply Z_mod_nonneg_nonneg.
      lia.
      easy.

      eapply Z.lt_le_trans.
      apply Z.mod_pos_bound.
      destruct i as [ | [ | [ | [] ]]] ; easy.
      rewrite modulusD.
      destruct i as [ | [ | [ | [] ]]] ; easy.
    }
    apply shiftr_bounds. lia.
    rewrite Zmod_small.
    {
      split.
      apply Z_mod_nonneg_nonneg.
      lia.
      easy.

      eapply Z.lt_le_trans.
      apply Z.mod_pos_bound.
      destruct i as [ | [ | [ | [] ]]] ; easy.
      destruct i as [ | [ | [ | [] ]]] ; easy.
    }
    {
      split.
      apply Z_mod_nonneg_nonneg.
      lia.
      easy.

      eapply Z.lt_le_trans.
      apply Z.mod_pos_bound.
      destruct i as [ | [ | [ | [] ]]] ; easy.
      destruct i as [ | [ | [ | [] ]]] ; easy.
    }
    Transparent Z.mul.
    Transparent Nat.mul.
  Qed.

  Lemma wpshufd1_eq_state :
    forall {H} (rkey : 'word U128)  (i n : nat),
      i < 4 ->
      ⊢ ⦃ H ⦄
          ret (wpshufd1 rkey (wrepr U8 n) i) ≈
          is_state (vpshufd1 rkey (Hacspec_Lib_Pre.repr n) (Hacspec_Lib_Pre.repr i))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    rewrite (wpshufd1_eq _ i n) ; [ | apply H0 ].
    now apply r_ret.
  Qed.

  Ltac match_wpshufd1_vpshufd1 i :=
    (let w := fresh in
     let y := fresh in
     let b := fresh in
     set (w := wpshufd1 _ _ i) ;
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

  Ltac solve_wpshufd1_vpshufd1 i n :=
    match_wpshufd1_vpshufd1 i ; [now apply (wpshufd1_eq_state _ i n) | intros ].

  Lemma shift_left_4_byte_ok :
    (forall i (a : 'word U32),
        i < 4 ->
        (0 <= Z.shiftl (wunsigned a) (Z.of_nat (i * 32)) <
           modulus (wsize_size_minus_1 U128).+1)%Z).
  Proof.
    clear.
    destruct a.
    unfold wunsigned, urepr, val, word_subType, word.toword.
    apply (ssrbool.elimT (iswordZP _ _)) in i0.
    split. apply Z.shiftl_nonneg. lia.
    destruct i0.
    rewrite Z.shiftl_mul_pow2 ; [ | lia].
    eapply Z.lt_le_trans.
    rewrite <- (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat _) toword) ; [ | lia ].
    apply H1.
    destruct i as [ | [ | [ | [ | []] ]] ] ; easy.
  Qed.

  Lemma num_smaller_if_modulus_lte : (forall {WS} (x : 'word WS) z, (modulus WS <= z)%Z -> (0 <= x < z)%Z).
  Proof.
    clear.
    cbn.
    intros.
    destruct x.
    pose (ssrbool.elimT (iswordZP _ _) i).
    split. easy.
    unfold word.toword.
    destruct a.
    eapply Z.lt_le_trans ; [ apply H1 | apply H].
  Qed.

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

  Lemma wpshufd_128_eq_state :
    forall {H} (rkey : 'word U128) (n : nat),
      ⊢ ⦃ H ⦄
          ret (wpshufd_128 rkey n) ≈
          is_state (vpshufd rkey (Hacspec_Lib_Pre.repr n))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    unfold wpshufd_128.
    unfold vpshufd.
    unfold wpshufd_128.
    unfold iota.
    unfold map.
    (* set (wpshufd1 _ _ _). *)
    (* set (wpshufd1 _ _ _). *)
    (* set (wpshufd1 _ _ _). *)
    unfold vpshufd.

    solve_wpshufd1_vpshufd1 0 n.
    solve_wpshufd1_vpshufd1 1 n.
    solve_wpshufd1_vpshufd1 2 n.
    solve_wpshufd1_vpshufd1 3 n.

    apply r_ret.
    intros ? ? [? [? [? []]]].
    subst.
    subst H4.
    split ; [ clear | assumption ].

    apply word_ext.

    unfold wcat_r.

    Opaque Z.shiftl.
    simpl.
    Transparent Z.shiftl.

    rewrite Zmod_small.
    2: {
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      replace (int_to_Z (Posz 32)) with 32%Z by reflexivity.

      repeat apply (Z_lor_pow2 _ _ (32 + 32 + 32 + 32)) ; replace (2 ^ (int_to_Z (Posz(32 + 32 + 32 + 32))))%Z with (2 ^ 32 * 2 ^ 32 * 2 ^ 32 * 2 ^ 32)%Z by reflexivity.
      all: split ; [ destruct a₁, a₁0, a₁1, a₁2 ; unfold urepr ; simpl ; apply (ssrbool.elimT (iswordZP _ _)) in i, i0, i1, i2 ; repeat (apply Z.lor_nonneg ; split ; [ repeat apply Z.mul_nonneg_nonneg ; easy | ]) ; repeat apply Z.mul_nonneg_nonneg ; easy | ].
      all: repeat (apply -> (@Z.mul_lt_mono_pos_r (2 ^ 32)) ; [ | easy ]) ; apply (@num_smaller_if_modulus_lte U32) ; easy.
    }

    rewrite Zmod_small ; [ | apply num_smaller_if_modulus_lte ; easy].
    rewrite Zmod_small.
    2:{
      setoid_rewrite Zmod_small ; [  | apply num_smaller_if_modulus_lte ; easy | apply num_smaller_if_modulus_lte ; easy ].
      apply (shift_left_4_byte_ok 1) ; easy.
    }
    rewrite Zmod_small.
    2:{
      setoid_rewrite Zmod_small ; try (apply num_smaller_if_modulus_lte ; easy).
      apply (shift_left_4_byte_ok 2) ; easy.
    }
    rewrite Zmod_small.
    2:{
      setoid_rewrite Zmod_small ; try (apply num_smaller_if_modulus_lte ; easy).
      apply (shift_left_4_byte_ok 3) ; easy.
    }
    setoid_rewrite Zmod_small ; try (apply num_smaller_if_modulus_lte ; easy).

    rewrite !Z.shiftl_lor.
    rewrite !Z.shiftl_mul_pow2 ; try easy.
    rewrite !Z.mul_0_l.
    rewrite Z.lor_0_r.
    rewrite <- !Z.mul_assoc.
    rewrite <- !Z.pow_add_r ; try easy.
    now rewrite <- !Z.lor_assoc.
  Qed.

  Lemma wshufps_128_eq_state :
    forall {H} (a b : 'word U128) (n : nat),
      ⊢ ⦃ H ⦄
          ret (wshufps_128 (wrepr U8 n) a b) ≈
          is_state (vshufps a b (Hacspec_Lib_Pre.repr n))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    unfold wshufps_128.
    unfold vshufps.
    unfold iota.
    unfold map.
    (* set (wpshufd1 _ _ _). *)
    (* set (wpshufd1 _ _ _). *)
    (* set (wpshufd1 _ _ _). *)
    unfold vpshufd.

    solve_wpshufd1_vpshufd1 0 n.
    solve_wpshufd1_vpshufd1 1 n.
    solve_wpshufd1_vpshufd1 2 n.
    solve_wpshufd1_vpshufd1 3 n.
    intros.
    apply r_ret.
    intros ? ? [? [? [? []]]].
    subst.
    subst H4.
    split ; [ clear | assumption ].

    apply word_ext.

    unfold wcat_r.

    Opaque Z.shiftl.
    simpl.
    Transparent Z.shiftl.

    rewrite !mkwordK.

    rewrite Zmod_small.
    2: {
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_mul_pow2 ; try easy.
      rewrite !Z.mul_0_l.
      rewrite Z.lor_0_r.
      repeat apply (Z_lor_pow2 _ _ (32 + 32 + 32 + 32)) ; replace (2 ^ (int_to_Z (Posz(32 + 32 + 32 + 32))))%Z with (2 ^ 32 * 2 ^ 32 * 2 ^ 32 * 2 ^ 32)%Z by reflexivity.
      all: split ; [ destruct a₁, a₁0, a₁1, a₁2 ; unfold urepr ; simpl ; apply (ssrbool.elimT (iswordZP _ _)) in i, i0, i1, i2 ; repeat (apply Z.lor_nonneg ; split ; [ repeat apply Z.mul_nonneg_nonneg ; easy | ]) ; repeat apply Z.mul_nonneg_nonneg ; easy | ].
      all: repeat (apply -> (@Z.mul_lt_mono_pos_r (2 ^ 32)) ; [ | easy ]) ; apply (@num_smaller_if_modulus_lte U32) ; easy.
    }

    rewrite !Zmod_small.
    all: try apply (@num_smaller_if_modulus_lte U32).
    all: try easy.
    2: apply (shiftl_bounds _ 96 128) ; [ lia |  cbn ; apply (@num_smaller_if_modulus_lte U32) ; easy ].
    2: apply (shiftl_bounds _ 64 128) ; [ lia |  cbn ; apply (@num_smaller_if_modulus_lte U32) ; easy ].
    2: apply (shiftl_bounds _ 32 128) ; [ lia |  cbn ; apply (@num_smaller_if_modulus_lte U32) ; easy ].

    rewrite !Z.shiftl_lor.
    rewrite !Z.shiftl_mul_pow2 ; try easy.
    rewrite !Z.mul_0_l.
    rewrite Z.lor_0_r.
    rewrite <- !Z.mul_assoc.
    rewrite <- !Z.pow_add_r ; try easy.
    rewrite <- !Z.lor_assoc.
    simpl.
    reflexivity.
  Qed.

  Definition pdisj (P : precond) (s_id : p_id) (rhs : {fset Location}) :=
    (forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
      (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

  Lemma key_combined_eq id0 rcon rkey temp2 (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        JKEY_COMBINE id0 rcon rkey temp2
        ≈
        is_state (key_combine rcon rkey temp2)
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                      /\ (o1, o2) = v1) /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JKEY_COMBINE _ _ _ _).
    unfold JKEY_COMBINE in r.
    unfold get_translated_static_fun in r.
    simpl in r.
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
    split.
    {
      destruct_pre.
      eexists.
      eexists.
      split ; [ reflexivity | ].
      cbn.
      rewrite !zero_extend_u.
      reflexivity.
    }
    {
      destruct_pre.
      destruct H_pdisj.
      repeat eapply H ; try easy.
    }

    Unshelve.
    {
      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      replace (toword _) with (255)%Z by (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).

      apply (wpshufd_128_eq_state rkey 255).
    }
    {
      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

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

      unfold lift2_vec.

      unfold map2.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.

      replace (word.subword _ _ _) with temp2.
      2:{
        destruct temp2.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }
      replace (word.subword _ _ _) with rcon.
      2:{
        destruct rcon.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (truncate_chWord _ _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).

      unfold make_vec.
      unfold wcat_r.
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.

      unfold mkword.

      epose (wshufps_128_eq_state temp2 rcon 16).
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.
      unfold prog.

      rewrite <- bind_ret.
      set (ret _).
      pattern (wshufps_128 (wrepr U8 16) temp2 rcon) in r0.
      subst r0.

      eapply (@r_bind _ _ _ _ (ret (wshufps_128 (wrepr U8 16) temp2 rcon))).
      apply r.
      intros.
      apply r_ret.
      intros ? ? [].
      subst.
      split.
      destruct a₁0. cbn. unfold wrepr. cbn. apply word_ext.
      rewrite Zmod_small.
      reflexivity.
      apply (ssrbool.elimT (iswordZP _ _)).
      apply i.
      apply H0.
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

      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

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

      unfold lift2_vec.

      unfold map2.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.

      replace (word.subword _ _ _) with a₁0.
      2:{
        destruct a₁0.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }
      replace (word.subword _ _ _) with a₁1.
      2:{
        destruct a₁1.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (truncate_chWord _ _) with (wrepr U8 140) by now repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).

      rewrite <- bind_ret.
      set (ret _).
      pattern (wshufps_128 (wrepr U8 140) a₁0 a₁1) in r.
      subst r.
      eapply (@r_bind _ _ _ _ (ret (wshufps_128 (wrepr U8 140) a₁0 a₁1))).
      apply (wshufps_128_eq_state a₁0 a₁1 140).

      intros.
      apply r_ret.
      intros ? ? [].
      subst.
      split.
      unfold make_vec.
      cbn.
      rewrite Z.lor_0_r.
      destruct a₁2. cbn. unfold wrepr. cbn. apply word_ext.
      rewrite Zmod_small.
      cbn.
      reflexivity.
      apply (ssrbool.elimT (iswordZP _ _)).
      apply i.
      apply H0.
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

  Ltac solve_in :=
    repeat match goal with
           | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
           | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
           end.

  Ltac pdisj_apply h :=
    lazymatch goal with
    | |- ?pre (set_heap _ _ _, set_heap _ _ _) => eapply h; [ solve_in | pdisj_apply h ]
    | |- ?pre (set_heap _ _ _, _) =>
        eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
    | |- _ => try assumption
    end.

  Theorem rpre_hypothesis_rule' :
    ∀ {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
          pre (s₀, s₁) → ⊢ ⦃ λ '(s₀', s₁'), s₀' = s₀ ∧ s₁' = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule.
    intros s0 s1 H. eapply rpre_weaken_rule.
    eapply h.
    eassumption.
    easy.
  Qed.

  Theorem rpre_weak_hypothesis_rule' :
    ∀ {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
          pre (s₀, s₁) → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule'.
    intros. eapply rpre_weaken_rule.
    eapply h. eassumption.
    intros s0' s1' [H0 H1].
    subst.
    assumption.
  Qed.

  Corollary better_r_put_rhs : forall {A B : choice.Choice.type} (ℓ : Location)
                                 (v : choice.Choice.sort (Value (projT1 ℓ))) (r₀ : raw_code A)
                                 (r₁ : raw_code B) (pre : precond)
                                 (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
      ⊢ ⦃ set_rhs ℓ v pre ⦄ r₀ ≈ r₁ ⦃ post ⦄ ->
      ⊢ ⦃ pre ⦄ r₀ ≈ #put ℓ := v ;; r₁ ⦃ post ⦄.
  Proof.
    intros.
    eapply rpre_hypothesis_rule.
    intros.
    eapply rpre_weaken_rule.
    apply r_put_rhs.
    apply H.
    intuition.
    Unshelve.
    subst.
    intuition.
  Qed.

  Check word.subword (1 * U32)%nat U32.
  (* let x1 := subword (1 * U32) U32 v1 in *)
  (* let x1 = (v1 >> 32) % (1_u128 << 32); *)
  Lemma subword_eq (n : int128) (i : nat):
    (i < 4) ->
    word.subword (i * U32)%nat U32 n =
      @repr U32 (unsigned (((lift_to_both0 n) shift_right (lift_to_both0 (usize (i * 32)))) .% ((
            lift_to_both0 (@repr U128 1)) shift_left (lift_to_both0 (usize 32))))).
  Proof.
    intros.
    apply word_ext.
    simpl.
    unfold Hacspec_Lib_Pre.int_mod.
    replace (Hacspec_Lib_Pre.shift_left_ (repr 1) (repr 32)) with (@repr U128 (modulus 32)) by reflexivity.
    setoid_rewrite wunsigned_repr.
    replace (wunsigned (repr (modulus 32))) with (modulus 32) by reflexivity.
    replace (modulus (wsize_size_minus_1 U128).+1) with (modulus 96 * modulus 32)%Z by reflexivity.
    rewrite mod_pq_mod_q.
    rewrite Zmod_mod.
    f_equal.
    do 4 (destruct i ; [easy | ]) ; easy.
    easy.
    easy.
  Qed.

  Lemma nat_to_be_range_is_subword : forall {WS : wsize.wsize} {WS_inp : wsize.wsize} (n : @int WS_inp) i `{H_WS : WS <= WS_inp} , (@repr WS (nat_be_range WS (toword n) i) = word.subword (i * WS) WS n).
  Proof.
    intros.
    apply word_ext.
    cbn.
    unfold nat_be_range.
    replace (_ ^ WS)%Z with (modulus WS)%Z by (destruct WS ; reflexivity).
    replace (modulus WS_inp) with (modulus (WS_inp - WS) * modulus WS)%Z by (destruct WS , WS_inp ; easy).
    rewrite mod_pq_mod_q ; [ | easy | easy ].
    rewrite !Zmod_mod.
    f_equal.
    rewrite <- Z.shiftr_div_pow2 ; [  | lia ].
    rewrite Nat2Z.inj_mul.
    f_equal. now zify.
  Qed.
  
  Lemma sbox_eq :
    (forall n i, (i < 4)%nat ->
            @Hacspec_Lib_Pre.array_index int8 (@int_default U8)
         (uint_size_to_nat
            (Z_to_uint_size
               (Z.modulo (Zpos (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))
                  (modulus (S nat31))))) sbox_v U8
         (@Hacspec_Lib_Pre.array_index int8 (@int_default U8)
            (S (S (S (S O))))
            (Hacspec_Lib_Pre.u32_to_be_bytes n) U32
            (@repr U32 i)) = waes.Sbox (word.subword (i * U8) U8 n)).
  Proof.
  Admitted.
    (* intros. *)

  (*   simpl. *)
  (*   unfold Hacspec_Lib_Pre.u32_to_be_bytes. *)
  (*   unfold to_be_bytes. *)
  (*   rewrite !eq_rect_K. *)
  (*   unfold Hacspec_Lib_Pre.array_index at 2. *)
  (*   assert (H0 : forall (n : int32) i, i < 4 -> Hacspec_Lib_Pre.array_index (WS := U8) sbox_v (repr (nat_be_range 8 n i)) = waes.Sbox (word.subword (i * U8) U8 n)). *)
  (*   2: do 4 (destruct i ; [ simpl ; apply H0 ; apply H | ]) ; discriminate. *)
  (*   clear ; intros. *)
  (*   rewrite (nat_to_be_range_is_subword (WS := U8) n i (H_WS := ltac:(easy))). *)

  (*   destruct (word.subword (i * U8) U8 n). *)
  (*   destruct toword. *)
  (*   - reflexivity. *)
  (*   - do 8 (destruct p ; [ | | shelve ]). *)
  (*     all: destruct p ; easy. *)
  (*     Unshelve. *)
  (*     all: reflexivity. *)
  (*   - easy. *)
  (* Qed. *)

  Lemma array_to_list_upd_spec : (forall A WS n (a : nseq A n) (i : @int WS) x,
                                array_to_list (Hacspec_Lib_Pre.array_upd a i x) =
                                  set_nth x (array_to_list a) (Z.to_nat (unsigned i)) x).
  Proof.
  Admitted.
    
  
  Lemma SubWord_eq id0 (n : int32) pre :
    (pdisj pre id0 (CEfset ([res_238_loc]))) ->
    ⊢ ⦃ pre ⦄
    ret (waes.SubWord n) ≈
      subword n
     ⦃ fun '(v0, h0) '(v1, h1) => (v0 = v1) /\ pre (h0, h1) ⦄.
  Proof.
    intros.
    unfold waes.SubWord.
    unfold split_vec.
    replace (U32 %/ U8 + U32 %% U8) with 4 by reflexivity.

    unfold subword.
    setoid_rewrite bind_rewrite.
    apply better_r_put_rhs.

    (* Unroll for loop *)
    unfold let_both at 1, is_state at 1, prog.
    setoid_rewrite <- foldi__move_S.
    replace (prog (lift_to_both0 (usize _) .+ one)) with (ret (usize 1)) by reflexivity.
    unfold bind at 3.

    setoid_rewrite <- foldi__move_S.
    replace (prog (is_state (usize 1 .+ one))) with (ret (usize 2)) by reflexivity.
    unfold bind at 3.

    setoid_rewrite <- foldi__move_S.
    replace (prog (is_state (usize 2 .+ one))) with (ret (usize 3)) by reflexivity.
    unfold bind at 3.

    setoid_rewrite <- foldi__move_S.
    replace (prog (is_state (usize 3 .+ one))) with (ret (usize 4)) by reflexivity.
    unfold bind at 3.
    unfold foldi_.

    rewrite bind_ret.
    setoid_rewrite bind_ret.
    rewrite bind_rewrite.

    rewrite !ct_T_id.
    rewrite !T_ct_id.

    apply r_ret.
    intros.
    destruct_pre.
    split.
    2:{
      cbn.

      apply H.
      setoid_rewrite <- fset1E.
      apply (ssrbool.introT (fset1P _ _)).
      reflexivity.
      apply H2.
    }
    
    unfold repr, unsigned.
    rewrite <- !sbox_eq ; try easy.

    unfold Hacspec_Lib_Pre.u32_from_be_bytes, from_be_bytes.
    unfold from_be_bytes_fold_fun.

    set (Hacspec_Lib_Pre.array_upd _ _ _) at 2.

    set ([ _ ; _ ; _ ; _ ]).
    replace (make_vec U32 l) with (4, make_vec U32 l).2 by reflexivity.
    Set Printing Coercions.
    unfold T_ct.
    unfold Datatypes.id.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold Logic.eq_sym.
    unfold ChoiceEq.
    unfold int32, int. unfold Hacspec_Lib_Pre.int_obligation_1.
    apply f_equal.

    do 4 rewrite array_to_list_upd_spec.

    replace (Z.to_nat (unsigned (wrepr U32 0))) with 0 by reflexivity.
    replace (Z.to_nat (unsigned (wrepr U32 1))) with 1 by reflexivity.
    replace (Z.to_nat (unsigned (wrepr U32 2))) with 2 by reflexivity.
    replace (Z.to_nat (unsigned (wrepr U32 3))) with 3 by reflexivity.

    subst l.

    unfold Hacspec_Lib_Pre.array_new_.
    simpl.
    rewrite eq_rect_K.
    set (getm _ _).
    cbn in o.
    subst o.
    hnf.
    set (_ ++ _).
    cbn in l.
    subst l.
    hnf.

    unfold fold_right.
    unfold set_nth.
    rewrite !nat_N_Z.
    unfold int8_to_nat, uint_size_to_nat, from_uint_size, nat_uint_sizeable, Z_to_uint_size.
    unfold unsigned, repr.
    unfold Hacspec_Lib_Pre.int_add, add_word.
    unfold make_vec.
    unfold wcat_r.
    unfold wunsigned, wrepr, mkword, urepr, val, word_subType.

    
    
    set (Hacspec_Lib_Pre.array_index _ _).
    set (Hacspec_Lib_Pre.array_index _ _).
    set (Hacspec_Lib_Pre.array_index _ _).
    set (Hacspec_Lib_Pre.array_index _ _).
    
    unfold toword in |- *.

    rewrite !Z2Nat.id.
    
    2: {
      destruct t3.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      rewrite Zmod_small ; [ lia | ].
      destruct i.
      split ; [ assumption | eapply Z.lt_trans ; [ apply H3 | easy ] ].
    }
    2: {
      destruct t2.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      rewrite Zmod_small ; [ lia | ].
      destruct i.
      split ; [ assumption | eapply Z.lt_trans ; [ apply H3 | easy ] ].
    }
    2: {
      destruct t1.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      rewrite Zmod_small ; [ lia | ].
      destruct i.
      split ; [ assumption | eapply Z.lt_trans ; [ apply H3 | easy ] ].
    }
    2: {
      destruct t0.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      rewrite Zmod_small ; [ lia | ].
      destruct i.
      split ; [ assumption | eapply Z.lt_trans ; [ apply H3 | easy ] ].
    }

    unfold Z.of_nat.

    f_equal.
    apply word_ext.

    Unset Printing Coercions. 

    (* rewrite !Zmod_small. *)
    rewrite !Z.shiftl_mul_pow2 ; try easy.

    simpl.
    cbn.

    replace 1%Z with (1 mod modulus nat31.+1)%Z by reflexivity.
    replace 256%Z with (256 mod modulus nat31.+1)%Z by reflexivity.
    replace 65536%Z with (65536 mod modulus nat31.+1)%Z by reflexivity.
    replace 16777216%Z with (16777216 mod modulus nat31.+1)%Z by reflexivity.
    rewrite <- !Zmult_mod.
    rewrite !Zmod_mod.
    rewrite <- !Z.add_mod.

    rewrite <- Z.add_assoc.
    rewrite (Z.add_mod ((_ * 1 + _ * 256) mod _)).
    rewrite !Zmod_mod.
    rewrite <- Z.add_mod.

    rewrite Z.add_comm.
    rewrite <- Z.add_assoc.
    rewrite (Z.add_mod ((_ * 65536) mod _)).
    rewrite !Zmod_mod.
    rewrite <- Z.add_mod.

    rewrite Z.add_comm.
    rewrite <- Z.add_assoc.
    rewrite Z.add_comm.
    rewrite <- Z.add_assoc.
    rewrite <- Z.add_assoc.

    simpl.
    cbn.

    f_equal.

    all: try easy.

    (* apply Z.bits_inj. *)
    (* intros i. *)

    assert (H_lor_add : forall (a b : Z) (k : nat), (0 <= a < modulus k)%Z -> (a + Z.shiftl b k)%Z = Z.lor a (Z.shiftl b k)).
    {
      clear ; intros.

      assert (Z.land a (Z.shiftl b k) = 0).
      {
        apply Z.bits_inj_iff.
        intros i.
        rewrite Z.land_spec.
        rewrite Z.bits_0.

        destruct (0 <=? i)%Z eqn:i0.
        {
          destruct (i <? k)%Z eqn:ik.
          - rewrite (Z.shiftl_spec_low b k i).
            lia.
            now apply (ssrbool.elimT (ZltP _ _)) in ik.
          -
            apply (ssrbool.elimT (ZleP _ _)) in i0.
            apply Z.ltb_ge in ik.

            rewrite (proj2 (Z.testbit_false _ _ i0)).
            lia.

            rewrite Z.div_small.
            reflexivity.

            split. easy.
            eapply Z.lt_le_trans ; [  |  ].
            apply H.

            rewrite modulusZE.
            apply (Z.pow_le_mono_r 2 k i).
            reflexivity.
            assumption.
        }
        {
          destruct i ; easy.
        }
      }
      
      rewrite <- Z.lxor_lor ; [ | apply H0 ].
      rewrite <- Z.add_nocarry_lxor ; [ | apply H0 ].
      reflexivity.
    }
    
    replace 1%Z with (modulus 0)%Z by reflexivity.
    replace 256%Z with (modulus 8)%Z by reflexivity.
    replace 65536%Z with  (modulus 16)%Z by reflexivity.
    replace 16777216%Z with  (modulus 24)%Z by reflexivity.

    rewrite !modulusZE.
    rewrite <- !Z.shiftl_mul_pow2 ; try easy.

    rewrite !Z.add_assoc.
    rewrite !Z.shiftl_0_r.
    rewrite Z.lor_0_r.

    rewrite !H_lor_add.

    2, 4, 6, 8: apply (ssrbool.elimT (iswordZP _ _)) ; now destruct t0.
    2: {
      destruct t0.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct t1.
      apply (ssrbool.elimT (iswordZP _ _)) in i0.
      split.
      - apply Z.lor_nonneg. split. lia.
        apply Z.shiftl_nonneg. lia.
      - rewrite modulusZE.
        apply Z_lor_pow2.
        split. lia.
        eapply Z.lt_trans.
        apply i.
        easy.
        
        rewrite <- modulusZE.
        apply shiftl_bounds.
        lia.
        apply i0.
      }
    2: {
      destruct t0.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct t1.
      apply (ssrbool.elimT (iswordZP _ _)) in i0.
      destruct t2.
      apply (ssrbool.elimT (iswordZP _ _)) in i1.
      split.
      - apply Z.lor_nonneg. split.
        apply Z.lor_nonneg. split. lia.
        apply Z.shiftl_nonneg. lia.
        apply Z.shiftl_nonneg. lia.
      - rewrite modulusZE.
        apply Z_lor_pow2.
        split. apply Z.lor_nonneg. split. lia. apply Z.shiftl_nonneg. lia.
        apply Z_lor_pow2.
        split. lia.
        eapply Z.lt_trans.
        apply i.
        easy.
        
        rewrite <- modulusZE.
        apply shiftl_bounds.
        lia.
        split. lia.
        eapply Z.lt_trans.
        apply i0.
        easy.

        rewrite <- modulusZE.
        apply shiftl_bounds.
        lia.
        split. lia.
        eapply Z.lt_le_trans.
        apply i1.
        easy.
    }
    2:{
      destruct t0.
      apply (ssrbool.elimT (iswordZP _ _)) in i.
      destruct t1.
      apply (ssrbool.elimT (iswordZP _ _)) in i0.
      split.
      - apply Z.lor_nonneg. split. lia.
        apply Z.shiftl_nonneg. lia.
      - rewrite modulusZE.
        apply Z_lor_pow2.
        split. lia.
        eapply Z.lt_trans.
        apply i.
        easy.
        
        rewrite <- modulusZE.
        apply shiftl_bounds.
        lia.
        split. lia.
        eapply Z.lt_le_trans.
        apply i0.
        easy.
    }

    
    rewrite !Z.shiftl_lor.
    rewrite <- !Z.lor_assoc.
    rewrite !Z.shiftl_shiftl.
        
    reflexivity.
    all: try easy.
  Qed.

  Ltac match_pattern_and_bind_repr p :=
    unfold let_both at 1, is_state at 1, prog ;
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ _ ⦃ ?Q ⦄ ] ] =>
        let Hx := fresh in
        set (Hx := x) ;
        pattern p in Hx ;
        subst Hx ;

        (* Match bind and apply *)
        match goal with
        | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
            let av := fresh in
            let fv := fresh in
            set (av := a)
            ; set (fv := f)
            ; eapply (r_bind (ret p) av _ fv P (fun '(v0, h0) '(v1, h1) => v0 = repr v1 /\ P (h0, h1)) Q) (* (v0 = v1) *)
            ; subst av fv ; hnf ; [ | intros ; apply rpre_hypothesis_rule' ; intros ? ? [] ; apply rpre_weaken_rule with (pre := fun '(s₀, s₁) => P (s₀, s₁))
              ]
        end
    end.

  Ltac match_pattern_and_bind p :=
    unfold let_both at 1, is_state at 1, prog ;
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ _ ⦃ ?Q ⦄ ] ] =>
        let Hx := fresh in
        set (Hx := x) ;
        pattern p in Hx ;
        subst Hx ;

        (* Match bind and apply *)
        match goal with
        | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
            let av := fresh in
            let fv := fresh in
            set (av := a)
            ; set (fv := f)
            ; eapply (r_bind (ret p) av _ fv P (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) Q) (* (v0 = v1) *)
            ; subst av fv ; hnf ; [ | intros ; apply rpre_hypothesis_rule' ; intros ? ? [] ; apply rpre_weaken_rule with (pre := fun '(s₀, s₁) => P (s₀, s₁))
              ]
        end
    end.

  Lemma keygen_assist_eq id0 (v1 : 'word U128) (v2 : 'word U8) (pre : precond) :
    (pdisj pre id0 (CEfset [res_238_loc])) ->
    ⊢ ⦃ pre ⦄
        ret (waes.wAESKEYGENASSIST v1 v2)
        (* (tr_app_sopn_tuple (w2_ty U128 U8) *)
        (*                    (sopn_sem (Oasm (BaseOp (None, VAESKEYGENASSIST)))) *)
        (*                    [totce v1; totce v2]) *)
        ≈
        prog (is_state (aeskeygenassist v1 v2))
        ⦃ fun '(v0, h0) '(v1, h1) => (v0 = v1) /\ pre (h0, h1) ⦄.
  Proof.
    intros.

    (* let rcon := zero_extend U32 v2 in *)
    (* let x1 := subword (1 * U32) U32 v1 in *)
    (* let x3 := subword (3 * U32) U32 v1 in *)
    (* let y0 := SubWord x1 in *)
    (* let y1 := wxor (wror (SubWord x1) 1) rcon in *)
    (* let y2 := SubWord x3 in *)
    (* let y3 := wxor (wror (SubWord x3) 1) rcon in *)
    (* make_vec U128 [:: y0; y1; y2; y3]. *)


    (* let x1 = (v1 >> 32) % (1_u128 << 32); *)
    (* let x3 = (v1 >> 96) % (1_u128 << 32); *)
    (* let y0 = subword(x1 as u32); *)
    (* let y1 = ror(subword(x1 as u32), 1) ^ (v2 as u32); *)
    (* let y2 = subword(x3 as u32); *)
    (* let y3 = ror(subword(x3 as u32), 1) ^ (v2 as u32); *)
    (* (y0 as u128) | ((y1 as u128) << 32) | ((y2 as u128) << 64) | (((y3) as u128) << 96) *)


    unfold waes.wAESKEYGENASSIST.

    unfold make_vec.
    unfold wcat_r.
    rewrite Z.shiftl_0_l.
    rewrite Z.lor_0_r.

    unfold aeskeygenassist.

    (* Unfold let both and match *)
    (* unfold let_both at 1, is_state at 1, prog. *)
    match_pattern_and_bind_repr (@word.subword (wsize_size_minus_1 U128).+1 (1 * U32) U32 v1).
    {
      apply r_ret.
      intros.
      rewrite (subword_eq v1) ; [ | easy ].
      split. reflexivity. assumption. 
    }
      

    (* unfold let_both at 1, is_state at 1, prog. *)
    match_pattern_and_bind_repr (@word.subword (wsize_size_minus_1 U128).+1 (3 * U32) U32 v1).
    {
      apply r_ret.
      intros.
      rewrite (subword_eq v1) ; [ | easy ].
      split ; easy.
    }
    
    unfold let_both at 1, is_state at 1, prog.
    match_pattern_and_bind (waes.SubWord a₀).
    {
      subst.
      apply (SubWord_eq id0 (repr a₁) (λ '(s₀1, s₁1), pre (s₀1, s₁1))).
      destruct_pre.
      hnf.
      eapply H.
    }

    match_pattern_and_bind (word.wxor (wror (sz:=U32) a₀1 1) (zero_extend U32 (sz':=U8) v2)).
    {
      subst.
      apply r_ret.
      intros.
      split.
      - (* TODO *) admit.
      - apply H0.
    }

    match_pattern_and_bind (waes.SubWord a₀0).
    {
      subst.
      apply (SubWord_eq id0 (repr a₁0) (λ '(s₀1, s₁1), pre (s₀1, s₁1))).
      destruct_pre.
      hnf.
      eapply H.
    }
    
    match_pattern_and_bind (word.wxor (wror (sz:=U32) a₀3 1)
                                  (zero_extend U32 (sz':=U8) v2)).
    {
      subst.
      apply r_ret.
      intros.
      split.
      - (* TODO *) admit.
      - apply H0.
    }    

    apply r_ret.
    intros.
    subst.
    all: try (intros ? ? [] ; subst ; assumption).
    split.
    - set (Hacspec_Lib_Pre.int_or _ _).
      cbn in t.
      subst t.

      apply word_ext.
      rewrite <- !Z.lor_assoc.
      rewrite !Z.shiftl_lor.
      rewrite !Z.shiftl_shiftl.
      rewrite !Zmod_small.
      f_equal.

      all: admit.
    - apply H12.
  Admitted.

  Lemma key_expand_eq id0 rcon rkey temp2  (pre : precond) :
    (pdisj pre id0 (CEfset [res_238_loc])) ->
    ⊢ ⦃ pre ⦄
        JKEY_EXPAND id0 rcon rkey temp2
        ≈
        key_expand (wrepr U8 rcon) rkey temp2
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                      /\ (o1, o2) = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JKEY_EXPAND _ _ _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    unfold JKEY_EXPAND in r.
    cbn in r.
    subst r.
    rewrite !zero_extend_u.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    do 2 remove_get_in_lhs.
    bind_jazz_hac ; [shelve | ].


    eapply rpre_weak_hypothesis_rule'.
    intros ? ? [? H].
    (* set (set_lhs _ _ _) in H. *)
    (* apply rpre_weaken_rule with (pre := λ s : heap * heap, s.1 = s₀ ∧ s.2 = s₁ /\ p s). *)
    (* }  *)


    (* apply H. *)
    (* s.1 = s₀ ∧ s.2 = s₁ /\ set_lhs ($$"temp2.317") temp2 *)
    (*   (set_lhs ($$"rkey.316") rkey *)
    (*      (set_lhs ($$"rcon.315") (coe_cht 'int (coe_cht 'int rcon)) pre)) *)
    (*   (s₀, s₁)). *)

    apply better_r_put_lhs.
    do 3 remove_get_in_lhs.

    rewrite bind_assoc.
    rewrite bind_assoc.
    match goal with
    | [ |- context [ ⊢ ⦃ ?pre ⦄ _ ≈ _ ⦃ _ ⦄ ] ] => set (P := pre)
    end.
    apply r_bind with (mid := λ '(v0, h0) '(v1, h1),
                         (∃ o1 o2 : 'word U128,
                             v0 = [('word U128; o1); ('word U128; o2)] ∧ (o1, o2) = v1) /\ P (h0, h1)).
    2:{
      intros.
      subst P.
      destruct a₁0.
      destruct a₀0 as [ | ? [] ] ; simpl ; repeat apply better_r_put_lhs ; repeat remove_get_in_lhs ; apply r_ret ; intros ; destruct_pre ; try easy.
      split.
      eexists.
      eexists.
      split.
      reflexivity.
      (* reflexivity. *)
      inversion H25.
      subst.
      inversion H24.
      subst.
      cbn.
      now rewrite !zero_extend_u.

      (* do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K). *)

      (* CAN BE DONE WITH: pdisj_apply H_pdisj. *)
      destruct H_pdisj.
      repeat eapply H ; easy.
    }

    subst.
    subst P.

    (* eapply rpre_hypothesis_rule. *)
    (* intros ? ? [? [[]]]. *)
    (* subst. *)
    (* (* apply rpre_weaken_rule with (pre := pre). *) *)

    (* 2:{ *)
    (*   intros ? ? []. *)
    (*   destruct_pre. *)
    (*   destruct H_pdisj. *)
    (*   eapply H; try easy. *)
    (*   eapply H; try easy. *)
    (*   eapply H; try easy. *)
    (*   eapply H; try easy. *)
    (* } *)

    (* (* eapply rpost_weaken_rule. *) *)

    intros.
    apply (key_combined_eq (id0~1)%positive rkey a₁ temp2).

    (* Unset Printing Notations. *)

    (* eapply H_pdisj. *)

    (* destruct H_pdisj. *)
    split.
    - intros.
      subst.
      repeat destruct H.
      subst.
      cbn in H2.
      subst.
      unfold set_lhs.

      (* exists (set_heap x0 (translate_var id0~1 v) a). *)
      subst.
      (* inversion H3. *)
      (* subst. *)
      (* exists (set_heap x0 (translate_var id0~1 v) a). *)
      (* rewrite set_heap_contract. *)
      destruct_pre.
      repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      eexists.
      split.
      split.
      reflexivity.
      eexists.
      split.
      eexists.
      split.
      exists (set_heap H9 (translate_var s_id' v) a).
      (* eexists. *)
      split.
      (* apply H10. *)
      eapply H_pdisj.
      reflexivity.
      etransitivity.
      apply fresh2_weak.
      assumption.
      assumption.
      reflexivity.
      reflexivity.
      reflexivity.

      rewrite ![set_heap _ (translate_var s_id' v) a]set_heap_commut.
      + reflexivity.
      + admit.
      + admit.
      + admit.
      + admit.
    - intros.
      subst.
      discriminate.

      Unshelve.
      {

        (* Keygen assist *)

        unfold tr_app_sopn_tuple.
        unfold sopn_sem.
        unfold sopn.get_instr_desc.


        Opaque aeskeygenassist.
        repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
        Transparent aeskeygenassist.
        apply (keygen_assist_eq (id0~1)%positive ).

        split.
        - intros.
          subst.
          destruct_pre.
          unfold set_lhs.
          eexists.
          eexists.
          eexists.
          split.
          exists (set_heap H5 (translate_var s_id' v) a).
          split.
          eapply H_pdisj.
          reflexivity.
          
          etransitivity.
          apply fresh2_weak.
          apply H0.
          apply H6.
          reflexivity.
          reflexivity.

          rewrite ![set_heap _ (translate_var s_id' v) a]set_heap_commut.
          reflexivity.
          admit.
          admit.
          admit.
        - intros.
          subst.
          destruct_pre.
          unfold set_lhs.
          eexists.
          eexists.
          eexists.
          split.
          eexists.
          split.
          eapply H_pdisj.
          apply H.
          apply H6.
          reflexivity.
          reflexivity.
          reflexivity.
      }
      Transparent translate_call.
  Admitted.


(* End Hacspec. *)
