Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra zify.
From mathcomp Require Import word_ssrZ word.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 ZArith micromega.Lia List.

From Jasmin Require Import expr xseq waes word.
From JasminSSProve Require Import jasmin_translate word aes_utils.

From Relational Require Import OrderEnrichedCategory.
From Crypt Require Import Prelude Package ChoiceAsOrd choice_type.

From extructures Require Import ord fset fmap.

Import ListNotations.
Import JasminNotation.
Import PackageNotation.
Import AesNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!". 

Local Open Scope Z.

(** Specs  *)

Definition rcon (i : Z) : u8 := nth (wrepr U8 54%Z) [:: (wrepr U8 1%Z); (wrepr U8 2%Z); (wrepr U8 4%Z); (wrepr U8 8%Z); (wrepr U8 16%Z); (wrepr U8 32%Z); (wrepr U8 64%Z); (wrepr U8 128%Z); (wrepr U8 27%Z); (wrepr U8 54%Z)]%Z ((Z.to_nat i) - 1).

Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

Definition key_expand (wn1 : u128) (rcon : u8) : 'word U128 :=
  let rcon := zero_extend U32 rcon in
  let w0 := subword 0 U32 wn1 in
  let w1 := subword (1 * U32) U32 wn1 in
  let w2 := subword (2 * U32) U32 wn1 in
  let w3 := subword (3 * U32) U32 wn1 in
  let tmp := w3 in
  let tmp := SubWord (RotWord tmp) ⊕ rcon in
  let w4 := w0 ⊕ tmp in
  let w5 := w1 ⊕ w4 in
  let w6 := w2 ⊕ w5 in
  let w7 := w3 ⊕ w6 in
  wcat [tuple w4; w5; w6; w7].

Definition key_i  (k : u128) i :=
  iteri i (fun i ki => key_expand ki (rcon ((Z_of_nat i) + 1))) k.

Definition aes (key msg : u128) :=
  let state := wxor msg (key_i key 0) in
  let state := iteri 9 (fun i state => wAESENC_ state (key_i key (i + 1))) state in
  wAESENCLAST_ state (key_i key 10).

Definition invaes (key cipher : u128) :=
  let state := wxor cipher (key_i key 10) in
  let state := iteri 9 (fun i state => wAESDEC_ state (key_i key (10 -(i + 1)))) state in
  wAESDECLAST state (key_i key 0).

Definition rkeys : Location := ( 'arr U128 ; 0%nat ).
Definition state : Location := ( 'word U128 ; 0%nat).
Definition Cenc_locs := [:: state ; rkeys].

Definition keyExpansion (key : u128) : raw_code ('arr U128) :=
    #put rkeys := @emptym (chElement_ordType 'int) u128 ;;
    rkeys0 ← get rkeys ;;
    #put rkeys := setm rkeys0 0 key ;;
    lfor_loop (fun i =>
    rkeys0 ← get rkeys ;;
    #put rkeys := setm rkeys0 i (key_expand (zero_extend _ (getmd rkeys0 word0 (i - 1))) (rcon i)) ;;
    ret tt) 1 11 ;;
    rkeys0 ← get rkeys ;;
    ret rkeys0.

Definition aes_rounds (rkeys : 'arr U128) (msg : 'word U128) : raw_code u128 :=
    #put state := wxor msg (getmd rkeys word0 0) ;;
    lfor_loop (fun i =>
      state0 ← get state ;;
      #put state := wAESENC_ state0 (getmd rkeys word0 i) ;;
      ret tt
    ) 1 10 ;;
    state0 ← get state ;;
    #put state := wAESENCLAST_ state0 (getmd rkeys word0 10) ;;
    state0 ← get state ;;
    ret state0.

Definition Caes (key msg : u128) :=
  rkeys ← keyExpansion key ;;
  cipher ← aes_rounds rkeys msg ;;
  ret cipher.

(** Correctness proofs *)

Lemma keyExpansion_h (pre : precond) k :
  u_pdisj pre [fset rkeys] ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    keyExpansion k
    ≈
    ret tt
    ⦃ fun '(v0, h0) '(_, h1) => pre (h0, h1) /\ forall i, 0 <= i < 11 -> (getmd v0 word0 i) = key_i k (Z.to_nat i) ⦄.
Proof.
  intros Hdisj.
  unfold keyExpansion.
  eapply r_put_lhs with (pre := fun '(_, _) => _).
  eapply r_get_remember_lhs. intros x.
  eapply r_put_lhs.
  eapply r_bind with (m₁ := ret _).
  { eapply u_lfor_loop_rule_weaken with
    (I:= fun i => fun h0 h1 => pre (h0, h1) /\ forall j, 0 <= j < i -> getmd (get_heap h0 rkeys) word0 j = key_i k (Z.to_nat j)).
    { lia. }
    - intros h1 h2 Hset.
      destruct_pre.
      split_post.
      + u_pdisj_apply Hdisj.
      + intros j Hj.
        sheap.
        unfold getmd.
        rewrite setmE.
        assert (@eq_op (Ord.eqType Z_ordType) j Z0) by (apply/eqP; lia).
        rewrite H.
        move: H=>/eqP ->.
        simpl.
        reflexivity.
    - intros i ile.
      ssprove_code_simpl.
      eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x0.
      eapply r_put_lhs.
      eapply r_ret.
      intros s0 s1 Hpre.
      destruct_pre. split_post.
      + u_pdisj_apply Hdisj.
      + intros j Hj.
        rewrite get_set_heap_eq.
        rewrite -> H6 by lia.
        unfold getmd in *.
        rewrite setmE.
        destruct (Z.eq_dec j i).
        * subst.
          rewrite eq_refl.
          rewrite zero_extend_u.
          replace (Z.to_nat i) with (Z.to_nat (i - 1)).+1 by lia.
          unfold key_i at 2.
          rewrite iteriS.
          f_equal. f_equal. simpl. lia.
        * assert (@eq_op (Ord.eqType Z_ordType) j i = false).
          { apply/eqP. assumption. }
          rewrite H1; auto.
          rewrite H6; auto.
          lia. }
  intros s0 s1.
  eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x0.
  eapply r_ret.
  intros s2 s3 Hpre.
  destruct_pre.
  split.
  - easy.
  - apply H2.
Qed.

Lemma aes_rounds_h rkeys k m pre :
  u_pdisj pre [fset state] ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) /\ (forall i, 0 <= i < 11 -> getmd rkeys word0 i = key_i k (Z.to_nat i)) ⦄
  aes_rounds rkeys m
  ≈
  ret tt
  ⦃ fun '(v0, h0) '(_, h1) => pre (h0, h1) /\ v0 = aes k m ⦄.
Proof.
  unfold aes_rounds.
  intros Hdisj.
  set (st0 := m ⊕ (key_i k 0%nat)).
  eapply r_put_lhs with (pre := fun '(_, _) => _).
  eapply r_bind with (m₁ := ret _).
  { eapply u_lfor_loop_rule_weaken with
    (I := fun i => fun h0 h1 => pre (h0, h1) /\ get_heap h0 state = iteri (Z.to_nat i - 1) (fun i state => wAESENC_ state (key_i k (i + 1))) st0
                      /\ (forall i, 0 <= i < 11 -> getmd rkeys word0 i = key_i k (Z.to_nat i))).
    - lia.
    - intros.
      simpl.
      destruct_pre. sheap. split_post.
      + u_pdisj_apply Hdisj.
      + rewrite H3; auto. lia.
      + assumption.
    - intros i Hi.
      eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x.
      eapply r_put_lhs. eapply r_ret.
      intros s0 s1 Hpre.
      destruct_pre; sheap; split_post.
      + u_pdisj_apply Hdisj.
      + replace (Z.to_nat (Z.succ i) - 1)%nat with ((Z.to_nat i - 1).+1) by lia.
        rewrite iteriS.
        rewrite H4.
        rewrite H7. 2: lia. repeat f_equal. lia. 
      + assumption. }
  intros a0 a1.
  eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x.
  eapply r_put_lhs.
  eapply r_get_remember_lhs. intros x0.
  eapply r_ret.
  intros s0 s1 Hpre.
  destruct Hpre as [[s2 [[[H5 [H4 H6]] H3] H2]] H1].
  simpl in H3, H1. subst.
  sheap.
  split; [u_pdisj_apply Hdisj|].
  unfold aes.
  rewrite H4.
  rewrite H6. 2: lia.
  replace ((Z.to_nat 10) - 1)%nat with 9%nat by reflexivity.
  reflexivity. 
Qed.

Lemma aes_h k m pre :
  (u_pdisj pre (fset Cenc_locs)) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    Caes k m
    ≈
    ret tt
    ⦃ fun '(v0, h0) '(_, h1) => pre (h0, h1) /\ v0 = aes k m ⦄.
Proof.
  unfold Caes.
  intros Hdisj.
  eapply r_bind with (m₁ := ret _).
  { eapply keyExpansion_h.
    u_pdisj_apply Hdisj.
    intros h1 h2 l a lin Hpre.
    eapply Hdisj; auto.
    rewrite in_fset in lin.
    simpl in lin.
    unfold Cenc_locs.
    move: lin => /InP []; [move=> ->|by []].
    auto_in_fset. }
  intros a0 [].
  eapply r_bind with (m₁ := ret _).
  { eapply aes_rounds_h.
    intros h1 h2 l a lin Hpre.
    eapply Hdisj; auto.
    rewrite in_fset in lin.
    simpl in lin.
    unfold Cenc_locs.
    move: lin => /InP []; [move=> ->|by []].
    auto_in_fset. }
  intros a1 [].
  eapply r_ret.
  intros.
  assumption.
Qed.
