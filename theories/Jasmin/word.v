From Coq Require Import Utf8 ZArith micromega.Lia.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import word ssrZ.

(* NB: This changes the behaviour of lia, making it work on goals with ssr types *)
From mathcomp Require Import zify.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!". 

Notation "m ⊕ k" := (wxor m k) (at level 20).
Notation "m ⟫ k" := (lsr m k) (at level 20).

Lemma lsr_word0 {n} a : word0 ⟫ a = @word0 n.
Proof.
  unfold lsr.
  rewrite Z.shiftr_0_l.
  apply val_inj.
  reflexivity.
Qed.

Lemma wxor_0_r {n} (a : word n) : a ⊕ word0 = a.
Proof.
  unfold wxor.
  apply val_inj. simpl.
  by rewrite Z.lxor_0_r.
Qed.

Lemma wxor_0_l {n} (a : word n) : wxor word0 a = a.
Proof.
  apply val_inj.
  reflexivity.
Qed.

Lemma wxor_involutive {n} : forall k : word n, k ⊕ k = word0.
Proof.
  intros k.
  apply/eqP/eq_from_wbit=> i.
  rewrite !wxorE addbb.
  unfold wbit.
  rewrite Z.testbit_0_l.
  reflexivity.
Qed.

Lemma wxorA {n} : forall m k l : word n, ((m ⊕ k) ⊕ l) = (m ⊕ (k ⊕ l)).
Proof.
  intros m k l.
  apply/eqP/eq_from_wbit=> i.
  by rewrite !wxorE addbA.
Qed.

Lemma wxorC {n} (a b : word n) : a ⊕ b = b ⊕ a.
Proof.
  apply/eqP/eq_from_wbit=> i. rewrite !wxorE.
  rewrite addbC. reflexivity.
Qed.

Lemma subword_word0 {n} a m : @subword n a m word0 = word0.
Proof.
  unfold subword.
  rewrite lsr_word0.
  apply val_inj.
  reflexivity.
Qed.

Lemma wcat_eq ws p a t :
  (forall (i : 'I_p), subword (i * ws) ws a = tnth t i) -> a = wcat t.
Proof.
  intros.
  rewrite -[a]wcat_subwordK.
  apply f_equal. apply eq_from_tnth.
  intros i.
  rewrite -H tnth_map tnth_ord_tuple.
  reflexivity.
Qed.

Lemma wbit_subword {ws1} i ws2 (w : word ws1) j :
  (ws2 <= ws1)%nat ->
  (j < ws2)%nat ->
  wbit (subword i ws2 w) j = wbit w (i + j)%nat.
Proof.
  intros.
  unfold subword.
  simpl.
  unfold urepr.
  simpl.
  unfold wbit.
  simpl.
  unfold modulus.
  rewrite !two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_low.
  { rewrite Z.mod_pow2_bits_low. 2: lia.
    rewrite Z.shiftr_spec. 2: lia.
    f_equal. lia.
  }
  lia.
Qed.

Lemma subword_xor {n} i ws (a b : n.-word) :
  (* I don't know if the assumption is necessary *)
  (ws <= n)%nat ->
  subword i ws (a ⊕ b) = (subword i ws a) ⊕ (subword i ws b).
Proof.
  intros H.
  apply/eqP/eq_from_wbit.
  intros. rewrite !wbit_subword. 2,3: auto.
  rewrite !wxorE.
  rewrite !wbit_subword. 2-5: auto.
  reflexivity.
Qed.

Lemma nth_aux {T} (a : T) l :
  [seq nth a l (val i) | i <- enum 'I_(size l)] = l.
Proof.
  replace [seq nth a l (val i) | i <- enum 'I_(size l)] with [seq nth a l i | i <- [seq val i | i <- enum 'I_(size l)]].
  2: { rewrite -map_comp. reflexivity. }
  rewrite val_enum_ord.
  rewrite map_nth_iota0. 2: lia.
  rewrite take_size. reflexivity.
Qed.

Lemma wcat_r_wcat {n} (l : seq (word n)) :
  wcat_r l = wcat [tuple nth word0 l i | i < size l].
Proof.
  rewrite/wcat=>/=.
  rewrite nth_aux.
  reflexivity.
Qed.

From Coq Require Import ZArith.

(* following three lemmas are from fiat crypto, consider importing *)
Local Open Scope Z.
Lemma mod_pow_same_base_larger a b n m :
  0 <= n <= m -> 0 < b ->
  (a mod (b^n)) mod (b^m) = a mod b^n.
Proof.
  intros.
  pose proof Z.mod_pos_bound a (b^n) ltac:(auto with zarith).
  assert (b^n <= b^m).
  { eapply Z.pow_le_mono_r; lia. }
  apply Z.mod_small. auto with zarith.
Qed.

Lemma mod_pow_same_base_smaller a b n m :
  0 <= m <= n -> 0 < b ->
  (a mod (b^n)) mod (b^m) = a mod b^m.
Proof.
  intros. replace n with (m+(n-m)) by lia.
  rewrite -> Z.pow_add_r, Z.rem_mul_r by auto with zarith.
  rewrite <- Zplus_mod_idemp_r.
  rewrite <- Zmult_mod_idemp_l.
  rewrite Z.mod_same. 2: eapply Z.pow_nonzero ; lia.
  rewrite Z.mul_0_l.
  rewrite Z.mod_0_l. 2: eapply Z.pow_nonzero ; lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod. 2: eapply Z.pow_nonzero ; lia.
  reflexivity.
Qed.

Lemma mod_pull_div a b c : 0 <= c -> (a / b) mod c = a mod (c * b) / b.
Admitted.
(* end of fiat crypto lemmas *)

Lemma shiftr_shiftr_mod w ws1 ws2 i j :
  (ws2 + j <= ws1)%nat ->
  Z.shiftr (Z.shiftr w (Z.of_nat i) mod modulus ws1) (Z.of_nat j) mod modulus ws2 =
    Z.shiftr w (Z.of_nat (i + j)) mod modulus ws2.
Proof.
  intros H.
  rewrite !modulusZE.
  rewrite !Z.shiftr_div_pow2; try lia.
  rewrite !mod_pull_div; try lia.
  simpl.
  rewrite -!Z.pow_add_r; try lia.
  rewrite mod_pow_same_base_smaller; try lia.
  rewrite Z.div_div; try lia.
  rewrite -Z.pow_add_r; try lia.
  rewrite Nat2Z.inj_add.
  f_equal. f_equal. f_equal. lia.
Qed.

Lemma larger_modulus a n m :
  (n <= m)%nat ->
  (a mod modulus n) mod modulus m = a mod modulus n.
Proof.
  intros H.
  rewrite !modulusZE.
  apply mod_pow_same_base_larger. 2: lia.
  zify. simpl. lia.
Qed.

Lemma smaller_modulus a n m :
  (m <= n)%nat ->
  (a mod modulus n) mod modulus m = a mod modulus m.
Proof.
  intros H.
  rewrite !modulusZE.
  apply mod_pow_same_base_smaller. 2: lia.
  zify. simpl. lia.
Qed.

Lemma subword_wshr {n} i j m (w : word n) :
  (m + i <= n)%nat ->
  subword i m (lsr w j) = subword (j + i) m w.
Proof.
  intros H.
  unfold subword; simpl.
  apply val_inj; simpl.
  rewrite urepr_word.
  unfold lsr.
  simpl.
  rewrite urepr_word.
  rewrite !smaller_modulus; try lia.
  rewrite shiftr_shiftr_mod; try lia.
Qed.

From Jasmin Require Import word.

Lemma subword_u {ws : wsize} (w : word ws) : subword 0 ws w = w.
Proof. by rewrite subword0 zero_extend_u. Qed.

Lemma wbit_wrepr (ws : wsize.wsize) a i :
  (i < ws)%nat ->
  word.word.wbit (urepr (wrepr ws a)) i = word.word.wbit a i.
Proof.
  move=>H/=.
  rewrite/word.word.wbit/wrepr/urepr=>/=.
  rewrite/modulus two_power_nat_equiv Z.mod_pow2_bits_low=>//.
  unfold nat_of_wsize in *. lia.
Qed.

Lemma wbit_make_vec {ws1} (ws2 : wsize) (l : seq (word.word ws1)) i :
  (i < ws2)%nat ->
  word.word.wbit (urepr (make_vec ws2 l)) i = word.word.wbit (nth word0 l (i %/ ws1)) (i %% ws1).
Proof.
  move=> H.
  rewrite /make_vec wcat_r_wcat wbit_wrepr=>//.
  rewrite wcat_wbitE=>/=.
  repeat f_equal.
  apply nth_aux.
Qed.

Lemma divn_aux j i n :
  (j < n)%nat ->
  (n <= j %% n + i %% n)%nat = false ->
  (j + i) %/ n = i %/ n.
Proof.
  intros H1 H2.
  rewrite divnD. 2: lia.
  rewrite H2.
  rewrite divn_small. all: lia.
Qed.

Lemma modn_aux j i n :
  (j < n)%nat ->
  (n <= j %% n + i %% n)%nat = false ->
  (j + i) %% n = (j + i %% n)%nat.
Proof.
  intros H1 H2.
  rewrite modnD. 2: lia.
  rewrite H2.
  rewrite modn_small. all: lia.
Qed.

Lemma subword_make_vec_full {ws1} i (ws2 ws3 : wsize.wsize) (l : seq (word.word ws1)) :
  (* i + ws2 does 'reach across' a single word in the list *)
  (ws2 <= ws1)%nat ->
  (i + ws2 <= ws3)%nat ->
  (ws1 <= (ws2 - 1) %% ws1 + i %% ws1)%nat = false ->
  (* i think this condition is equivalent, but the others fit with other lemmas *)
  (* ((i + ws2 - 1) / ws1)%nat = (i / ws1)%nat -> *)
  subword i ws2 (make_vec ws3 l) = subword (i %% ws1) ws2 (nth word0 l (i %/ ws1)%nat).
Proof.
  intros H1 H2 H3.
  rewrite !subwordE.
  f_equal.
  apply eq_mktuple.
  intros j.
  destruct j.  simpl.
  rewrite wbit_make_vec. 2: lia.
  f_equal.
  - f_equal. f_equal.
    apply divn_aux. 1:{ simpl. lia. }
    rewrite modn_small in H3. 2: lia.
    rewrite modn_small. 2: lia.
    lia.
  - apply modn_aux. 1: lia.
    rewrite modn_small in H3. 2: lia.
    rewrite modn_small. 1: lia.
    lia.
Qed.

Lemma subword_make_vec {ws1} i (ws2 : wsize.wsize) (l : seq (word.word ws1)) :
  (ws1 <= ws2)%nat ->
  ((i + 1) * ws1 <= ws2)%nat ->
  subword (i * ws1) ws1 (make_vec ws2 l) = nth word0 l i.
Proof.
  intros H1 H2.
  rewrite subword_make_vec_full.
  all: try lia. 
  { rewrite modnMl mulnK.
    2: { unfold nat_of_wsize; lia. }
    apply subword_u. }
  rewrite modnMl. unfold nat_of_wsize. lia.
Qed.

Lemma make_vec_ws ws (l : seq (word ws)) :
  make_vec ws l = nth word0 l 0.
Proof.
  apply/eqP. apply/eq_from_wbit.
  intros [i].
  rewrite wbit_make_vec=>/=.
  2: unfold nat_of_wsize in *; lia.
  rewrite divn_small.
  2: unfold nat_of_wsize in *; lia.
  rewrite modn_small.
  2: unfold nat_of_wsize in *; lia.
  reflexivity.
Qed.

Lemma make_vec_single {ws1} ws2 (a : word ws1) :
  make_vec ws2 [:: a] = zero_extend ws2 a.
Proof.
  unfold make_vec. cbn -[Z.of_nat].
  by rewrite Z.shiftl_0_l Z.lor_0_r.
Qed.

Lemma wshr_word0 {ws} i : @wshr ws 0 i = word0.
Proof.
  unfold wshr. by rewrite lsr_word0.
Qed.

Lemma nth_split_vec {ws1} ws2 n (d : word ws2) (w : word ws1) :
  (n < ws1 %/ ws2 + ws1 %% ws2)%nat ->
  nth d (split_vec ws2 w) n = subword (n * ws2) ws2 w.
Proof.
  intros H.
  unfold split_vec.
  erewrite nth_map.
  1: f_equal; rewrite nth_iota; try lia.
  rewrite size_iota.
  assumption.
  Unshelve. exact 0%nat.
Qed.

From Jasmin Require Import waes utils xseq.

Lemma subword_U8_SubWord n w :
  (0 <= n < 4)%nat ->
  subword (n * U8) U8 (SubWord w) = Sbox (subword (n * U8) U8 w).
Proof.
  intros.
  unfold SubWord.
  rewrite subword_make_vec.
  1: erewrite nth_map; f_equal.
  all: try (unfold nat_of_wsize, wsize_size_minus_1; zify; simpl; lia). 
  apply nth_split_vec.
  cbn. lia.
  Unshelve. exact word0.
Qed.

Lemma split_vec_make_vec {ws1} (ws2 : wsize.wsize) (l : seq (word.word ws1)) :
  (ws2 %% ws1 = 0)%nat ->
  (size l = ws2 %/ ws1)%nat ->
  split_vec ws1 (make_vec ws2 l) = l.
Proof.
  destruct l.
  - intros .
    unfold make_vec, split_vec.
    rewrite -H0 H.
    reflexivity.
  - intros Hmod Hsize.
    unfold split_vec.
    rewrite <- take_size.
    erewrite <- map_nth_iota0.
    2: easy.
    rewrite Hsize Hmod addn0.
    apply map_ext.
    intros.
    apply subword_make_vec.
    1: simpl in Hsize; nia.
    move: H => /InP. rewrite mem_iota.
    nia.
Qed.

Lemma SubWord_make_vec l :
  (size l = 4)%nat ->
  SubWord (make_vec U32 l) = make_vec U32 [seq Sbox i | i <- l].
Proof.
  intros.
  unfold SubWord.
  rewrite split_vec_make_vec.
  all: unfold nat_of_wsize, wsize_size_minus_1; easy.
Qed.

Lemma subword_make_vec_32_0_32_128 (l : seq u32) : subword 0 U32 (make_vec U128 l) = nth word0 l 0.
Proof.
  rewrite subword_make_vec_full; rewrite ?subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_1_32_128 (l : seq u32) : subword U32 U32 (make_vec U128 l) = nth word0 l 1.
Proof.
  rewrite subword_make_vec_full; rewrite ?subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_2_32_128 (l : seq u32) : subword (2 * U32) U32 (make_vec U128 l) = nth word0 l 2.
Proof.
  rewrite subword_make_vec_full; rewrite ?subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_3_32_128 (l : seq u32) : subword (3 * U32) U32 (make_vec U128 l) = nth word0 l 3.
Proof.
  rewrite subword_make_vec_full; rewrite ?subword_u.
  all: auto.
Qed.

Lemma wbit_wror {ws} (a : word ws) n m : wbit_n (wror a n) m = wbit_n a (Z.to_nat (((Z.of_nat m) - n) mod (wsize_bits ws)))%Z.
Proof.
  unfold wror.
  (* rewrite urepr_word. *)
  (* wbit_n *)
  rewrite worE.
  rewrite wshrE.
  rewrite wshlE.
  destruct ((Z.to_nat (wsize_bits ws - n mod wsize_bits ws) <= m <= wsize_size_minus_1 ws))%nat eqn:E.
  { cbn -[Z.sub].
    rewrite Nat2Z.inj_add.
    (* rewrite Z2Nat.inj_add. *)
    rewrite Z2Nat.id.
    2: admit. admit. }
Admitted.

Lemma wror_substitute w k : wror (SubWord w) k = SubWord (wror w k).
Proof.
  unfold SubWord.
  unfold wror.
  (* I would like to case on w, but not sure how to do this most efficiently? *)
Admitted.

Lemma wreprI ws (a : word.word ws) : wrepr ws (toword a) = a.
Proof.
  apply val_inj. simpl. destruct a. rewrite Z.mod_small. 1: reflexivity.
  simpl in *. lia.
Qed.

(** AES *)

Lemma ShiftRows_SubBytes s : ShiftRows (SubBytes s) = SubBytes (ShiftRows s).
Proof.
  unfold ShiftRows, SubBytes. simpl.
  f_equal. f_equal.
  all: rewrite !subword_make_vec_32_0_32_128 !subword_make_vec_32_1_32_128 !subword_make_vec_32_2_32_128 !subword_make_vec_32_3_32_128; simpl;
    rewrite -> !subword_U8_SubWord by lia;
    rewrite -> !SubWord_make_vec by reflexivity; reflexivity.
Qed.

Lemma wAESENC_wAESENC_ s k : wAESENC s k = wAESENC_ s k.
Proof.
  unfold wAESENC, wAESENC_.
  f_equal. f_equal.
  rewrite ShiftRows_SubBytes.
  reflexivity.
Qed.

(* NOTE: This is only so simple because InvMixColumns is not properly implemented *)
Lemma AESDEC_AESDEC_ s k : wAESDEC s (InvMixColumns k) = wAESDEC_ s k.
Proof.
  unfold wAESDEC, wAESDEC_.
  unfold InvMixColumns.
  reflexivity.
Qed.

Lemma wAESENCLAST_wAESENCLAST_ s k : wAESENCLAST s k = wAESENCLAST_ s k.
Proof.
  unfold wAESENCLAST, wAESENCLAST_.
  rewrite ShiftRows_SubBytes.
  reflexivity.
Qed.
