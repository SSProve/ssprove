From Coq Require Import Utf8 ZArith micromega.Lia.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word ssrZ.

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
(* end of fiat crypto lemmas *)

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

Lemma wbit_subword {ws1} i ws2 (w : word ws1) (j : 'I_ws2) :
  wbit (subword i ws2 w) j = wbit w (i + j)%nat.
Proof.
  intros.
  unfold subword.
  rewrite wbit_mkword.
  apply wbit_lsr.
Qed.

Lemma subword_wshr {n} i j m (w : word n) :
  subword i m (lsr w j) = subword (j + i) m w.
Proof.
  intros.
  apply/eqP/eq_from_wbit.
  intros.
  rewrite !wbit_subword.
  rewrite wbit_lsr.
  f_equal.
  lia.
Qed.

Lemma subword_xor {n} i ws (a b : n.-word) :
  subword i ws (a ⊕ b) = (subword i ws a) ⊕ (subword i ws b).
Proof.
  apply/eqP/eq_from_wbit.
  intros. rewrite !wbit_subword.
  rewrite !wxorE.
  rewrite !wbit_subword.
  reflexivity.
Qed.

(** AES *)

Lemma subword_subword {k} i j n m (w : k.-word) : (i + n <= m)%nat -> subword i n (subword j m w) = subword (i + j) n w.
Proof.
  intros.
  apply/eqP/eq_from_wbit => l.
  rewrite !wbit_subword.
  assert (i + l < m)%nat. 1: destruct l; simpl; lia.
  change (i + l)%nat with (@Ordinal m (i + l) H0 : nat).
  rewrite wbit_subword.
  f_equal.
  simpl. lia.
Qed.

Locate "`_".

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

(* Local Open Scope ring_scope. *)
Lemma subword_wcat {n p} i l (s : p.-tuple n.-word) :
  (* i + l does 'reach across' a single word in the tuple *)
  (l <= n)%nat ->
  ((l - 1) %% n + i %% n < n)%nat ->
  subword i l (wcat s) = subword (i %% n) l (s`_(i %/ n))%R.
Proof.
  intros H1 (* H2 *) H3.
  rewrite !subwordE.
  f_equal.
  apply eq_mktuple => j.
  rewrite wcat_wbitE.
  destruct j.  simpl.
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

(* Lemma nth_wsplitnec {n p} (i : 'I_p) (w : (n * p).-word) : *)
(*   (* (n < n %/ l + n %% l)%nat -> *) *)
(*   ((wsplitn w)`_i)%R = subword (i * n) n w. *)
(* Proof. *)
(*   (* intros H. *) *)
(*   (* unfold split_vec. *) *)
(*   unfold wsplitn. *)
(*   (* Unset Printing Notations. *) *)
(*   (* pose proof nth_mktuple . *) *)
(*   rewrite  *)
(*   rewrite (nth_map 0). *)
(*   erewrite nth_map. *)
(*   1: f_equal; rewrite nth_iota; try lia. *)
(*   rewrite size_iota. *)
(*   assumption. *)
(*   Unshelve. exact 0%nat. *)
(* Qed. *)

Lemma mkword_word {n} (w : n.-word) :
  mkword n w = w.
Proof.
  apply val_inj; simpl.
  rewrite Z.mod_small.
  1: reflexivity.
  destruct w. simpl. lia.
Qed.

Lemma subword_u {n} (w : n.-word) : subword 0 n w = w.
Proof.
  unfold subword. unfold lsr. rewrite Z.shiftr_0_r. rewrite ureprK.
  apply mkword_word.
Qed.

From Jasmin Require Import word.

(* Lemma make_vec_eq {ws1 ws2 : wsize} {p : nat} a t : *)
(*   (p * ws1 = ws2) -> *)
(*   (forall (i : 'I_p), subword (i * ws1) ws1 a = nth word0 t i) -> a = make_vec ws2 t. *)
(* Proof. *)
(*   intros. *)
(*   unfold make_vec. *)
(*   unfold wrepr. *)
(*   apply val_inj. *)
(*   simpl. *)
(*   rewrite wcat *)

(* Lemma wcat_eq ws p a t : *)
(*   (forall (i : 'I_p), subword (i * ws) ws a = tnth t i) -> a = wcat t. *)
(* Proof. *)
(*   intros. *)
(*   rewrite -[a]wcat_subwordK. *)
(*   apply f_equal. apply eq_from_tnth. *)
(*   intros i. *)
(*   rewrite -H tnth_map tnth_ord_tuple. *)
(*   reflexivity. *)
(* Qed. *)

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

Lemma wbit_n_make_vec {ws1} (ws2 : wsize) (l : seq (word ws1)) i :
  (i < ws2)%nat ->
  wbit_n (make_vec ws2 l) i = wbit_n (nth word0 l (i %/ ws1)) (i %% ws1).
Proof.
  move=> H.
  unfold wbit_n.
  rewrite /make_vec wcat_r_wcat wbit_wrepr=>//.
  rewrite wcat_wbitE=>/=.
  repeat f_equal.
  rewrite nth_aux.
  reflexivity.
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

(* Lemma subw *)

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

Lemma SubBytes_make_vec l :
  (size l = 4)%nat ->
  SubBytes (make_vec U128 l) = make_vec U128 [seq SubWord i | i <- l].
Proof.
  intros.
  unfold SubBytes.
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


Lemma wreprI ws (a : word.word ws) : wrepr ws (toword a) = a.
Proof.
  apply val_inj. simpl. destruct a. rewrite Z.mod_small. 1: reflexivity.
  simpl in *. lia.
Qed.

(** AES *)

Lemma subword_SubWord n w :
  (0 <= n < 4)%nat -> subword (n * U8) U8 (SubWord w) = Sbox (subword (n * U8) U8 w).
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

Lemma subword_SubBytes n w : (0 <= n < 4)%nat -> subword (n * U32) U32 (SubBytes w) = SubWord (subword (n * U32) U32 w).
Proof.
  intros.
  unfold SubBytes.
  rewrite subword_make_vec.
  1: erewrite nth_map; f_equal.
  all: try (unfold nat_of_wsize, wsize_size_minus_1; zify; simpl; lia).
  apply nth_split_vec.
  cbn. lia.
  Unshelve. exact word0.
Qed.

Lemma ShiftRows_SubBytes s : ShiftRows (SubBytes s) = SubBytes (ShiftRows s).
Proof.
  unfold ShiftRows. simpl.
  rewrite !subword_SubBytes; try reflexivity.
  rewrite !subword_SubWord; try reflexivity.
  rewrite SubBytes_make_vec; auto. simpl.
  rewrite !SubWord_make_vec; auto.
Qed.

Lemma RotWord_SubWord w : RotWord (SubWord w) = SubWord (RotWord w).
Proof.
  unfold RotWord.
  rewrite SubWord_make_vec; auto.
  rewrite !subword_SubWord; auto.
Qed.

Lemma wAESENC_wAESENC_ s k : wAESENC s k = wAESENC_ s k.
Proof.
  unfold wAESENC, wAESENC_.
  f_equal. f_equal.
  rewrite ShiftRows_SubBytes.
  reflexivity.
Qed.

Lemma wAESENCLAST_wAESENCLAST_ s k : wAESENCLAST s k = wAESENCLAST_ s k.
Proof.
  unfold wAESENCLAST, wAESENCLAST_.
  rewrite ShiftRows_SubBytes.
  reflexivity.
Qed.
