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

Infix "^" := wxor.
Definition ws_def : seq Z := [::].

Definition get_tr := get_translated_fun ssprove_jasmin_prog.

Definition pdisj (P : precond) (s_id : p_id) (rhs : {fset Location}) :=
  (forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
  (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

Ltac solve_in :=
  repeat match goal with
    | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
    | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
    end.

Fixpoint list_to_chtuple (l : list typed_chElement) : lchtuple [seq t.π1 | t <- l] :=
  match l as l0 return lchtuple [seq t.π1 | t <- l0]
  with
  | [] => tt
  | tc' :: l' =>
      let rec := @list_to_chtuple l' in
      match l' as l'0
            return
            lchtuple [seq t.π1 | t <- l'0] ->
            lchtuple [seq t.π1 | t <- (tc'::l'0)]
      with
      | [] => fun _ => tc'.π2
      | tc'' :: l'' => fun rec => (tc'.π2, rec)
      end rec
  end.

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

Ltac split_post :=
  repeat
    match goal with
    | |- (_ ⋊ _) _ => split
    | |- _ /\ _ => split
    | |- set_lhs _ _ _ _ => eexists
    end.

(* NB: this redefines neq_loc_auto, which helps some tactics, since checking for inequality by computation is not feasible for translated variables *)
Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

(* I don't know what rewrite * means, but this is much faster than regular rewrite, which also sometimes overflows the stack *)
Ltac sheap :=
  repeat first [ rewrite * get_set_heap_neq; [| neq_loc_auto ] |
                 rewrite * get_set_heap_eq ].

(* This works sometimes, but might be very slow *)
Ltac simpl_heap :=
  repeat lazymatch goal with
    | |- context [ get_heap (set_heap _ ?l _) ?l ] => rewrite -> get_set_heap_eq
    | |- context [ get_heap (set_heap (translate_var ?s_id _) (translate_var ?s_id _ ) _ ) _ ] => (rewrite -> get_set_heap_neq by (apply injective_translate_var3; auto))
    | |- context [ get_heap (set_heap _ (translate_var _ _ ) _ ) _ ] => (rewrite -> get_set_heap_neq by (apply injective_translate_var2; assumption))
    end.

Ltac simpl_heap' :=
  repeat lazymatch goal with
    | |- context [ get_heap (set_heap _ _ _) _ ] =>
        try rewrite -> get_set_heap_eq;
        try (rewrite -> get_set_heap_neq by (apply injective_translate_var3; auto));
        try (rewrite -> get_set_heap_neq by (apply injective_translate_var2; assumption))
    end.

#[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq.
Ltac solve_preceq :=
  repeat lazymatch goal with
    | |- ?a ⪯ ?a => reflexivity
    | |- ?a ⪯ ?b~1 => etransitivity; [|apply preceq_I]
    | |- ?a ⪯ ?b~0 => etransitivity; [|apply preceq_O]
    end.

Ltac pdisj_apply h :=
  lazymatch goal with
  | |- ?pre (set_heap _ _ _, set_heap _ _ _) => eapply h; [ solve_in | pdisj_apply h ]
  | |- ?pre (set_heap _ _ _, _) =>
      eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
  | |- _ => try assumption
  end.

Definition rcon (i : Z) : u8 := nth (wrepr U8 54%Z) [:: (wrepr U8 1%Z); (wrepr U8 2%Z); (wrepr U8 4%Z); (wrepr U8 8%Z); (wrepr U8 16%Z); (wrepr U8 32%Z); (wrepr U8 64%Z); (wrepr U8 128%Z); (wrepr U8 27%Z); (wrepr U8 54%Z)]%Z ((Z.to_nat i) - 1).

Notation hdtc res := (coerce_to_choice_type ('array) (hd ('word U64 ; chCanonical _) res).π2).
Notation call fn := (translate_call _ fn _).

Definition key_expand (wn1 : u128) (rcon : u8) : 'word U128 :=
  let rcon := zero_extend U32 rcon (* W4u8 *) (* U32 4 *) (* [tuple rcon ; 0%R; 0%R; 0%R] *) (* [toword rcon; 0%Z; 0%Z; 0%Z] *) in
  let w0 := subword 0 U32 wn1 in
  let w1 := subword (1 * U32) U32 wn1 in
  let w2 := subword (2 * U32) U32 wn1 in
  let w3 := subword (3 * U32) U32 wn1 in
  let tmp := w3 in
  let tmp := SubWord (wror tmp 1) ^ rcon in
  let w4 := w0 ^ tmp in
  let w5 := w1 ^ w4 in
  let w6 := w2 ^ w5 in
  let w7 := w3 ^ w6 in
  wcat [tuple w4; w5; w6; w7].

Lemma rcon_correct id0 pre i :
  (pdisj pre id0 fset0) ->
  (forall s0 s1, pre (s0, s1) -> (1 <= i < 11)%Z) ->
  ⊢ ⦃ fun '(s0, s1) => pre (s0, s1) ⦄ JRCON id0 i
    ≈ ret tt
    ⦃ fun '(v0, s0) '(v1, s1) => pre (s0, s1) /\ exists o, v0 = ([('int ; o)] : tchlist) /\ o = wunsigned (rcon i) ⦄.
Proof.
  unfold  get_tr, get_translated_fun.
  intros Hpdisj H.
  simpl_fun.
  repeat setjvars.
  repeat match goal with
         | |- context[(?a =? ?b)%Z] => let E := fresh in destruct (a =? b)%Z eqn:E; [rewrite ?Z.eqb_eq in E; subst|]
         | |- _ => simpl; ssprove_contract_put_get_lhs; rewrite !coerce_to_choice_type_K
         end.
  all: ssprove_code_simpl; rewrite !coerce_to_choice_type_K; eapply r_put_lhs; ssprove_contract_put_get_lhs; eapply r_put_lhs; eapply r_ret.
  all: intros; destruct_pre; split_post; [ pdisj_apply Hpdisj | rewrite coerce_to_choice_type_K; eexists; split; eauto ].
  destruct (i =? 10)%Z eqn:E. rewrite Z.eqb_eq in E. subst. reflexivity.
  apply H in H13. lia.
Qed.

(* copy of the easycrypt functional definition *)
Definition W4u8 : 4.-tuple u8 -> u32 := wcat.
Definition W4u32 : 4.-tuple u32 -> u128 := wcat.


Notation "m ⊕ k" := (@word.word.wxor _ m k) (at level 20).

Lemma lsr_word0 {ws1} a : @lsr ws1 word0 a = word0.
Proof.
  unfold lsr.
  rewrite Z.shiftr_0_l.
  apply val_inj.
  reflexivity.
Qed.

Lemma subword_word0 {ws1} a ws2 : @subword ws1 a ws2 word0 = word0.
Proof.
  unfold subword.
  rewrite lsr_word0.
  apply val_inj.
  reflexivity.
Qed.

Lemma wpshufd10 : forall w n, wpshufd1 w 0 n = zero_extend U32 w.
Proof.
  unfold wpshufd1.
  intros a n.
  rewrite subword_word0 Z.mul_0_r wshr0.
  change 32%nat with (nat_of_wsize U32).
  apply subword0.
Qed.

(* Lemma wpshufd_1280 : forall a,  wpshufd_128 a 0 = a. *)
(* Proof. *)
(*   intros a. *)
(*   unfold wpshufd_128. *)
(*   rewrite wrepr0. *)
(*   unfold iota, map. *)
(*   rewrite !wpshufd10. *)
(*   simpl. *)
(* Admitted. *)

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

Definition W4u32_eq : forall a t, (forall (i : 'I_4), subword (i * U32) U32 a = tnth t i) -> a = W4u32 t := wcat_eq U32 4.

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

Local Open Scope Z_scope.

Lemma wrepr_lsr (ws : wsize.wsize) a i :
  (0 <= a < modulus ws)%Z ->
  lsr (wrepr ws a) i = wrepr ws (Z.shiftr a (Z.of_nat i)).
Proof.
  intros H.
  unfold lsr.
  rewrite mkwordK.
  unfold wrepr.
  apply val_inj.
  simpl.
  rewrite [a mod _]Z.mod_small. 2: assumption.
  reflexivity.
Qed.

Lemma modulus_gt0' n : (0 < modulus n)%Z.
Proof.
  apply Z.ltb_lt.
  apply modulus_gt0.
Qed.

(* following two lemmas are from fiat crypto, consider importing *)
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

Lemma nat_of_wsize_m ws : (wsize_size_minus_1 ws).+1 = nat_of_wsize ws.
Proof. destruct ws; reflexivity. Qed.
Lemma modulus_ne0 : forall n, modulus n <> 0.
Proof.
  intros n.
  pose proof modulus_gt0 n.
  zify. lia.
Qed.

Lemma enum0 :
  enum ('I_0) = [].
Proof.
  assert (size (enum 'I_0) = 0%nat).
  { apply size_enum_ord. }
  apply size0nil. assumption.
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

Lemma make_vec_wcat {ws1} (l : seq (word.word ws1)) :
  wcat_r l = wcat [tuple nth word0 l i | i < size l].
Proof.
  unfold wcat.
  simpl.
  rewrite nth_aux.
  reflexivity.
Qed.
Lemma wbit_wrepr (ws : wsize.wsize) a i :
  (i < ws)%nat ->
  wbit (urepr (wrepr ws a)) i = wbit a i.
Proof.
  intros H.
  unfold wbit.
  unfold wrepr.
  unfold urepr.
  simpl. unfold modulus.
  rewrite two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_low.
  2:{ unfold nat_of_wsize in *. lia. }
  reflexivity.
Qed.

Lemma wbit_make_vec {ws1} (ws2 : wsize.wsize) (l : seq (word.word ws1)) i :
  (i < ws2)%nat ->
  wbit (urepr (make_vec ws2 l)) i = wbit (nth word0 l (i %/ ws1)) (i %% ws1).
Proof.
  intros H.
  unfold make_vec.
  rewrite make_vec_wcat.
  rewrite wbit_wrepr. 2: assumption.
  rewrite wcat_wbitE.
  unfold urepr.
  simpl.
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

Lemma subword_make_vec1 {ws1} i ws2 (ws3 : wsize.wsize) (l : seq (word.word ws1)) :
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
  destruct j. simpl.
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

Lemma make_vec_ws ws (l : seq (word.word ws)) :
  make_vec ws l = nth word0 l 0.
Proof.
  apply/eqP.
  apply/eq_from_wbit.
  intros [i].
  rewrite wbit_make_vec.
  simpl.
  rewrite divn_small.
  rewrite modn_small.
  reflexivity.
  unfold nat_of_wsize. lia.
  unfold nat_of_wsize. lia.
  unfold nat_of_wsize. simpl. lia.
Qed.

Lemma subword_0_128 (l : seq u128) :
  subword 0 0 (make_vec U128 l) = subword 0 0 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_0_32_128 (l : seq u128) :
  subword 0 U32 (make_vec U128 l) = subword 0 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_1_32_128 (l : seq u128) :
  subword 1 U32 (make_vec U128 l) = subword 1 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_2_32_128 (l : seq u128) :
  subword 2 U32 (make_vec U128 l) = subword 2 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_3_32_128 (l : seq u128) :
  subword 3 U32 (make_vec U128 l) = subword 3 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.


Lemma subword_make_vec {ws1} i (ws2 : wsize.wsize) (l : seq (word.word ws1)) :
  (ws1 <= ws2)%nat ->
  ((i + 1) * ws1 < ws2)%nat ->
  subword (i * ws1) ws1 (make_vec ws2 l) = nth word0 l i.
Proof.
  intros H1 H2.
  apply/eqP.
  apply /eq_from_wbit.
  intros [i0]. simpl.
  rewrite wbit_subword.
  rewrite wbit_make_vec.
  rewrite addnC.
  rewrite divn_aux.
  rewrite mulnK.
  rewrite modn_aux.
  rewrite modnMl.
  rewrite addn0.
  reflexivity. all: try lia.
  rewrite modnMl. lia.
  rewrite modnMl. lia.
  unfold nat_of_ord in *. unfold nat_of_wsize in *. lia.
Qed.

Lemma subword_u {ws} (w : word.word ws) : subword 0 ws w = w.
Proof. by rewrite subword0 zero_extend_u. Qed.

Lemma nth_map2 {A B C} (a : A) (b : B) (c : C) la lb f n :
  (n < Nat.min (size la) (size lb))%nat -> nth c (map2 f la lb) n = f (nth a la n) (nth b lb n).
Proof.
  revert la lb.
  induction n; intros.
  - destruct la.
    + simpl in H; zify; lia.
    + destruct lb.
      * simpl in H; zify; lia.
      * reflexivity.
  - destruct la.
    + simpl in H; zify; lia.
    + destruct lb.
      * simpl in H; zify; lia.
      * simpl.
        eapply IHn.
        simpl in H.
        zify; lia.
Qed.

Lemma subword_make_vec_32_0_32_128 (l : seq u32) : subword 0 U32 (make_vec U128 l) = nth word0 l 0.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_1_32_128 (l : seq u32) : subword U32 U32 (make_vec U128 l) = nth word0 l 1.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_2_32_128 (l : seq u32) : subword (2 * U32) U32 (make_vec U128 l) = nth word0 l 2.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_3_32_128 (l : seq u32) : subword (3 * U32) U32 (make_vec U128 l) = nth word0 l 3.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Arguments nat_of_wsize : simpl never.
Arguments wsize_size_minus_1 : simpl never.

Lemma make_vec_single {ws1} ws2 (a : word.word ws1) :
  make_vec ws2 [:: a] = zero_extend ws2 a.
Proof.
  unfold make_vec. cbn -[Z.of_nat].
  by rewrite Z.shiftl_0_l Z.lor_0_r.
Qed.

Lemma wshr_word0 {ws} i : @wshr ws 0 i = word0.
Proof.
  unfold wshr.
  by rewrite lsr_word0.
Qed.

Lemma wxor_0_r {n} (a : n.-word) : wxor a word0 = a.
Proof.
  unfold wxor.
  apply val_inj. simpl.
  by rewrite Z.lxor_0_r.
Qed.

Lemma wxor_0_l {n} (a : n.-word) : wxor word0 a = a.
Proof.
  apply val_inj.
  reflexivity.
Qed.

(* from fiat crypto, but proof is more involved *)
Lemma mod_pull_div a b c
  : 0 <= c -> (a / b) mod c = a mod (c * b) / b.
Admitted.

Lemma shiftr_shiftr_mod w ws1 ws2 i j :
  (ws2 + j <= ws1)%nat ->
  Z.shiftr (Z.shiftr w (Z.of_nat i) mod modulus ws1) (Z.of_nat j) mod modulus ws2 =
    Z.shiftr w (Z.of_nat (i + j)) mod modulus ws2.
Proof.
  intros H.
  rewrite modulusZE.
  simpl.
  rewrite !modulusZE.
  rewrite !Z.shiftr_div_pow2.
  rewrite !mod_pull_div.
  simpl.
  rewrite -!Z.pow_add_r.
  rewrite mod_pow_same_base_smaller.
  rewrite Z.div_div.
  rewrite -Z.pow_add_r.
  rewrite Nat2Z.inj_add.
  f_equal. f_equal. f_equal.
  all: try lia.
Qed.

Lemma subword_wshr {ws1} i j ws2 (w : ws1.-word) :
  (ws2 + i <= ws1)%nat ->
  subword i ws2 (lsr w j) = subword (j + i) ws2 w.
Proof.
  intros H.
  unfold subword; simpl.
  apply val_inj; simpl.
  rewrite urepr_word.
  unfold lsr.
  simpl.
  rewrite urepr_word.
  rewrite !smaller_modulus.
  rewrite shiftr_shiftr_mod.
  reflexivity.
  all: lia.
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

Lemma wror_substitute w k : wror (SubWord w) k = SubWord (wror w k).
Proof.
  (* I would like to case on w, but not sure how to do this most efficiently? *)
Admitted.

Notation pr T l n := (coerce_to_choice_type T (nth (T ; chCanonical T) l n).π2).
Lemma wxorC {n} (a b : word n) : wxor a b = wxor b a.
Proof.
  apply/eqP/eq_from_wbit=> i. rewrite !wxorE.
  rewrite addbC. reflexivity.
Qed.

Lemma wreprI ws (a : word.word ws) : wrepr ws (toword a) = a.
Proof.
  apply val_inj. simpl. destruct a. rewrite Z.mod_small. reflexivity.
  simpl in *. lia.
Qed.

Lemma key_expand_aux rcon rkey temp2 rcon_ :
  toword rcon_ = rcon ->
  subword 0 U32 temp2 = word0 ->
  ((rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     (rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)) ⊕ wpshufd_128 (wAESKEYGENASSIST rkey (wrepr U8 rcon)) (wunsigned (wpack U8 2 [3; 3; 3; 3])) =
    key_expand rkey rcon_.
Proof.
  intros.
  subst.
  unfold key_expand.
  apply W4u32_eq.
  intros [[ | [ | [ | [ | i]]]] j]; simpl; unfold tnth; simpl.
  - rewrite !subword_xor.
    rewrite mul0n.
    unfold lift2_vec.
    rewrite !subword_0_32_128.
    simpl.
    rewrite mul0n.
    rewrite !make_vec_ws.
    rewrite !subword_u.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpack.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !wshr0.
    rewrite !subword_make_vec_32_0_32_128.
    simpl.
    unfold wAESKEYGENASSIST.
    rewrite subword_wshr.
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
    all: auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_1_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    rewrite subword_wshr.
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
    all: try auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_2_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpshufd1.
    rewrite subword_wshr.
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
    all: try auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_2_32_128.
    unfold wpshufd1.
    rewrite subword_wshr.
    simpl.
    rewrite !wxorA.
    f_equal.
    rewrite wxorC.
    rewrite !wxorA.
    f_equal.
    rewrite subword_wshr.
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
  subword 0 U32 temp2 = word0 ->
  subword 0 U32
    (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
       (word.wxor rkey (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey))) = word0.
Proof.
  intros.
  rewrite subword_0_32_128. simpl.
  rewrite subword_make_vec_32_0_32_128. simpl.
  unfold wpshufd1. simpl.
  rewrite subword_wshr. simpl.
  rewrite addn0.
  rewrite subword_u.
  rewrite subword_0_32_128. simpl.
  rewrite subword_make_vec_32_0_32_128. simpl.
  rewrite subword_u.
  unfold wpshufd1. simpl.
  rewrite subword_wshr.
  rewrite add0n.
  assumption.
  auto. auto.
Qed.

Lemma key_expandP pre id0 rcon rkey temp2 rcon_ :
  pdisj pre id0 fset0 →
  toword rcon_ = rcon →
  (forall s0 s1, pre (s0, s1) -> subword 0 U32 temp2 = word0) →
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
    JKEY_EXPAND id0 rcon rkey temp2
    ≈ ret tt
    ⦃ λ '(v0, s0) '(v1, s1),
      pre (s0, s1) ∧
        ∃ o1 o2,
          v0 = [ ('word U128 ; o1) ; ('word U128 ; o2) ] ∧
            o1 = key_expand rkey rcon_ ∧
            subword 0 U32 o2 = word0
    ⦄.
Proof.
  intros disj Hrcon Htemp2.
  simpl_fun.
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
    + apply key_expand_aux. reflexivity. eapply Htemp2. eassumption.
    + apply key_expand_aux2. eapply Htemp2. eassumption.
Qed.

Definition getmd {T S} m d i := match @getm T S m i with Some a => a | _ => d end.

Local Open Scope Z_scope.

Fixpoint for_list (c : Z → raw_code 'unit) (vs : seq Z) : raw_code 'unit :=
  match vs with
  | [::] => ret tt
  | v :: vs => c v ;; for_list c vs
  end.

Definition for_loop' (c : Z -> raw_code 'unit) lo hi := for_list c (wrange UpTo lo hi).

Definition to_oarr ws len (a : 'array) : (chMap (chFin len) ('word ws)) :=
  mkfmapf (fun (i : 'I_len) => chArray_get ws a i (wsize_size ws)) (ord_enum len).

Definition to_arr ws len (a : 'array) :=
  mkfmapf (fun i => chArray_get ws a i (wsize_size ws)) (ziota 0 len).

Lemma iota_aux {A} k c n (f : nat -> A) g :
  (forall a, a \in (iota k n) -> f a = g (a + c)%nat) ->
  [seq f i | i <- iota k n] = [seq g i | i <- iota (k + c) n].
Proof.
  revert k c.
  induction n.
  - reflexivity.
  - intros k c ex.
    simpl. rewrite -addSn.
    rewrite <- IHn.
    f_equal.
    apply ex.
    simpl.
    rewrite in_cons.
    apply/orP. left. apply/eqP. reflexivity.
    intros a ain. apply ex.
    simpl. rewrite in_cons.
    apply/orP. right. assumption.
Qed.

Lemma u_for_loop'_rule I c lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, _), I i s₀ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, _), I (Z.succ i) s₀ ⦄) →
  ⊢ ⦃ λ '(s₀, _), I lo s₀ ⦄
    for_loop' c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,_), I hi s₀ ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - simpl.
    assert (hi = lo).
    { zify. lia. }
    unfold for_loop'.
    simpl.
    rewrite -Heqn.
    simpl.
    subst.
    apply r_ret.
    easy.
  - unfold for_loop'.
    simpl. rewrite -Heqn. simpl. rewrite Z.add_0_r.
    eapply r_bind with (m₁ := ret tt) (f₁ := fun _ => _).
    + eapply h. lia.
    + intros a1 a2.
      destruct a1, a2.
      replace [seq lo + Z.of_nat i | i <- iota 1 n] with [seq (Z.succ lo) + Z.of_nat i | i <- iota 0 n].
      replace n with (Z.to_nat (hi - Z.succ lo)).
      eapply ih.
      * lia.
      * intros i hi2. apply h. lia.
      * lia.
      * lia.
      * replace (iota 1 n) with (iota (0 + 1) n). apply iota_aux.
        intros. lia.
        f_equal.
Qed.

Lemma u_for_loop'_rule' (I : Z -> heap -> Prop) c lo hi (pre : precond) :
  lo <= hi ->
  (forall h1 h2, pre (h1, h2) -> I lo h1) ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, _), I i s₀ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, _), I (Z.succ i) s₀ ⦄) →
  ⊢ ⦃ pre ⦄
    for_loop' c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,_), I hi s₀ ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  eapply u_for_loop'_rule.
  assumption.
  assumption.
  apply H0.
Qed.

Lemma for_loop'_rule I c₀ c₁ lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z -> ⊢ ⦃ λ '(s₀, s₁), I i (s₀, s₁) ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo (s₀, s₁) ⦄
    for_loop' c₀ lo hi ≈ for_loop' c₁ lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - simpl.
    assert (hi = lo).
    { zify. lia. }
    unfold for_loop'.
    simpl.
    rewrite -Heqn.
    simpl.
    subst.
    apply r_ret.
    easy.
  - unfold for_loop'.
    simpl. rewrite -Heqn. simpl. rewrite Z.add_0_r.
    eapply r_bind.
    + eapply h. lia.
    + intros a1 a2.
      replace [seq lo + Z.of_nat i | i <- iota 1 n] with [seq (Z.succ lo) + Z.of_nat i | i <- iota 0 n].
      replace n with (Z.to_nat (hi - Z.succ lo)).
      apply ih.
      * lia.
      * intros i hi2. apply h. lia.
      * lia.
      * lia.
      * replace (iota 1 n) with (iota (0 + 1) n). apply iota_aux.
        intros. lia.
        f_equal.
Qed.

Lemma translate_for_rule I lo hi (v : var_i) m_id s_id (body1 : p_id -> p_id * raw_code 'unit) body2 :
  (* it is annoying that this is a proof obligation, since its true for all translated programs, but I don't know how to prove the theorem without it *)
  (forall s_id', s_id' ⪯ (body1 s_id').1) ->
  lo <= hi ->
  (forall i s_id', (s_id ⪯ s_id') -> (lo <= i <  hi) ->
                   ⊢ ⦃ λ '(s₀, s₁), set_lhs (translate_var m_id v) (truncate_el (vtype v) (i : chInt)) (I i) (s₀, s₁) ⦄
                     let (_, body1') := body1 s_id' in
                     body1'
                       ≈ body2 i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀,s₁), I lo (s₀, s₁)⦄
    translate_for v (wrange UpTo lo hi) m_id body1 s_id
    ≈ for_loop' body2 lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros Hbody1 Hle ih.
  remember (Z.to_nat (hi - lo)).
  revert Heqn Hle ih. revert n lo hi s_id.
  induction n as [|n ih2]; intros.
  - assert (hi = lo). { zify. lia. }
    subst.
    unfold translate_for, for_loop'. simpl.
    rewrite -Heqn.
    simpl.
    apply r_ret.
    easy.
  - unfold translate_for, for_loop'.
    unfold wrange.
    rewrite -Heqn.
    simpl.
    specialize (ih lo s_id) as ih''.
    specialize (Hbody1 s_id).
    destruct (body1 s_id).
    eapply r_put_lhs.
    eapply r_bind.
    + eapply r_transL.
      2: rewrite Z.add_0_r; eapply ih''; [ reflexivity | lia ].
      eapply rreflexivity_rule.
    + intros a0 a1.
      replace (iota 1 n) with (iota (0 + 1) n) by f_equal.
      rewrite <- iota_aux with (f := fun i => Z.succ lo + Z.of_nat i) by lia.
      replace n with (Z.to_nat (hi - Z.succ lo)) by lia.
      specialize (ih2 (Z.succ lo) hi p ltac:(lia) ltac:(lia)).
      eapply ih2.
      intros i s_id' Hs_id' ile.
      specialize (ih i s_id').
      destruct (body1 s_id'). apply ih.
      etransitivity. eassumption. assumption.
      lia.
Qed.

Opaque translate_for.

From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
From Crypt Require Import Prelude Axioms ChoiceAsOrd.

Theorem rpre_hypothesis_rule' :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
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
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
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

Lemma wsize_size_aux (ws : wsize.wsize) :
  (ws %/ U8 + ws %% U8) = wsize_size ws.
Proof. destruct ws; reflexivity. Qed.

Lemma encode_aux {ws} (w : word.word ws) :
  LE.encode w = [seq subword ((Z.to_nat i0) * U8) U8 w | i0 <- ziota 0 (wsize_size ws)].
Proof.
  unfold LE.encode.
  unfold split_vec.
  unfold ziota.
  rewrite -wsize_size_aux.
  simpl.
  rewrite Z2Nat.inj_add.
  rewrite !Nat2Z.id.
  rewrite -map_comp.
  unfold comp.
  apply map_ext.
  intros a Ha.
  rewrite Nat2Z.id.
  reflexivity.
  apply Zle_0_nat.
  apply Zle_0_nat.
Qed.

Lemma wsize_size_bits ws:
  wsize_size ws < wsize_bits ws.
Proof.
  unfold wsize_size, wsize_bits.
  destruct ws; simpl; lia.
Qed.

Lemma chArray_get_set_eq ws a i w :
  (* (i * wsize_bits ws < wsize_size ws) -> *)
  chArray_get ws (chArray_set a AAscale i w) i (wsize_size ws) = w.
Proof.
  unfold chArray_get.
  unfold chArray_set.
  rewrite <- LE.decodeK.
  f_equal.
  rewrite encode_aux.
  apply map_ext.
  intros j Hj.
  unfold chArray_get8.
  rewrite chArray_write_get.
  assert ((0 <=? i * wsize_size ws + j - i * mk_scale AAscale ws) && (i * wsize_size ws + j - i * mk_scale AAscale ws <? wsize_size ws)).
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.  lia.
  rewrite H.
  unfold LE.wread8.
  unfold LE.encode.
  unfold split_vec.
  unshelve erewrite nth_map. exact 0%nat.
  simpl.
  rewrite nth_iota.
  simpl.
  f_equal.
  lia.
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)). lia.
  destruct ws; simpl; reflexivity.
  rewrite size_iota.
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)). lia.
  destruct ws; simpl; reflexivity.
Qed.

Lemma chArray_get_set_neq ws a i j (w : 'word ws) :
  i <> j ->
  chArray_get ws (chArray_set a AAscale i w) j (wsize_size ws) = chArray_get ws a j (wsize_size ws).
Proof.
  intros H.
  unfold chArray_get.
  unfold chArray_set.
  f_equal.
  apply map_ext.
  intros a0 Ha0.
  unfold chArray_get8.
  rewrite chArray_write_get.
  assert ((0 <=? j * wsize_size ws + a0 - i * mk_scale AAscale ws) && (j * wsize_size ws + a0 - i * mk_scale AAscale ws <? wsize_size ws) = false).
  simpl. move: Ha0=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  nia.
  rewrite H0.
  reflexivity.
Qed.

Lemma getm_to_arr_None' ws len a (i: Z) :
  ((len <=? i) || (i <? 0)) ->
  to_arr ws len a i = None.
Proof.
  intros. unfold to_arr.
  rewrite mkfmapfE.
Admitted.                  (* figure out a proof that is less stupid than the one for getm_to_arr *)

Lemma getm_to_oarr ws len a (i : 'I_(pos len)) :
  to_oarr ws len a i = Some (chArray_get ws a i (wsize_size ws)).
Proof.
  unfold to_oarr.
  rewrite mkfmapfE.
  rewrite mem_ord_enum.
  reflexivity.
Qed.

Lemma getm_to_arr ws len a i :
  (0 <= i < len) ->
  to_arr ws len a i = Some (chArray_get ws a i (wsize_size ws)).
Proof.
  unfold to_arr.
  rewrite mkfmapfE.
  intros H.
  (* this is a stupid proof and should be true by in_ziota, though for some reason the \in's resolve differently (one uses Z_eqType the other Z_ordType) *)
  assert (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota Z0 len)))).
  { assert (0 <= len) by lia. move: H. move: (Z.le_refl 0). replace len with (0 + len) at 1 by (now rewrite Z.add_0_l). generalize 0 at 2 3 4 5.
    change (∀ z : Z, 0 <= z -> z <= i < z + len →
                     (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota z len))))
           ) with ((fun len => ((forall z, 0 <= z -> z <= i < z + len ->
                                           (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota z len))))
                   ))) len).
    apply natlike_ind.
    - intros z Hz Hz2. lia.
    - intros x Hx Ih z Hz Hz2. rewrite ziotaS_cons.
      destruct (Z.eq_dec z i).
      + rewrite in_cons. apply/orP. left. apply/eqP. easy.
      + rewrite in_cons. apply/orP. right. apply Ih. lia. lia.
      + lia.
    - assumption. }
  rewrite H0.
  reflexivity.
Qed.

Lemma to_oarr_set_eq ws len a (i : 'I_(pos len)) w :
  (* (0 <= i < len) -> *)
  (to_oarr ws len (chArray_set a AAscale i w)) i = Some w.
Proof.
  rewrite getm_to_oarr.
  rewrite chArray_get_set_eq.
  reflexivity.
Qed.

Lemma to_arr_set_eq ws len a i w :
  (0 <= i < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) i = Some w.
Proof.
  intros H.
  rewrite getm_to_arr.
  rewrite chArray_get_set_eq.
  reflexivity.
  assumption.
Qed.

Lemma to_arr_set_neq' ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = Some (chArray_get ws a j (wsize_size ws)).
Proof.
  intros Hneq H.
  rewrite getm_to_arr.
  rewrite chArray_get_set_neq.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma to_arr_set_neq ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = (to_arr ws len a) j.
Proof.
  intros Hneq H.
  rewrite !getm_to_arr.
  rewrite chArray_get_set_neq.
  reflexivity.
  assumption.
  assumption.
  assumption.
Qed.

(* TODO: move these, note they are the same as fresh1 and fresh2 *)
Lemma prec_O :
  forall i, i ≺ i~0.
Proof.
  simpl; split.
  - apply preceq_O.
  - apply nesym. apply xO_neq.
Qed.

Lemma prec_I :
  forall i, i ≺ i~1.
Proof.
  simpl; split.
  - apply preceq_I.
  - apply nesym. apply xI_neq.
Qed.

(* Notation " 'arr ws len " := (chMap (chFin len) ('word ws)) (at level 2) : package_scope. *)

(* Definition rkeys : Location := ( (chMap (chFin (mkpos 11)) ('word U128)) ; 0%nat ). *)

(* Definition keyExpansion (key : u128) : raw_code (chMap (chFin (mkpos 11)) ('word U128)):= *)
(*  #put rkeys := @emptym (chElement_ordType (chFin (mkpos 11))) u128 ;; *)
(*  rkeys0 ← get rkeys ;; *)
(*  #put rkeys := setm rkeys0 (inord 0) key ;; *)
(*  for_loop' (fun i => rkeys0 ← get rkeys ;; #put rkeys := setm rkeys0 (inord (Z.to_nat i)) (key_expand (zero_extend _ (getmd rkeys0 word0 (inord (Z.to_nat i - 1)))) (wrepr U8 (rcon i))) ;; ret tt) 1 11 ;; *)
(*  rkeys0 ← get rkeys ;; *)
(*  ret rkeys0. *)

Notation " 'arr ws " := (chMap 'int ('word ws)) (at level 2) : package_scope.

Definition rkeys : Location := ( 'arr U128 ; 0%nat ).

Definition keyExpansion (key : u128) : raw_code ('arr U128) :=
 #put rkeys := @emptym (chElement_ordType 'int) u128 ;;
 rkeys0 ← get rkeys ;;
 #put rkeys := setm rkeys0 0 key ;;
 for_loop' (fun i =>
   rkeys0 ← get rkeys ;;
   #put rkeys := setm rkeys0 i (key_expand (zero_extend _ (getmd rkeys0 word0 (i - 1))) (rcon i)) ;;
   ret tt) 1 11 ;;
 rkeys0 ← get rkeys ;;
 ret rkeys0.

Definition key_i  (k : u128) i :=
  iteri i (fun i ki => key_expand ki (rcon (i + 1))) k.

From extructures Require Import ord.

Lemma aes_keyExpansion_h k :
  ⊢ ⦃ fun '(h0, h1) => True ⦄
    keyExpansion k
    ≈
    ret tt
    ⦃ fun '(v0, h0) '(_, _) => forall i, 0 <= i < 11 -> (getmd v0 word0 i) = key_i k (Z.to_nat i) ⦄.
Proof.
  unfold keyExpansion.
  eapply r_put_lhs with (pre := fun _ => _).
  eapply r_get_remember_lhs. intros x.
  eapply r_put_lhs.
  eapply r_bind with (m₁ := ret _).
  eapply u_for_loop'_rule' with
    (I:= fun i => fun h => forall j, 0 <= j < i -> getmd (get_heap h rkeys) word0 j = key_i k (Z.to_nat j)).
lia.
  - intros i ile Hpre.
    destruct_pre.
    intros j Hj.
    rewrite !get_set_heap_eq.
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
    destruct_pre.
    intros j Hj.
    rewrite get_set_heap_eq.
    rewrite -> H4 by lia.
    unfold getmd in *.
    rewrite setmE.
    destruct (Z.eq_dec j i).
    + subst.
      rewrite eq_refl.
      rewrite zero_extend_u.
      replace (Z.to_nat i) with (Z.to_nat (i - 1)).+1 by lia.
      unfold key_i at 2.
      rewrite iteriS.
      f_equal. f_equal. simpl. lia.
    + assert (@eq_op (Ord.eqType Z_ordType) j i = false).
      apply/eqP. assumption.
      rewrite H0.
      rewrite H4.
      reflexivity.
      lia.
  - intros s0 s1.
    eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x0.
    eapply r_ret.
    intros s2 s3 Hpre i Hi.
    destruct_pre.
    apply H1. lia.
Qed.
(* hoare aes_keyExpansion_h k : *)
(*   Aes.keyExpansion : key = k *)
(*   ==> *)
(*   forall i, 0 <= i < 11 => res.[i] = key_i k i. *)
(* proof. *)
(*   proc. *)
(*   while (1 <= round <= 11 /\ forall i, 0 <= i < round => rkeys.[i] = key_i k i). *)
(*   + by auto => />; smt (key_iE iteriS get_setE). *)
(*   by auto => />; smt(key_iE iteri0 get_setE). *)
(* qed. *)

Lemma u_trans_det :
  ∀ {A₀ A₁ : ord_choiceType}
    (P P0 P1 : precond)
    (Q : A₀ -> A₁ -> Prop) (Q0 : A₀ -> Prop) (Q1 : A₁ -> Prop)
    (c₀ : raw_code A₀) (c₁ : raw_code A₁),
    (forall h0 h1, P (h0, h1) -> P0 (h0, h1)) ->
    (forall h0 h1, P1 (h1, h0) -> P (h0, h1)) ->
    (forall v0 v1, Q v0 v1 -> Q0 v0 -> Q1 v1) ->
    deterministic c₀ →
    deterministic c₁ →
    ⊢ ⦃ λ '(h₀, h₁), P (h₀, h₁) ⦄ c₀ ≈ c₁ ⦃ λ '(v₀, _) '(v₁, _), Q v₀ v₁ ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), P0 (h₀, h₁) ⦄ c₀ ≈ ret tt ⦃ λ '(v₀, _) '(_ , _), Q0 v₀ ⦄ ->
    ⊢ ⦃ λ '(h₀, h₁), P1 (h₀, h₁) ⦄ c₁ ≈ ret tt ⦃ λ '(v₀, _) '(_ , _), Q1 v₀ ⦄.
Proof.
  intros A₀ A₁ P P0 P1 Q Q0 Q1 c0 c1 HP0 HP1 HQ Hd0 Hd1 Hc Hc0.
  unshelve eapply det_to_sem. assumption. constructor.
  unshelve eapply sem_to_det in Hc. 1,2: assumption.
  unshelve eapply sem_to_det in Hc0. assumption. constructor.
  intros s₀ s₁ hP1. eapply HP1 in hP1 as HP. eapply HP0 in HP as hP0.
  specialize (Hc s₁ s₀ HP). specialize (Hc0 s₁ s₀ hP0).
  destruct (det_run c0 _).
  destruct (det_run c1 _).
  simpl in *.
  eapply HQ. eassumption. eassumption.
Qed.

Lemma u_trans_det' :
  ∀ {A₀ A₁ : ord_choiceType}
    (P P0 P1 : precond)
    (Q : A₁ -> A₀ -> Prop) (Q0 : A₀ -> Prop) (Q1 : A₁ -> Prop)
    (c₀ : raw_code A₀) (c₁ : raw_code A₁),
    (forall h0 h1, P (h1, h0) -> P0 (h0, h1)) ->
    (forall h0 h1, P1 (h1, h0) -> P (h1, h0)) ->
    (forall v1 v0, Q v1 v0 -> Q0 v0 -> Q1 v1) ->
    deterministic c₀ →
    deterministic c₁ →
    ⊢ ⦃ λ '(h₀, h₁), P (h₀, h₁) ⦄ c₁ ≈ c₀ ⦃ λ '(v₀, _) '(v₁, _), Q v₀ v₁ ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), P0 (h₀, h₁) ⦄ c₀ ≈ ret tt ⦃ λ '(v₀, _) '(_ , _), Q0 v₀ ⦄ ->
    ⊢ ⦃ λ '(h₀, h₁), P1 (h₀, h₁) ⦄ c₁ ≈ ret tt ⦃ λ '(v₀, _) '(_ , _), Q1 v₀ ⦄.
Proof.
  intros A₀ A₁ P P0 P1 Q Q0 Q1 c0 c1 HP0 HP1 HQ Hd0 Hd1 Hc Hc0.
  unshelve eapply det_to_sem. assumption. constructor.
  unshelve eapply sem_to_det in Hc. 1,2: assumption.
  unshelve eapply sem_to_det in Hc0. assumption. constructor.
  intros s₀ s₁ hP1. eapply HP1 in hP1 as HP. eapply HP0 in HP as hP0.
  specialize (Hc s₀ s₁ HP). specialize (Hc0 s₁ s₀ hP0).
  destruct (det_run c0 _).
  destruct (det_run c1 _).
  simpl in *.
  eapply HQ. eassumption. eassumption.
Qed.

Lemma keyExpansionE pre id0 rkey :
  (pdisj pre id0 [fset rkeys]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JKEYS_EXPAND id0 rkey
    ≈
    keyExpansion rkey
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ (to_arr U128 (mkpos 11) (hdtc v0)) = v1 ⦄.
Proof.
  intros disj.
  unfold translate_call.
  unfold translate_call_body.

  Opaque translate_call.
  Opaque wrange.
  Opaque for_loop'.

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
                                        /\ subword 0 U32 (get_heap h0 temp2) = word0
                                        /\ (get_heap h0 key = chArray_get U128 (get_heap h0 rkeys) (i - 1) 16)
                                        /\ (forall j, (0 <= j < i) -> (to_arr U128 (mkpos 11) (get_heap h0 rkeys)) j = (get_heap h1 aes.rkeys) j)
                                        /\ (forall j, (j < 0) \/ (11 <= j) -> get_heap h1 aes.rkeys j = None)).

      (* the two following bullets are small assumptions of the translate_for rule *)
      * intros. simpl. solve_preceq.
      * lia.
      (* Inductive step of the for loop rule, we have to prove the bodies are equivalent and imply the successor predicate *)
      * intros i s_id Hs_id ile.
        ssprove_code_simpl.

        (* NB: Do not rewrite here, since it breaks unification when trying to apply other correctness lemmas *)
        (* rewrite !coerce_to_choice_type_K. *)

        eapply r_get_remember_lhs. intros.

        (* Now we apply the correctnes of rcon *)
        eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).
        ** eapply rcon_correct with (id0 := (s_id~1)%positive) (i:=x).
           (* We have to prove the precond is disjoint from the variables of rcon, i.e. any variables stored locally in rcon does not change the precond *)
           *** split.
               (* rcon_correct does not use any variables on the rhs *)
               2: { easy. }
               intros s0 s1 l a vr s_id' Hl Hs_id' H.
               assert (id0_preceq : id0 ⪯ s_id'). {
                 etransitivity. eapply preceq_I. etransitivity. eassumption. etransitivity. eapply preceq_I. eassumption.
               }
               assert (id0_neq : id0 <> s_id'). {
                 apply prec_neq. eapply prec_preceq_trans. eapply preceq_prec_trans. etransitivity. eapply preceq_I. eassumption. eapply prec_I. assumption.
               }
               intros. destruct_pre. split_post.
               { eapply disj. reflexivity. eassumption. eassumption. }
               { sheap. assumption. }
               { sheap. assumption. }
               { sheap. assumption. }
               { assumption. }
               { rewrite set_heap_commut. reflexivity.
                 apply injective_translate_var2. assumption. }
               { simpl. sheap. reflexivity. }
           (* this is an assumption of rcon_correct *)
           *** intros; destruct_pre. fold round. sheap. rewrite coerce_to_choice_type_K. lia.
        (* we continue after the rcon call *)
        ** intros a0 a1.
           simpl; ssprove_code_simpl.
           (* we need to know the value of a0 here *)
           eapply rpre_weak_hypothesis_rule'; intros.
           destruct_pre; simpl.
           repeat clear_get.
           eapply r_put_lhs with (pre := λ '(s0',s1'), _ ).
           eapply r_get_remember_lhs. intros x0.
           eapply r_get_remember_lhs. intros x1.
           sheap.

           eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).

           (* First we apply correctness of key_expandP *)
           *** (* Here the rewrite is necessary. How should correctness be phrased in general such that this is not important? *)
               rewrite !coerce_to_choice_type_K.
               eapply key_expandP with (id0 := (s_id~0~1)%positive) (rcon := (wunsigned (rcon i))) (rkey := x0) (temp2 := x1) (rcon_ := rcon i).
               (* again, we have to prove that our precond does not depend key_expand locations *)
               { split.
                 (* key_expandP also does not use variables on the rhs *)
                 2: { easy. }
                 intros s0 s1 l a vr s_id' Hl Hs_id' H1.
                 assert (id0_preceq : id0 ⪯ s_id'). {
                 etransitivity. eapply preceq_I. etransitivity. eassumption. etransitivity. eapply preceq_O. etransitivity. eapply preceq_I. eassumption.
                 }
                 assert (id0_neq : id0 <> s_id'). {
                   apply prec_neq. eapply prec_preceq_trans. eapply preceq_prec_trans. etransitivity. eapply preceq_I. eassumption. eapply prec_O. etransitivity. eapply prec_I. assumption.
                 }
                 destruct_pre. sheap. split_post.
                 { eapply disj. reflexivity. eassumption. eassumption. }
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
               eapply rpre_weak_hypothesis_rule'.
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
                 subst. simpl.
                 pose proof to_arr_set_eq.
                 simpl.
                 rewrite to_arr_set_eq.
                 rewrite setmE. rewrite eq_refl.

                 f_equal. unfold getmd. rewrite -H41. rewrite getm_to_arr.
                 f_equal. rewrite !get_set_heap_neq in H33. rewrite -H33. assumption.
                 neq_loc_auto. neq_loc_auto. lia. lia. lia.

                 (* i <> j *)
                 rewrite to_arr_set_neq.
                 rewrite setmE.
                 assert (@eq bool (@eq_op Z_ordType j i) false). apply/eqP. auto.
                 rewrite H3.
                 apply H41. lia. assumption. lia. }
               { intros j Hj.

                 rewrite setmE.
                 (* why do I have to set printing off to realize this? Shouldn't j == i always mean the same on the same type? *)
                 assert (@eq_op (Ord.eqType Z_ordType) j i = false). apply/eqP. lia.
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
        rewrite to_arr_set_eq. rewrite setmE. rewrite eq_refl. reflexivity. lia.
      * intros. rewrite setmE.
        (* Set Printing All. *)
        replace (_ == _) with false.
        apply emptymE. symmetry. apply/eqP. lia.
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
    + eapply eq_fmap. intros j.
      destruct ((0 <=? j) && (j <? 11)) eqn:E.
      (* within bounds, this follows from the precondition *)
      * rewrite !coerce_to_choice_type_K. apply H4. lia.
      * rewrite -> getm_to_arr_None' by lia.
        rewrite H6. reflexivity.
        lia.
Qed.

(* without the pre in the post, try to remove this and generalize lemmas instead *)
Lemma keyExpansionE' pre id0 rkey :
  (pdisj pre id0 [fset rkeys]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JKEYS_EXPAND id0 rkey
    ≈
    keyExpansion rkey
    ⦃ fun '(v0, _) '(v1, _) => (to_arr U128 (mkpos 11) (hdtc v0)) = v1 ⦄.
Proof.
  intros.
  eapply rpost_weaken_rule.
  eapply keyExpansionE.
  assumption.
  intros.
  destruct a₀, a₁.
  easy.
Qed.

(* maybe extend this to also preserve a precond, to do this prove a similar `u_trans_det` *)
Lemma keys_expand_jazz_correct pre id0 rkey :
  (pdisj pre id0 [fset rkeys]) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JKEYS_EXPAND id0 rkey
    ≈
    ret tt
    ⦃ fun '(v0, _) '(_, _) => forall i, 0 <= i < 11 -> getmd (to_arr U128 (mkpos 11) (hdtc v0)) word0 i = key_i rkey (Z.to_nat i) ⦄.
Proof.
  intros h.
  eapply u_trans_det' with (P0 := fun '(_, _) => True) (P1 := fun '(_, _) => _).
  7: { eapply aes_keyExpansion_h. }
  6: { eapply keyExpansionE'. eassumption. }
  - easy.
  - easy.
  - intros. simpl in *. rewrite H. apply H0. assumption.
  - unfold keyExpansion.
    repeat constructor.
  - admit.                      (* TODO: figure out how to do this *)
Admitted.

Definition aes (key msg : u128) :=
  let state := wxor msg (key_i key 0) in
  let state := iteri 9 (fun i state => AESENC_ state (key_i key (i + 1))) state in
  AESENCLAST_ state (key_i key 10).

Definition invaes (key cipher : u128) :=
  let state := wxor cipher (key_i key 10) in
  let state := iteri 9 (fun i state => AESDEC_ state (key_i key (10 -(i + 1)))) state in
  wAESDECLAST state (key_i key 0).

(* Definition rkeys : Location := () *)
(* Definition (rkeys : chMap 'int ('word U128)) (msg : 'word U128) := *)
Definition state : Location := ( 'word U128 ; 0%nat).

Definition aes_rounds (rkeys : 'arr U128) (msg : 'word U128) :=
    #put state := wxor msg (getmd rkeys word0 0) ;;
    for_loop' (fun i =>
      state0 ← get state ;;
      #put state := AESENC_ state0 (getmd rkeys word0 i) ;;
      ret tt
    ) 1 10 ;;
    state0 ← get state ;;
    #put state := AESENCLAST_ state0 (getmd rkeys word0 10) ;;
    state0 ← get state ;;
    ret state0.

Lemma aes_rounds_h rkeys k m :
  (forall i, 0 <= i < 11 -> getmd rkeys word0 i = key_i k (Z.to_nat i)) ->
  ⊢ ⦃ fun '(_, _) => True ⦄
  aes_rounds rkeys m
  ≈
  ret tt
  ⦃ fun '(v0, _) '(_, _) => v0 = aes k m ⦄.
Proof.
  unfold aes_rounds.
  intros H.
  eapply r_put_lhs with (pre := fun _ => _).
  eapply r_bind with (m₁ := ret _).
  set (st0 := m ⊕ (key_i k 0%nat)).
  eapply u_for_loop'_rule' with
    (I := fun i => fun h => get_heap h state = iteri (Z.to_nat i - 1) (fun i state => AESENC_ state (key_i k (i + 1))) st0).
  - lia.
  - intros.
    simpl.
    destruct_pre. sheap. rewrite H. reflexivity. lia.
  - intros i Hi.
    eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x.
    eapply r_put_lhs. eapply r_ret.
    intros s0 s1 pre.
    destruct_pre; sheap.
    replace (Z.to_nat (Z.succ i) - 1)%nat with ((Z.to_nat i - 1).+1) by lia.
    rewrite iteriS.
    rewrite H5.
    rewrite H. repeat f_equal. lia. lia.
  - intros a0 a1.
    eapply r_get_remember_lhs with (pre := fun '(_, _) => _). intros x.
    eapply r_put_lhs.
    eapply r_get_remember_lhs. intros x0.
    eapply r_ret.
    intros s0 s1 pre.
    Opaque getmd.
    destruct pre as [[s2 [[H4 H3] H2]] H1].
    simpl in H3, H1. subst.
    sheap.
    unfold aes.
    rewrite H4.
    rewrite H.
    replace ((Z.to_nat 10) - 1)%nat with 9%nat by reflexivity.
    reflexivity. lia.
Qed.
