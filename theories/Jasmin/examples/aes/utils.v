Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra zify.
From mathcomp Require Import word_ssrZ word.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 ZArith micromega.Lia List.

From Jasmin Require Import expr xseq.
From JasminSSProve Require Import jasmin_translate.

From Relational Require Import OrderEnrichedCategory.
From Crypt Require Import Prelude Package ChoiceAsOrd.

From extructures Require Import ord fset fmap.

Import ListNotations.
Import JasminNotation.
Import PackageNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!". 
 
(** For loops  *)

Local Open Scope Z. 

Fixpoint for_list (c : Z → raw_code 'unit) (vs : seq Z) : raw_code 'unit :=
  match vs with
  | [::] => ret tt
  | v :: vs => c v ;; for_list c vs
  end.

Definition for_loop (c : Z -> raw_code 'unit) lo hi := for_list c (wrange UpTo lo hi).

Lemma iota_aux {A} k c n (f : nat -> A) g :
  (forall a, a \in (iota k n) -> f a = g (a + c)%nat) ->
  [seq f i | i <- iota k n] = [seq g i | i <- iota (k + c) n].
Proof.
  revert k c.
  induction n.
  - reflexivity.
  - intros k c ex.
    simpl. rewrite -addSn -IHn.
    + f_equal.
      apply ex.
      rewrite in_cons eq_refl => //=.
    + intros a ain. apply ex.
      simpl. rewrite in_cons.
      apply/orP. right. assumption.
Qed.

Lemma u_for_loop_rule I c lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, s₁), I i s₀ s₁ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) s₀ s₁ ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo s₀ s₁ ⦄
    for_loop c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,s₁), I hi s₀ s₁ ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - assert (hi = lo) by lia.
    unfold for_loop=>/=.
    rewrite -Heqn.
    subst.
    apply r_ret. easy.
  - unfold for_loop=>/=.
    rewrite -Heqn. simpl. rewrite Z.add_0_r.
    eapply r_bind with (m₁ := ret tt) (f₁ := fun _ => _).
    + eapply h. lia.
    + intros a1 a2.
      destruct a1, a2.
      replace [seq lo + Z.of_nat i | i <- iota 1 n] with [seq (Z.succ lo) + Z.of_nat i | i <- iota 0 n].
      2: { replace (iota 1 n) with (iota (0 + 1) n) by f_equal. apply iota_aux. intros. lia. }
      replace n with (Z.to_nat (hi - Z.succ lo)) by lia.
      eapply ih.
      all: try lia.
      intros i hi2. apply h. lia.
Qed.

Lemma u_for_loop_rule_weaken (I : Z -> heap -> heap -> Prop) c lo hi (pre : precond) :
  lo <= hi ->
  (forall h1 h2, pre (h1, h2) -> I lo h1 h2) ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, s₁), I i s₀ s₁ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) s₀ s₁ ⦄) →
  ⊢ ⦃ pre ⦄
    for_loop c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,s₁), I hi s₀ s₁ ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  1: eapply u_for_loop_rule; eauto.
  assumption.
Qed.

Lemma for_loop_rule I c₀ c₁ lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z -> ⊢ ⦃ λ '(s₀, s₁), I i (s₀, s₁) ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo (s₀, s₁) ⦄
    for_loop c₀ lo hi ≈ for_loop c₁ lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - assert (hi = lo) by lia.
    unfold for_loop=>/=.
    rewrite -Heqn.
    subst.
    apply r_ret. easy.
  - unfold for_loop=>/=.
    rewrite -Heqn. simpl. rewrite Z.add_0_r.
    eapply r_bind. 
    + eapply h. lia.
    + intros a1 a2.
      destruct a1, a2.
      replace [seq lo + Z.of_nat i | i <- iota 1 n] with [seq (Z.succ lo) + Z.of_nat i | i <- iota 0 n].
      2: { replace (iota 1 n) with (iota (0 + 1) n) by f_equal. apply iota_aux. intros. lia. }
      replace n with (Z.to_nat (hi - Z.succ lo)) by lia.
      eapply ih.
      all: try lia.
      intros i hi2. apply h. lia.
Qed.

Lemma translate_for_rule I lo hi (v : var_i) m_id s_id (body1 : p_id -> p_id * raw_code 'unit) body2 :
  (* it is annoying that this is a proof obligation, since its true for all translated programs, but I don't know how to prove the theorem without it *)
  (forall s_id', s_id' ⪯ (body1 s_id').1) ->
  lo <= hi ->
  (forall i s_id', (s_id ⪯ s_id') -> (lo <= i <  hi) ->
                ⊢ ⦃ λ '(s₀, s₁), set_lhs (translate_var m_id v) (truncate_el (vtype v) (i : chInt)) (I i) (s₀, s₁) ⦄
                    let (_, body1') := body1 s_id' in
                    body1' ≈ body2 i
                ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀,s₁), I lo (s₀, s₁)⦄
    translate_for v (wrange UpTo lo hi) m_id body1 s_id
    ≈ for_loop body2 lo hi
  ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros Hbody1 Hle ih.
  remember (Z.to_nat (hi - lo)).
  revert Heqn Hle ih. revert n lo hi s_id.
  induction n as [|n ih2]; intros.
  - assert (hi = lo). { zify. lia. }
    subst.
    unfold translate_for, for_loop. simpl.
    rewrite -Heqn.
    simpl.
    apply r_ret.
    easy.
  - unfold translate_for, for_loop.
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
      1: etransitivity; eauto. 
      lia.
Qed.

Lemma translate_for_rule_weaken (pre : precond) (I : Z -> heap * heap -> Prop) lo hi (v : var_i) m_id s_id (body1 : p_id -> p_id * raw_code 'unit) body2 :
  (forall h0 h1, pre (h0, h1) -> I lo (h0, h1)) ->
  (* it is annoying that this is a proof obligation, since its true for all translated programs, but I don't know how to prove the theorem without it *)
  (forall s_id', s_id' ⪯ (body1 s_id').1) ->
  lo <= hi ->
  (forall i s_id', (s_id ⪯ s_id') -> (lo <= i <  hi) ->
                   ⊢ ⦃ λ '(s₀, s₁), set_lhs (translate_var m_id v) (truncate_el (vtype v) (i : chInt)) (I i) (s₀, s₁) ⦄
                     let (_, body1') := body1 s_id' in
                     body1'
                       ≈ body2 i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ pre ⦄
    translate_for v (wrange UpTo lo hi) m_id body1 s_id
    ≈ for_loop body2 lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  1: eapply translate_for_rule.
  all: easy.
Qed.

(** Arrays *)

Definition getmd {T S} m d i := match @getm T S m i with Some a => a | _ => d end.

Definition to_oarr ws len (a : 'array) : (chMap (chFin len) ('word ws)) :=
  mkfmapf (fun (i : 'I_len) => chArray_get ws a (Z.of_nat i) (wsize_size ws)) (ord_enum len).
Definition to_arr ws len (a : 'array) :=
  mkfmapf (fun i => chArray_get ws a i (wsize_size ws)) (ziota 0 len).

Lemma wsize_size_aux (ws : wsize.wsize) :
  (ws %/ U8 + ws %% U8)%nat = Z.to_nat (wsize_size ws).
Proof. destruct ws; reflexivity. Qed.

Lemma encode_aux {ws} (w : word.word ws) :
  LE.encode w = [seq word.subword ((Z.to_nat i0) * U8) U8 w | i0 <- ziota 0 (wsize_size ws)].
Proof.
  unfold LE.encode.
  unfold split_vec.
  unfold ziota.
  rewrite -wsize_size_aux.
  simpl.
  (* rewrite Z2Nat.inj_add. *)
  (* rewrite !Nat2Z.id. *)
  rewrite -map_comp.
  unfold comp.
  apply map_ext.
  intros a Ha.
  rewrite Nat2Z.id.
  reflexivity.
  (* apply Zle_0_nat. *)
  (* apply Zle_0_nat. *)
Qed.

Lemma wsize_size_bits ws:
  wsize_size ws < wsize_bits ws.
Proof.
  unfold wsize_size, wsize_bits.
  destruct ws; simpl; lia.
Qed.

Lemma chArray_get_set_eq ws a i w :
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
  { simpl. move: Hj=> /InP. rewrite in_ziota=>/andP [] H1 h2. lia. }
  rewrite H.
  unfold LE.wread8.
  unfold LE.encode.
  unfold split_vec.
  unshelve erewrite nth_map. 1: exact 0%nat.
  { simpl.
    rewrite nth_iota.
    1: f_equal; lia.
    simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
    replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)); [lia|].
    destruct ws; simpl; reflexivity. }
  rewrite size_iota.
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)); [lia|].
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
  { simpl. move: Ha0=>/InP. rewrite in_ziota=>/andP [] H1 h2. nia. }
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
    - intros x Hx Ih z Hz Hz2. rewrite ziotaS_cons. 2: lia.
      destruct (Z.eq_dec z i).
      + rewrite in_cons. apply/orP. left. apply/eqP. easy.
      + rewrite in_cons. apply/orP. right. apply Ih. all: lia. 
    - assumption. }
  rewrite H0.
  reflexivity.
Qed.

Lemma to_oarr_set_eq ws len a (i : 'I_(pos len)) w :
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
  rewrite getm_to_arr; auto.
  rewrite chArray_get_set_eq; auto.
Qed.

Lemma to_arr_set_neq' ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = Some (chArray_get ws a j (wsize_size ws)).
Proof.
  intros Hneq H.
  rewrite getm_to_arr; auto.
  rewrite chArray_get_set_neq; auto.
Qed.

Lemma to_arr_set_neq ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = (to_arr ws len a) j.
Proof.
  intros Hneq H.
  rewrite !getm_to_arr; auto.
  rewrite chArray_get_set_neq; auto.
Qed.

(** Additional rules *)

Theorem rpre_weak_hypothesis_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁,
      pre (s₀, s₁) → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ p₀ ≈ p₁ ⦃ post ⦄
    ) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post h.
  eapply rpre_hypothesis_rule.
  intros. eapply rpre_weaken_rule.
  1: eapply h; eauto. 
  intros s0' s1' [H0 H1].
  subst.
  assumption.
Qed.

(** Misc (TODO: move these) *)

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
