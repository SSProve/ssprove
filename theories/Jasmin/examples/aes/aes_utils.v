Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra zify.
From mathcomp.word Require Import word ssrZ.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 ZArith micromega.Lia List.

From Jasmin Require Import sem.

Context
  {pd : PointerData}
  {fcp : FlagCombinationParams}.

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

(** Notations *)

Module AesNotation.
  Notation " 'arr ws " := (chMap 'int ('word ws)) (at level 2) : package_scope.
End AesNotation.

(** For loops  *)

Local Open Scope Z. 

Fixpoint for_list (c : Z → raw_code 'unit) (vs : seq Z) : raw_code 'unit :=
  match vs with
  | [::] => ret tt
  | v :: vs => c v ;; for_list c vs
  end.

Definition lfor_loop (c : Z -> raw_code 'unit) lo hi := for_list c (wrange UpTo lo hi).

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

Lemma u_lfor_loop_rule I c lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, s₁), I i s₀ s₁ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) s₀ s₁ ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo s₀ s₁ ⦄
    lfor_loop c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,s₁), I hi s₀ s₁ ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - assert (hi = lo) by lia.
    unfold lfor_loop=>/=.
    rewrite -Heqn.
    subst.
    apply r_ret. easy.
  - unfold lfor_loop=>/=.
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

Lemma u_lfor_loop_rule_weaken (I : Z -> heap -> heap -> Prop) c lo hi (pre : precond) :
  lo <= hi ->
  (forall h1 h2, pre (h1, h2) -> I lo h1 h2) ->
  (∀ i, (lo <= i < hi)%Z ->
        ⊢ ⦃ λ '(s₀, s₁), I i s₀ s₁ ⦄
          c i ≈ ret tt
          ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) s₀ s₁ ⦄) →
  ⊢ ⦃ pre ⦄
    lfor_loop c lo hi ≈ ret tt
    ⦃ λ '(_,s₀) '(_,s₁), I hi s₀ s₁ ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  1: eapply u_lfor_loop_rule; eauto.
  assumption.
Qed.

Lemma lfor_loop_rule I c₀ c₁ lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z -> ⊢ ⦃ λ '(s₀, s₁), I i (s₀, s₁) ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo (s₀, s₁) ⦄
    lfor_loop c₀ lo hi ≈ lfor_loop c₁ lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - assert (hi = lo) by lia.
    unfold lfor_loop=>/=.
    rewrite -Heqn.
    subst.
    apply r_ret. easy.
  - unfold lfor_loop=>/=.
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
    ≈ lfor_loop body2 lo hi
  ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros Hbody1 Hle ih.
  remember (Z.to_nat (hi - lo)).
  revert Heqn Hle ih. revert n lo hi s_id.
  induction n as [|n ih2]; intros.
  - assert (hi = lo). { zify. lia. }
    subst.
    unfold translate_for, lfor_loop. simpl.
    rewrite -Heqn.
    simpl.
    apply r_ret.
    easy.
  - unfold translate_for, lfor_loop.
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
    ≈ lfor_loop body2 lo hi
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
  rewrite -map_comp.
  unfold comp.
  apply map_ext.
  intros a Ha.
  rewrite Nat2Z.id.
  reflexivity.
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

Lemma in_ziota' i p z :
  @in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota p z)) = (p <=? i) && (i <? p + z).
Proof.
  destruct (Z.le_decidable 0 z).
  2: { rewrite ziota_neg. 2: lia. intros. rewrite in_nil. lia. }
  move: z H p.
  set (P := fun z => ∀ p : Z, @in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota p z)) = (p <=? i) && (i <? p + z)).
  assert (forall z : Z, 0 <= z -> P z).
  1: { apply natlike_ind.
       - unfold P. intros. rewrite in_nil. lia.
       - unfold P. intros.
         rewrite ziotaS_cons. 2: auto.
         destruct (Z.eq_dec x i).
         + subst.
           simpl.
           unfold in_mem.
           simpl.
           unfold in_mem in H0.
           simpl in H0.
           rewrite H0.
           destruct (Z.eq_dec i p).
           * subst. rewrite eq_refl. lia.
           * assert ((@eq_op (Ord.eqType Z_ordType) i p) = false).
             1: { apply/eqP. intros contra. subst. easy. }
             rewrite H1. lia.
         + simpl.
           unfold in_mem.
           simpl.
           unfold in_mem in H0.
           simpl in H0.
           rewrite H0.
           destruct (Z.eq_dec i p).
           * subst. rewrite eq_refl. lia.
           * assert ((@eq_op (Ord.eqType Z_ordType) i p) = false).
             1: { apply/eqP. intros contra. subst. easy. }
             rewrite H1. lia. }
  assumption.
Qed.

Lemma getm_to_arr_None' ws len a (i: Z) :
  ((len <=? i) || (i <? 0)) ->
  to_arr ws len a i = None.
Proof.
  intros. unfold to_arr.
  rewrite mkfmapfE.
  rewrite in_ziota'.
  assert ((0 <=? i) && (i <? 0 + len) = false) by lia.
  rewrite H0.
  reflexivity.
Qed.

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
  rewrite in_ziota'.
  assert ((0 <=? i) && (i <? 0 + len)) by lia.
  rewrite H0.
  reflexivity.
Qed.

Lemma getmd_to_arr a ws len x i :
  (0 <= i < len) ->
  getmd (to_arr ws len a) x i = chArray_get ws a i (wsize_size ws).
Proof.
  intros.
  unfold getmd.
  rewrite getm_to_arr; auto.
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

(** Valid code *)

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

(** Invariants and tactics *)

Definition pdisj (P : precond) (s_id : p_id) (rhs : {fset Location}) :=
  (forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
  (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

Definition u_pdisj (P : precond) (lhs : {fset Location}) :=
  (forall h1 h2 l a, l \in lhs -> (P (h1, h2) -> P (set_heap h1 l a, h2))).

Definition pdisj' (P : precond) (s_id : p_id) (lhs : {fset Location}) (rhs : {fset Location}) :=
  (forall h1 h2 l a, l \in lhs -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
  (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

Ltac solve_in :=
  repeat match goal with
    | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
    | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
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

Ltac split_post :=
  repeat
    match goal with
    | |- (_ ⋊ _) _ => split
    | |- _ /\ _ => split
    | |- set_lhs _ _ _ _ => eexists
    end.

(* NB: this redefines neq_loc_auto, which helps some tactics, since checking for inequality by computation is not feasible for translated variables *)
(* Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ]. *)

#[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq.
Ltac solve_preceq :=
  repeat lazymatch goal with
    | |- ?a ⪯ ?a => reflexivity
    | |- ?a ⪯ ?b~1 => etransitivity; [|apply preceq_I]
    | |- ?a ⪯ ?b~0 => etransitivity; [|apply preceq_O]
    end.

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

Ltac pdisj_apply h :=
  lazymatch goal with
  | |- ?pre (set_heap _ _ _, set_heap _ _ _) => eapply h; [ solve_in | pdisj_apply h ]
  | |- ?pre (set_heap _ _ _, _) =>
      eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
  | |- _ => try assumption
  end.

Ltac pdisj'_apply h :=
  lazymatch goal with
  | |- ?pre (set_heap _ _ _, _) => eapply h; [ tr_auto_in_fset | pdisj'_apply h ]
  | |- ?pre (_, set_heap _ _ _) => eapply h; [ auto_in_fset | pdisj'_apply h ]
  | |- _ => try assumption
  end.

Ltac u_pdisj_apply h :=
  lazymatch goal with
  | |- ?pre (set_heap _ _ _, _) => eapply h; [ solve_in | u_pdisj_apply h ]
  | |- _ => try assumption
  end.

Ltac clear_fset :=
  repeat match goal with
    | |- ValidCode _ _ _ => red
    | |- valid_code (fset (_ :: _)) _ _ => eapply valid_code_cons
    | |- valid_code (fset (_ ++ _)) _ _ => eapply valid_code_cat_l
    end; eapply valid_code_cat_r.

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

Ltac solve_prec :=
  repeat lazymatch goal with
    | |- ?a ≺ ?a~1 => apply prec_I
    | |- ?a ≺ ?a~0 => apply prec_O
    | |- ?a ≺ ?b~1 => etransitivity; [|apply prec_I]
    | |- ?a ≺ ?b~0 => etransitivity; [|apply prec_O]
    end.

(** *)
