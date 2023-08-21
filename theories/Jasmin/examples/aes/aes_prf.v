(** PRF Example

  Inspired by "State Separation for Code-Based Game-Playing Proofs"
  by Brzuska et al.

  Appendix A.

  "Given a pseudorandom function (PRF) we construct a symmetric encryption
  scheme that is indistinguishable under chosen plaintext attacks (IND-CPA)."

*)
From JasminSSProve Require Import jasmin_translate aes_valid aes_spec aes.aes word aes_utils.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq word word.ssrZ.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From Jasmin Require Import word.

Section PRF_example.

  Context (n : wsize).

  Notation key := 'word n.
  Notation pt := 'word n.
  Notation ct := 'word n.

  Notation " 'word " := ('word n) (in custom pack_type at level 2).
  Notation " 'key " := ('word n) (in custom pack_type at level 2).

  Context (f : key -> pt -> ct).

  Notation N := ((expn 2 n).-1.+1).

  #[export] Instance : Positive N.
  Proof. red; by rewrite prednK_modulus expn_gt0. Qed.

  #[export] Instance word_pos (i : wsize.wsize) : Positive i.
  Proof. by case i. Qed.

  #[local] Open Scope package_scope.

  Definition key_location : Location := ('option key ; 0).

  Definition i0 : nat := 3.
  Definition i1 : nat := 4.

  Definition table_location : Location :=
    (chMap 'nat ('word n) ; 7).

  Definition enc (m : pt) (k : key) :
    code fset0 [interface] ('fin N × 'word n) :=
      {code
        r ← sample uniform N ;;
        let pad := f (word_of_ord r) k in
        let c := m ⊕ pad in
        ret (r, c)
      }.

  Definition kgen : code (fset [:: key_location]) [interface] 'word n :=
      {code
       k ← get key_location ;;
       match k with
       | None =>
           k_val ← sample uniform N ;;
           #put key_location := Some (word_of_ord k_val) ;;
           ret (word_of_ord k_val) 
       | Some k_val =>
         ret k_val
       end
      }.

  Definition EVAL_location_tt := (fset [:: key_location]).
  Definition EVAL_location_ff := (fset [:: table_location]).

  Definition EVAL_pkg_tt :
    package EVAL_location_tt [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package
      #def #[i0] (r : 'word) : 'key
      {
        k_val ← kgen ;;
        ret (f r k_val)
      }
    ].

  Definition EVAL_pkg_ff :
    package EVAL_location_ff [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package
      #def #[i0] (r : 'word) : 'key
      {
        T ← get table_location ;;
        match getm T (ord_of_word r) with
        | None =>
            T_key ← sample uniform N ;;
            #put table_location := (setm T (ord_of_word r) (word_of_ord T_key)) ;;
            ret (word_of_ord T_key)
        | Some T_key => ret T_key
        end
      }
    ].

  Definition EVAL : loc_GamePair [interface #val #[i0] : 'word → 'key ] :=
    λ b, if b then {locpackage EVAL_pkg_tt } else {locpackage EVAL_pkg_ff }.

  Definition MOD_CPA_location : {fset Location} := fset0.

  Definition MOD_CPA_tt_pkg :
    package MOD_CPA_location 
      [interface #val #[i0] : 'word → 'key ]
      [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    [package
      #def #[i1] (m : 'word) : ('fin N) × 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform N ;;
        pad ← eval (word_of_ord r) ;;
        let c := m ⊕ pad in
        ret (r, c)
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package MOD_CPA_location 
      [interface #val #[i0] : 'word → 'key]
      [interface #val #[i1] : 'word → ('fin N) × 'word ]:=
    [package
      #def #[i1] (m : 'word) : ('fin N) × 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform N ;;
        m' ← sample uniform N ;;
        pad ← eval (word_of_ord r) ;;
        let c := (word_of_ord m' ⊕ pad) in
        ret (r, c)
      }
    ].

  Definition IND_CPA_location : {fset Location} := fset [:: key_location].

  Program Definition IND_CPA_pkg_tt :
    package IND_CPA_location
      [interface]
      [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    [package
      #def #[i1] (m : 'word) : ('fin N) × 'word
      {
        k_val ← kgen ;;
        enc m k_val
      }
   ].
  (* why is this not inferred? *)
  Next Obligation.
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity. 
    intros. repeat constructor.
    1: auto_in_fset. destruct v.
    1: intros; repeat constructor.
    1: intros; repeat constructor.
    auto_in_fset.
  Defined.

  Program Definition IND_CPA_pkg_ff :
    package IND_CPA_location
      [interface]
      [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    [package
      #def #[i1] (m : 'word) : ('fin N) × 'word
      {
        k_val ← kgen ;;
        m' ← sample uniform N ;;
        enc (word_of_ord m') k_val
      }
    ].
  (* TODO: infer this *)
  Next Obligation.
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity. 
    intros. repeat constructor.
    1: auto_in_fset. destruct v.
    1: intros; repeat constructor.
    1: intros; repeat constructor.
    auto_in_fset.
  Defined.

  Program Definition IND_CPA :
    loc_GamePair [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_tt } else {locpackage IND_CPA_pkg_ff }.

  Local Open Scope ring_scope.

  Definition prf_epsilon A := Advantage EVAL A.

  Definition statistical_gap :=
    AdvantageE (MOD_CPA_ff_pkg ∘ EVAL false) (MOD_CPA_tt_pkg ∘ EVAL false).

  Lemma IND_CPA_equiv_false :
    IND_CPA false ≈₀ MOD_CPA_ff_pkg ∘ (EVAL true).
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq. cbn -[expn]. intros [k|].
    - cbn -[expn]. ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn -[expn].
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  Lemma IND_CPA_equiv_true :
    MOD_CPA_tt_pkg ∘ (EVAL true) ≈₀ IND_CPA true.
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq. cbn -[expn]. intros [k|].
    - cbn -[expn]. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn -[expn].
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  (** Security of PRF

    The bound is given by using the triangle inequality several times,
    using the following chain of computational indistinguishabilities:
    IND_CPA false ≈ MOD_CPA_ff_pkg ∘ EVAL true
                  ≈ MOD_CPA_ff_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL true
                  ≈ IND_CPA true

  *)
  Theorem security_based_on_prf :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → ('fin N) × 'word ] A_export A →
      fdisjoint LA (IND_CPA false).(locs) →
      fdisjoint LA (IND_CPA true).(locs) →
      Advantage IND_CPA A <=
      prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
      statistical_gap A +
      prf_epsilon (A ∘ MOD_CPA_tt_pkg).
  Proof.
    intros LA A vA hd₀ hd₁. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    ssprove triangle (IND_CPA false) [::
      MOD_CPA_ff_pkg ∘ EVAL true ;
      MOD_CPA_ff_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL true
    ] (IND_CPA true) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    erewrite IND_CPA_equiv_false. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    erewrite IND_CPA_equiv_true. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    rewrite GRing.add0r GRing.addr0.
    rewrite !Advantage_link. rewrite Advantage_sym. auto.
  Qed.
End PRF_example.

From JasminSSProve Require Import aes.aes aes_jazz jasmin_utils aes_valid.
From Jasmin Require Import expr sem.

Import JasminNotation JasminCodeNotation.

(* From Jasmin Require Import expr. *)
Require Import String.
Local Open Scope string.

Section JasminPRF.

  Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

  Notation n := U128.
  
  Definition key := 'word n.
  Definition pt := 'word n.
  Definition ct := 'word n.

  Notation " 'word " := ('word n) (in custom pack_type at level 2).
  Notation " 'key " := ('word n) (in custom pack_type at level 2).
  Notation N := ((expn 2 n).-1.+1).

  Notation enc := (enc U128 aes).
  Notation kgen := (kgen U128).
  Notation key_location := (key_location U128).

  Definition Cenc (m : pt) (k : key) :
    code (fset [:: state ; rkeys]) [interface] (('fin N) × 'word n).
  Proof.
    refine
      {code
        r ← sample uniform N ;;
        pad ← Caes (word_of_ord r) k ;; 
        ret (r, (m ⊕ pad))
      }.
    repeat constructor.
    all: auto_in_fset.
  Defined.

  Opaque wrange.
  Opaque expn.

  Definition IND_CPA_pkg_Cenc :
    package (fset (key_location :: Cenc_locs))
      [interface]
      [interface #val #[i1] : 'word → ('fin N) × 'word].
  Proof.
    refine
      [package
        #def #[i1] (m : 'word) : ('fin N) × 'word
        {
          k_val ← kgen ;;
          Cenc m k_val
        }
      ].
    (* infer this *)
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity.
    intros. repeat constructor.
    all: auto_in_fset.
    intros. destruct v.
    1: repeat constructor; auto_in_fset.
    1: repeat constructor; auto_in_fset.
  Defined.

  Notation hdtc128 l := (coerce_to_choice_type ('word U128) (head ( 'word U128 ; word0 ) l).π2).
  
  Definition IND_CPA_pkg_JENC (id0 : p_id) :
    package (fset (key_location :: (JENC_valid id0).π1))
      [interface]
      [interface #val #[i1] : 'word → ('fin N) × 'word ].
  Proof.
    refine
      [package
        #def #[i1] (m : 'word) : ('fin N) × 'word
          {
            k_val ← kgen ;;
            r ← sample uniform N ;;
            res ← JENC id0 (word_of_ord r) k_val m ;;
            ret (r, hdtc128 res)
          }
        ].
    repeat constructor.
    intros [].
    rewrite in_fset in_cons => /orP []; [|easy]; move=> /eqP H; noconf H.
    cbv zeta match.
    eexists.
    split. 
    1: reflexivity.
    intros x.
    constructor.
    1: auto_in_fset.
    intros. destruct v.
    - constructor. intros.
      eapply valid_bind.
      + red. eapply valid_code_cons.
        1: eapply (JENC_valid id0).π2.
      + constructor.
    - constructor.
       intros.
       constructor.
       1: auto_in_fset.
       constructor. intros.
       eapply valid_bind.
       + red. eapply valid_code_cons.
         1: eapply (JENC_valid id0).π2.
       + constructor.
    Unshelve. all: exact _.
  Defined.

  (* Notation KG_pkg := (KG_pkg U128). *)
  Notation IND_CPA_pkg_ff := (IND_CPA_pkg_ff U128 aes).
  Notation MOD_CPA_ff_pkg := (MOD_CPA_ff_pkg U128).
  Notation IND_CPA := (IND_CPA U128 aes).
  Notation EVAL := (EVAL U128 aes).

  Lemma fsubset_ext2 : ∀ [T : ordType] (s1 s2 : {fset T}), fsubset s1 s2 -> (forall x, x \in s1 -> x \in s2). 
  Proof.
    intros.
    rewrite -fsub1set.
    eapply fsubset_trans. 2: eassumption.
    rewrite fsub1set. assumption.
  Qed.

  Lemma fsubset_cons : ∀ [T : ordType] a (s1 s2 : {fset T}), fsubset s1 s2 -> fsubset s1 (a |: s2). 
  Proof.
    intros.
    apply fsubset_ext.
    intros. rewrite in_fset in_cons.
    apply/orP. right.
    eapply fsubset_ext2.
    1: eassumption.
    assumption.
  Qed.
  
  Definition IND_CPA_Cenc :
    loc_GamePair [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_Cenc } else (IND_CPA true).

  Definition IND_CPA_JENC id0 :
    loc_GamePair [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_JENC id0} else {locpackage IND_CPA_pkg_Cenc}.

  (* TODO: move *)
  Lemma JXOR_E pre id0 x y :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
      JXOR id0 x y
      ≈
      ret (chCanonical chUnit) 
      ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ (exists o, (v0 = cons ('word U128 ; o ) nil ) /\ (o = x ⊕ y)) ⦄.
  Proof.
    unfold JXOR, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body.
    intros disj.
    simpl. simpl_fun.
    repeat setjvars.
    ssprove_code_simpl.
    repeat clear_get.
    repeat eapply r_put_lhs.
    eapply r_ret.
    rewrite !zero_extend_u.
    intros.  destruct_pre; split_post.
    1: pdisj_apply disj.
    eexists; split; [reflexivity|]. reflexivity.
  Qed.

  (* TODO: move *)
  Arguments pheap_ignore : simpl never.

  Lemma translate_var_option {A} s_id v i : ( 'option A ; i ) != translate_var s_id v.
  Proof.
    unfold translate_var.
    apply/eqP => contra.
    apply EqdepFacts.eq_sigT_fst in contra.
    destruct v.
    destruct vtype0; simpl in contra; noconf contra.
  Qed.

  (* NOTE: the next 5 lemmas are not used, but might useful. Move *)
  Lemma nat_of_stype_bound s : 5 <= nat_of_stype s.
  Proof.
    destruct s. 1-2: simpl; try micromega.Lia.lia.
    - simpl. pose proof Pos2Nat.is_succ p as []. rewrite H.
      pose proof Nat.pow_le_mono_r 11 1 (x.+1) ltac:(micromega.Lia.lia) ltac:(micromega.Lia.lia). simpl in *.  micromega.Lia.lia.
    - cbn [nat_of_stype].
      assert (0 < nat_of_wsize w). 1: destruct w; unfold nat_of_wsize; simpl; try micromega.Lia.lia.
      pose proof Nat.pow_le_mono_r 13 1 w ltac:(micromega.Lia.lia) ltac:(micromega.Lia.lia). simpl in *.  micromega.Lia.lia.
  Qed.

  Lemma nat_of_p_id_ident_bound s_id v : 2 <= nat_of_p_id_ident s_id v.
  Proof.
    unfold nat_of_p_id_ident.
    pose proof nat_of_p_id_pos s_id.
    pose proof nat_of_ident_pos v.
    pose proof Nat.pow_le_mono_r 3 1 (nat_of_p_id s_id) ltac:(micromega.Lia.lia) ltac:(micromega.Lia.lia).
    pose proof Nat.pow_le_mono_r 2 1 (nat_of_ident v) ltac:(micromega.Lia.lia) ltac:(micromega.Lia.lia).
    simpl in *; micromega.Lia.lia.
  Qed.

  Lemma nat_of_p_id_var_bound s_id v : 10 <= nat_of_p_id_var s_id v.
  Proof.
    unfold nat_of_p_id_var.
    pose proof nat_of_stype_bound (vtype v).
    pose proof nat_of_p_id_ident_bound s_id (vname v).
    micromega.Lia.nia.
  Qed.

  Lemma translate_var_bound {A} s_id v i : i < 10 -> ( A ; i ) != translate_var s_id v.
  Proof.
    intros.
    apply/eqP => contra.
    inversion contra.
    pose proof nat_of_p_id_var_bound s_id v.
    micromega.Lia.lia.
  Qed.

  Lemma IND_CPA_JENC_equiv_false id0 :
    padv_equiv (fun l => exists s_id v, id0 ⪯ s_id /\ l = translate_var s_id v) (fun l => l \in fset Cenc_locs) (IND_CPA_JENC id0 true) (IND_CPA_JENC id0 false) (λ _ : raw_package, 0%R).
  Proof.
    eapply eq_rel_perf_ind'.
    (* invariant *)
    { eapply pInvariant_pheap_ignore with
        (P := fun l => (forall s_id v, id0 ⪯ s_id -> l != translate_var s_id v) /\ l \notin fset Cenc_locs).
      { intros.
        split.
        - intros. apply/eqP. intros contra.
          destruct H. apply H.
          exists s_id, v. split; auto.
        - apply/negP; easy. } }
    unfold eq_up_to_inv, get_op_default, lookup_op, IND_CPA_JENC, IND_CPA_pkg_JENC.
    Opaque Caes.
    Opaque translate_call.
    Opaque wrange.
    Opaque expn.
    simpl.
    simplify_eq_rel m.
    simplify_linking.
    rewrite !cast_fun_K.
    ssprove_sync.
    { intros h0 h1 hpre. apply hpre. split.
      - intros. apply translate_var_option.
      - unfold Cenc_locs. rewrite in_fset in_cons; auto. }
    intros.
    eapply r_bind with (mid := fun '(a₀, s₀) '(a₁, s₁) => pheap_ignore (λ l : ∑ _ : choice_type, nat, (∀ (s_id : p_id) (v : var), id0 ⪯ s_id → l != translate_var s_id v) /\ l \notin fset Cenc_locs) (s₀, s₁) /\ a₀ = a₁).
    { destruct a.
      - eapply r_ret. easy.
      - ssprove_sync. intros.
        ssprove_sync.
        { intros h0 h1 Hh l H.
          destruct (l == key_location) eqn:E.
          - move: E => /eqP heq. subst. rewrite !get_set_heap_eq. reflexivity.
          - move: E => /negP Hneq. rewrite !get_set_heap_neq; auto. 1-2: apply /negP; auto. }
        eapply r_ret. easy. }
    intros.
    (* TODO: find easier way to do next three lines *)
    eapply rpre_weak_hypothesis_rule.
    intros; destruct_pre.
    eapply rpre_weaken_rule with (pre:= fun '(s₀, s₁) => pheap_ignore (λ l : ∑ _ : choice_type, nat, (∀ (s_id : p_id) (v : var), id0 ⪯ s_id → l != translate_var s_id v) /\ l \notin fset Cenc_locs) (s₀, s₁)); try easy.
    ssprove_code_simpl.
    simpl.
    ssprove_sync. intros.
    rewrite !zero_extend_u.
    repeat clear_get.
    do 3 eapply r_put_lhs.
    eapply r_bind.
    - eapply aes_E; split.
      + intros.
        destruct_pre.
        do 2 eexists.
        1: do 2 eexists.
        1: do 2 eexists.
        1: instantiate (1 := set_heap H7 (translate_var s_id' v) a1).
        all: try reflexivity.
        { intros l lnin. rewrite get_set_heap_neq. 1: eapply H8; auto.
          apply lnin.
          etransitivity.
          2: eassumption.
          solve_preceq. }
        { repeat rewrite [set_heap _ _ a1]set_heap_commut; auto.
          1-3: apply injective_translate_var2; apply prec_neq; eapply prec_preceq_trans; try eassumption; apply prec_I. }
      + intros.
        destruct_pre.
        do 2 eexists.
        1: do 2 eexists.
        1: do 2 eexists.
        1: instantiate (1 := H6).
        all: try reflexivity.
        intros l2 lnin.
        rewrite get_set_heap_neq.
        1: eapply H7. 1: assumption.
        unfold Cenc_locs in lnin.
        destruct lnin. apply /eqP => contra; subst.
        rewrite H in H2. easy.
    - simpl. intros.
      eapply rpre_weak_hypothesis_rule; intros.
      destruct_pre. 
      simpl.
      clear_get.
      eapply r_put_lhs with (pre := fun _ => _).
      eapply r_get_remember_lhs. intros.
      eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _).
      1: eapply JXOR_E; split.
      + intros.
        destruct_pre.
        1: do 1 eexists.
        1: do 2 eexists.
        1: do 7 eexists.
        1: instantiate (1:= (set_heap H14 (translate_var s_id' v) a1)).
        all: try reflexivity.
        { intros l hl. rewrite get_set_heap_neq. 1: eapply H15. 1: assumption. apply hl.
          etransitivity. 2: eauto.
          solve_preceq. }
        { repeat rewrite [set_heap _ _ a1]set_heap_commut; auto.
          1-4: apply injective_translate_var2; apply prec_neq; eapply prec_preceq_trans; try eassumption; solve_prec. }
        { sheap. simpl. rewrite get_set_heap_neq. 1: sheap. 1: reflexivity.
          apply injective_translate_var2; apply prec_neq; eapply prec_preceq_trans; try eassumption; solve_prec. }
      + intros. easy.
      + intros.
        eapply rpre_weak_hypothesis_rule; intros.
        destruct_pre; simpl.
        clear_get.
        eapply r_put_lhs with (pre := fun _ => _).
        eapply r_ret.
        rewrite !coerce_to_choice_type_K.
        rewrite !zero_extend_u.
        intros.
        destruct_pre; simpl; split_post.
        { sheap. by rewrite wxorC. }
        { intros l s_id.
          rewrite !get_set_heap_neq.
          1: eapply H19; auto.
          1-5: apply s_id; reflexivity. }
  Qed.

  Lemma IND_CPA_jazz_equiv_false :
    (IND_CPA_Cenc) true ≈₀ (IND_CPA_Cenc) false.
  Proof.
    eapply eq_rel_perf_ind_ignore  with (L := fset Cenc_locs).
    { eapply fsubsetU. apply/orP; left. simpl.
      rewrite [fset (key_location :: _)]fset_cons.
      eapply fsubset_cons.
      eapply fsubsetxx. }
    unfold eq_up_to_inv.
    Opaque Caes.
    Opaque wrange.
    Opaque expn.
    simplify_eq_rel m.
    ssprove_sync. intros.
    eapply r_bind with (mid := fun '(a0, s0) '(a1, s1) => a0 = a1 /\ heap_ignore (fset Cenc_locs) (s0, s1)). 
    { destruct a.
      - eapply r_ret. easy.
      - ssprove_sync. intros.
        ssprove_sync.
        (* { intros h0 h1 H1 H2 H. rewrite !get_set_heap_neq. 1: eapply H1; eauto. 1-2: admit. } *)
        eapply r_ret. easy. }
    intros. simpl.
    (* TODO: find easier way to do next three lines *)
    eapply rpre_weak_hypothesis_rule.
    intros; destruct_pre.
    eapply rpre_weaken_rule with (pre:= fun '(s₀, s₁) => heap_ignore (fset Cenc_locs) (s₀, s₁)); try easy.
    ssprove_sync. intros.
    eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _).
    - 1: eapply aes_h.
      intros h1 h2 l a2 lin h.
      intros l2 lnin.
      unfold Cenc_locs in *.
      rewrite get_set_heap_neq.
      1: apply h; auto.
      apply/eqP=>contra; subst.
      move: lnin => /negP. easy.
    - intros. eapply r_ret.
      intros. destruct_pre; split_post; auto.
  Qed.

  Definition JIND_CPA id0 :
    loc_GamePair [interface #val #[i1] : 'word → ('fin N) × 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_JENC id0 } else (IND_CPA true).
  
  Theorem jasmin_security_based_on_prf id0 :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → ('fin N) × 'word ] A_export A →
      pdisjoint LA (λ l : Location, ∃ (s_id : p_id) (v : var), id0 ⪯ s_id ∧ l = translate_var s_id v) ->
      pdisjoint LA (λ l : Location, l \in fset Cenc_locs) ->
      fdisjoint LA (IND_CPA_Cenc false).(locs) →
      fdisjoint LA (IND_CPA_Cenc true).(locs) →
      Advantage (JIND_CPA id0) A = 0%R.
  Proof.
    intros LA A vA hd₀ hd₁ hd2 hd3. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    eapply AdvantageE_le_0.
    ssprove triangle (JIND_CPA id0 false) [::
                                             IND_CPA_pkg_Cenc : raw_package
      ] (JIND_CPA id0 true) A
      as ineq.
    eapply Order.POrderTheory.le_trans.
    1: exact ineq.
    clear ineq.
    rewrite Advantage_sym.
    erewrite IND_CPA_jazz_equiv_false. all: eauto.
    rewrite Advantage_sym.
    pose proof IND_CPA_JENC_equiv_false id0.
    unfold padv_equiv in H.
    specialize (H LA A vA hd₀ hd₁).
    rewrite H.
    rewrite GRing.addr0.
    apply Order.POrderTheory.le_refl.
  Qed.

  Print Assumptions jasmin_security_based_on_prf.

End JasminPRF.
