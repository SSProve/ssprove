Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.
From mathcomp.word Require Import word.
(* From Jasmin Require Import x86_extra. *)
From JasminSSProve Require Import jasmin_translate jasmin_utils.
From Crypt Require Import Prelude Package pkg_user_util.

Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

Local Open Scope string.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Context (f : funname).

Definition xor : uprog.
Proof.
  refine {| p_funcs :=
 [ ( (* xor *) xH,
     {| f_info := xO xH
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "x.143"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "y.144"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := (sword U64)
                                ; vname := "r.145"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "x.143"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := (sword U64)
                                ; vname := "r.145"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp2 (Olxor U64)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "r.145"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "y.144"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.145"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.
Defined.

Definition tr_P := Eval simpl in translate_prog' xor.
Definition default_prog' := (1%positive, fun s_id : p_id => (ret tt)).
Definition default_call := (1%positive, fun (s_id : p_id) (x : [choiceType of seq typed_chElement]) => ret x).
Definition get_tr sp n := List.nth_default default_call sp n.
Definition tr_xor := Eval simpl in (get_tr tr_P.2 0).
Eval simpl in (tr_P.1).

Opaque translate_for.

Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.

Lemma f_xor_correct : forall w1 w2, ⊢ ⦃ fun _ => True ⦄ tr_xor.2 1%positive [('word U64; w1); ('word U64; w2)] ⇓ [('word U64; wxor w1 w2)] ⦃ fun _ => True ⦄.
Proof.
  (* preprocessing *)
  intros w1 w2.
  simpl_fun.
  repeat setjvars.

  (* this makes Qed hang *)
  (* repeat setoid_rewrite (@zero_extend_u U64). *)

  (* proof *)
  unfold eval_jdg.
  repeat clear_get.

  ssprove_swap_lhs 1.
  ssprove_swap_lhs 0.
  ssprove_swap_lhs 1.
  rewrite !zero_extend_u.

  (* ssprove_swap_lhs 1. *)
  (* ssprove_contract_put_get_lhs. *)
  (* ssprove_swap_seq_lhs [:: 1 ; 0 ; 2 ; 1]. *)
  (* ssprove_contract_put_get_lhs. *)
  (* ssprove_swap_seq_lhs [:: 1 ; 0 ; 2 ; 1]. *)
  (* ssprove_contract_put_get_lhs. *)
  (* ssprove_swap_seq_lhs [:: 0 ; 2 ; 1 ]. *)
  (* ssprove_contract_put_lhs. *)
  (* ssprove_swap_seq_lhs [:: 2 ; 1 ]. *)
  (* ssprove_contract_put_get_lhs. *)
  repeat eapply u_put.
  eapply u_ret.
  (* rewrite !zero_extend_u. *)
  easy.
Qed.

(*
  OTP example
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.

#[local] Open Scope ring_scope.
From mathcomp.word Require Import ssrZ.

Import GRing Order TotalTheory.
(* We could just use these, but to get the proper size, we copy paste the proofs from ordinals *)
(* Definition word_finMixin n := Eval hnf in CanFinMixin (@ord_of_wordK n). *)
(* Canonical word_finType n := Eval hnf in FinType (n.-word) (word_finMixin n). *)
Section word_fin.

  Variable n : nat.
  Notation word := (word n).

  Definition word_enum : seq word := pmap insub (ziota 0 (modulus n)).

  Lemma val_word_enum : map val word_enum = ziota 0 (modulus n).
  Proof.
    rewrite pmap_filter; last exact: insubK.
    by apply/all_filterP/allP=> i; rewrite in_ziota isSome_insub.
  Qed.

  From mathcomp Require Import zify.

  Lemma ltzS x y : (x < Z.succ y) = (x <= y).
  Proof. zify; lia. Qed.

  Lemma ltSz x y : (Z.succ x <= y) = (x < y).
  Proof. zify; lia. Qed.

  Lemma addzS x y : (x + Z.succ y) = Z.succ (x + y).
  Proof. zify; lia. Qed.

  Lemma addSz x y : (Z.succ x + y) = Z.succ (x + y).
  Proof. zify; lia. Qed.

  Lemma mem_ziota m k i : (i \in ziota m k) = (m <= i < m + k).
  Proof.
    destruct (Z.leb 0 k) eqn:E.
    - move: m. eapply natlike_ind with (x:=k).
      + intros m. by rewrite addr0 ltNge andbN.
      + intros x Hx Hi m.
        rewrite ziotaS_cons; [|assumption].
        apply Z.leb_le in Hx.
        by rewrite in_cons Hi addzS addSz ltzS ltSz; case: ltgtP => //= ->; rewrite ler_addl.
      + by apply Z.leb_le.
    - rewrite ziota_neg.
      + rewrite in_nil.
        apply/idP. unfold le, lt=>//=.
        destruct ((Z.leb m i) && (Z.ltb i (m + k)%R)%Z) eqn:E2=>//=.
        unfold add in E2. simpl in E2. lia.
      + lia.
  Qed.

  Lemma ziota_uniq i j : uniq (ziota i j).
  Proof.
    unfold ziota.
    rewrite map_inj_uniq.
    - apply iota_uniq.
    -  intros x y. lia.
  Qed.

  Lemma word_enum_uniq : uniq word_enum.
  Proof. by rewrite pmap_sub_uniq ?ziota_uniq. Qed.

  Lemma word_inj : injective (@toword n).
  Proof. exact val_inj. Qed.

  Lemma mem_word_enum i : i \in word_enum.
  Proof. by rewrite -(mem_map word_inj) val_word_enum mem_ziota add0r; case: i. Qed.

  Definition word_finMixin :=
    Eval hnf in UniqFinMixin word_enum_uniq mem_word_enum.
  Canonical word_finType := Eval hnf in FinType word word_finMixin.
  Canonical word_subFinType := Eval hnf in [subFinType of word].
  Canonical finEnum_unlock := Unlockable Finite.EnumDef.enumDef.

  (* can't get `enum` in `val_enum_word` to work without this import *)
  From mathcomp Require Import fintype.

  Lemma val_enum_word : map val (enum [finType of word]) = ziota 0 (modulus n).
  Proof. by rewrite enumT unlock val_word_enum. Qed.

  Lemma size_enum_word : size (enum [finType of word]) = Z.to_nat (modulus n).
  Proof. by rewrite -(size_map val) val_enum_word size_ziota. Qed.

End word_fin.

Section word_uniform.

  Definition fin_family_word (i : wsize.wsize) : finType := [finType of chWord i].
  Lemma F_w0_word :
    forall i, fin_family_word i.
  Proof.
    intros i. unfold fin_family_word. cbn.
    exists (word1 i). apply isword1.
  Qed.

  Definition Uni_W_word : forall i, SDistr (fin_family_word i).
    move=> i. apply (@uniform_F (fin_family_word i)).
    apply F_w0_word.
  Defined.

  Definition uniform_word (i : wsize.wsize) : Op :=
    existT _ ('word i) (Uni_W_word i).

  #[export] Instance LosslessOp_uniform_word i : LosslessOp (uniform_word i).
  Proof.
    unfold LosslessOp.
    simpl.
    unfold r. rewrite psumZ. 2: apply ler0n.
    simpl. rewrite GRing.mul1r.
    rewrite psum_fin. rewrite cardE.
    rewrite size_enum_word. simpl.
    rewrite GRing.sumr_const. rewrite cardE. rewrite size_enum_word.
    rewrite -normrMn.
    rewrite -GRing.Theory.mulr_natr.
    rewrite GRing.mulVf.
    2:{
      apply /negP => e.
      rewrite intr_eq0 in e.
      move: e => /eqP e.
      assert (forall p, Pos.to_nat p <> 0%nat).
      { intros p. pose proof (Pos2Nat.is_pos p). lia. }
      eapply H. injection e. intros ?.
      eassumption.
    }
    rewrite normr1. reflexivity.
  Qed.

End word_uniform.

Notation "m ⊕ k" := (@wxor _ m k) (at level 70).

Section wxor.

  Context (n : wsize.wsize).
  Notation word := (word n).

  Lemma wxor_involutive : ∀ m k : word, (m ⊕ k) ⊕ k = m.
  Proof.
    intros m k.
    apply/eqP/eq_from_wbit=> i.
    by rewrite !wxorE -addbA addbb addbF.
  Qed.

  Lemma wxorC : ∀ m k : word, (m ⊕ k) = (k ⊕ m).
  Proof.
    intros m k.
    apply/eqP/eq_from_wbit=> i.
    by rewrite !wxorE addbC.
  Qed.

  Lemma wxorA : ∀ m k l : word, ((m ⊕ k) ⊕ l) = (m ⊕ (k ⊕ l)).
  Proof.
    intros m k l.
    apply/eqP/eq_from_wbit=> i.
    by rewrite !wxorE addbA.
  Qed.

End wxor.

Section OTP_example.

  Context (n : wsize.wsize).
  Notation word := (word n).

  #[local] Open Scope package_scope.

  Definition i1 : nat := 0.

  Definition Enc {L : {fset Location}} (m : word) (k : word) :
    code L [interface] ('word n) :=
    {code
       ret (m ⊕ k)
    }.

  Notation N := ((expn 2 n).-1.+1).

  #[export] Instance : Positive N.
  Proof. red; by rewrite prednK_modulus expn_gt0. Qed.

  #[export] Instance word_pos (i : wsize.wsize) : Positive i.
  Proof. by case i. Qed.

  Definition KeyGen {L : {fset Location}} :
    code L [interface] ('word n) :=
    {code
       k ← sample uniform N ;;
       ret (word_of_ord k)
    }.

  Definition dec {L : {fset Location }}(c : word) (k : word) :
    code L [interface] 'word n := Enc k c.

  Definition IND_CPA_location : {fset Location} := fset0.

  (* REM: Key is always sampled at the side of the encrypter. *)
  (* This assumption is stronger than usual crypto definitions. *)
  (* We need control over the key to apply coupling. *)
  Notation " 'word " := (chWord n) (in custom pack_type at level 2).

  Definition IND_CPA_real :
    package IND_CPA_location
      [interface]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
        #def #[i1] (m : 'word) : 'word
        {
          k_val ← sample uniform N ;;
          r ← Enc m (word_of_ord k_val) ;;
          ret r
        }
    ].

  Definition IND_CPA_ideal :
    package IND_CPA_location
      [interface ]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
      #def #[i1] (m : 'word) : 'word
      {
        m'    ← sample uniform N ;;
        k_val ← sample uniform N ;;
        r     ← Enc (word_of_ord m') (word_of_ord k_val) ;;
        ret r
      }
    ].

  Definition IND_CPA : loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b, if b then {locpackage IND_CPA_real } else {locpackage IND_CPA_ideal }.

  #[local] Open Scope ring_scope.

  From Crypt Require Import pkg_distr.
  Notation IN := 'I_N.
  Coercion word_of_ord : IN >-> word.

  Lemma IND_CPA_ideal_real :
    IND_CPA false ≈₀ IND_CPA true.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    (* TODO Why doesn't it infer this? *)
    eapply r_const_sample_L with (op := uniform _).
    1: exact _. intro m_val.
    pose (f :=
      λ (k : Arit (uniform N)),
        ord_of_word ((word_of_ord k) ⊕ m ⊕ (word_of_ord m_val))
    ).
    assert (bij_f : bijective f).
    { subst f.
      exists (λ x, ord_of_word ((word_of_ord x) ⊕ (word_of_ord m_val) ⊕ m)).
      - intro x. by rewrite ord_of_wordK !wxor_involutive word_of_ordK.
      - intro x. by rewrite ord_of_wordK !wxor_involutive word_of_ordK.
    }
    eapply r_uniform_bij with (1 := bij_f). intro k_val.
    apply r_ret. intros s₀ s₁ e. intuition auto.
    subst f. simpl.
    rewrite ord_of_wordK.
    rewrite !wxorA 2![_ m _]wxorC wxorA  wxor_involutive.
    by rewrite wxorC.
  Qed.

  Theorem unconditional_secrecy :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word ] A_export A →
      Advantage IND_CPA A = 0.
  Proof.
    intros LA A vA.
    rewrite Advantage_E. eapply IND_CPA_ideal_real. 1: eauto.
    all: eapply fdisjoints0.
  Qed.

End OTP_example.

Section Jasmin_OTP.

  (* Context (n : wsize.wsize). *)
  Definition n := U64.
  Notation word := (word n).
  Notation " 'word " := (chWord n) : package_scope.
  Notation " 'word " := (chWord n) (in custom pack_type at level 2) : package_scope.
  Notation N := ((expn 2 n).-1.+1).

  Definition id0 : BinNums.positive := 1.

  Definition xor_locs :=
    [fset
       (translate_var id0 {| vtype := sword n ; vname := "x.143" |}) ;
       (translate_var id0 {| vtype := sword n ; vname := "y.144" |}) ;
       (translate_var id0 {| vtype := sword n ; vname := "r.145" |})
    ].

  Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.

  #[local] Open Scope package_scope.

  Program Definition JasminEnc (m : 'word n) (k : 'word n) : (* why can't I just use 'word here? *)
    code xor_locs [interface] ('word n) :=
    {code
       e ← tr_xor.2 id0 [:: totce m; totce k] ;;
       ret (coerce_to_choice_type _ (hd (totce (chCanonical ('word n))) e).π2)
    }.
  Next Obligation.
    unfold xor_locs. unfold n.
    repeat constructor; repeat rewrite in_fset in_cons;
      repeat match goal with
      | [ |- is_true (orb (translate_var ?i1 ?v1 == translate_var ?i1 ?v1) _) ] =>
          apply/orP; left; by rewrite translate_var_eq
      | |- is_true (orb _ _) => apply/orP; right
        end.
  Defined.

  Program Definition JasminDec {L : {fset Location }}(c : 'word n) (k : 'word n) :
    code xor_locs [interface] 'word n := JasminEnc k c.

  Program Definition IND_CPA_jasmin :
    package xor_locs
      [interface]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
        #def #[i1] (m : 'word) : 'word
        {
          k_val ← sample uniform N ;;
          r ← JasminEnc m (word_of_ord k_val) ;;
          ret r
        }
    ].

  Definition IND_CPA_jasmin_real_game : loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b, if b then {locpackage IND_CPA_jasmin } else {locpackage (IND_CPA_real n) }.
  Definition IND_CPA_jasmin_ideal_game : loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b, if b then {locpackage IND_CPA_jasmin } else {locpackage (IND_CPA_ideal n) }.

  #[local] Open Scope ring_scope.

  From Crypt Require Import pkg_distr.

  Lemma IND_CPA_jasmin_real :
    IND_CPA_jasmin_real_game false ≈₀ IND_CPA_jasmin_real_game true.
  Proof.
    eapply eq_rel_perf_ind_ignore with (L := xor_locs); [apply fsubsetUr|].

    Opaque n.
    simplify_eq_rel m.
    Transparent n.

    ssprove_sync.
    intros x.

    (* note that this simpl chokes if called before ssprove_sync_eq *)
    apply rsymmetry; repeat clear_get; apply rsymmetry.
    rewrite !zero_extend_u.

    (* why is this not inferred? *)
    repeat eapply r_put_rhs.
    eapply r_ret.

    intros ? ? ?.
    rewrite coerce_to_choice_type_K.
    split; [reflexivity|].
    intros l lnin.
    repeat destruct H. subst.
    rewrite !get_set_heap_neq.
    1: eapply H; assumption.
  Admitted.

  Theorem advantage_jas_real :
    ∀ LA A,
      fdisjoint LA xor_locs ->
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word ] A_export A →
      Advantage IND_CPA_jasmin_real_game A = 0.
  Proof.
    intros LA A vA HA.
    rewrite Advantage_E.
    eapply IND_CPA_jasmin_real. 1: eauto.
    1: eapply fdisjoints0.
    1: assumption.
  Qed.

  Theorem unconditional_secrecy_jas :
    ∀ LA A,
      fdisjoint LA xor_locs ->
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word ] A_export A →
      Advantage IND_CPA_jasmin_ideal_game A = 0.
  Proof.
    intros LA A vA HA.
    rewrite Advantage_E.
    assert (AdvantageE (IND_CPA_jasmin_ideal_game false) (IND_CPA_jasmin_ideal_game true) A <= 0 + 0).
    - rewrite -{2}advantage_jas_real; [|assumption].
      rewrite -unconditional_secrecy.
      rewrite !Advantage_E.
      (* cbn [IND_CPA_jasmin_real_game IND_CPA IND_CPA_jasmin_ideal_game]. *)
      eapply Advantage_triangle.
    - rewrite add0r in H.
      apply AdvantageE_le_0.
      assumption.
  Qed.
End Jasmin_OTP.

From Hacspec Require Import Xor_Both.
From Hacspec Require Import Hacspec_Lib_Pre.
(* consider exporting this from Hacspec_Lib_Pre? Needed for int64 : Type coercion  *)
From Hacspec Require Import ChoiceEquality.

Section JasminHacspec.

  Definition state_xor (x y : int64) : raw_code int64 :=
    xor (x, y).

  Definition pure_xor (x y : int64) : raw_code int64 :=
    lift_to_code (L:=fset0) (I := [interface]) (is_pure (xor (x, y))).

  Definition state_pure_xor x y := code_eq_proof_statement (xor (x, y)).
  Notation jazz_xor w1 w2 := ((snd tr_xor) 1%positive [('word U64; w1); ('word U64; w2)]).
  Notation hdtc res := (coerce_to_choice_type ('word U64) (hd ('word U64 ; chCanonical _) res).π2).

  Lemma rxor_pure : forall w1 w2,
      ⊢ ⦃ true_precond ⦄
        res ← jazz_xor w1 w2 ;;
      ret (hdtc res)
        ≈
        pure_xor w1 w2
        ⦃ fun '(a, h₀) '(b, h₁) => (a = b) ⦄.
  Proof.
    intros w1 w2.
    simpl_fun.

    repeat setjvars.

    Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.

    repeat clear_get.

    rewrite !zero_extend_u.
    eapply r_put_lhs with (pre := fun _ => Logic.True).
    repeat eapply r_put_lhs.
    eapply r_ret.

    intros ? ? ?.
    rewrite coerce_to_choice_type_K.
    reflexivity.
  Qed.

  Lemma rxor_state : forall w1 w2,
      ⊢ ⦃ true_precond ⦄
        res ← ((snd tr_xor) 1%positive [('word U64; w1); ('word U64; w2)]) ;;
      ret (coerce_to_choice_type ('word U64) (hd ('word U64 ; chCanonical _) res).π2)
        ≈
        state_xor w1 w2
        ⦃ fun '(a, _) '(b, _) => (a = b) ⦄.
  Proof.
    intros w1 w2.
    unfold state_xor.

    simpl_fun.
    repeat setjvars.
    repeat clear_get.

    rewrite !zero_extend_u.
    rewrite coerce_to_choice_type_K.
    eapply r_put_vs_put with (pre := fun _ => Logic.True).
    repeat eapply r_put_vs_put.
    repeat eapply r_put_rhs.
    eapply r_ret.
    easy.
  Qed.

  Lemma val_sym :
    ∀ {A : ord_choiceType} {pre : precond}
    {c₀ : raw_code A} {c₁ : raw_code A},
      ⊢ ⦃ true_precond ⦄
        c₀
        ≈
        c₁
        ⦃ fun '(a, _) '(b, _) => a = b ⦄ ->
    ⊢ ⦃ fun '(h0, h1) => true_precond (h0, h1) ⦄
        c₁
        ≈
        c₀
        ⦃ fun '(a, _) '(b, _) => a = b ⦄.
  Proof.
    intros.
    eapply rsymmetry.
    eapply rpost_weaken_rule.
    1: exact H.
    intros [] []; auto.
  Qed.

  Lemma rxor_pure_via_state : forall w1 w2,
      ⊢ ⦃ true_precond ⦄
        res ← ((snd tr_xor) 1%positive [('word U64; w1); ('word U64; w2)]) ;;
      ret (coerce_to_choice_type ('word U64) (hd ('word U64 ; chCanonical _) res).π2)
        ≈
        pure_xor w1 w2
        ⦃ fun '(a, _) '(b, _) => (a = b) ⦄.
  Proof.
    intros w1 w2.
    eapply @r_transL_val with (c₀ := state_xor w1 w2) (P := Logic.True).
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - eapply rsymmetry.
      eapply rpost_weaken_rule.
      1: eapply rxor_state.
      intros [] []; auto.
    - pose proof state_pure_xor.
      eapply rpre_weaken_rule.
      1: eapply rpost_weaken_rule.
      1: eapply state_pure_xor.
      2: auto.
      intros [] []. unfold pre_to_post_ret; intuition subst.
  Qed.
End JasminHacspec.
