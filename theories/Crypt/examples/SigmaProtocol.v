
From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl
  Package Prelude RandomOracle Casts.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

#[local] Open Scope ring_scope.

Module Type SigmaProtocolParams.

  Parameter Witness Statement Message Challenge Response : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.
  Parameter R : Statement → Witness → bool.

  Parameter Statement_pos : Positive #|Statement|.
  Parameter Witness_pos : Positive #|Witness|.
  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.
  Parameter Response_pos : Positive #|Response|.
  Parameter Bool_pos : Positive #|'bool|.

End SigmaProtocolParams.

Module Type SigmaProtocolAlgorithms (π : SigmaProtocolParams).

  Import π.

  #[local] Open Scope package_scope.

  #[local] Existing Instance Bool_pos.
  #[local] Existing Instance Statement_pos.
  #[local] Existing Instance Witness_pos.
  #[local] Existing Instance Message_pos.
  #[local] Existing Instance Challenge_pos.
  #[local] Existing Instance Response_pos.

  Definition choiceWitness := 'fin #|Witness|.
  Definition choiceStatement := 'fin #|Statement|.
  Definition choiceMessage := 'fin #|Message|.
  Definition choiceChallenge := 'fin #|Challenge|.
  Definition choiceResponse := 'fin #|Response|.
  Definition choiceTranscript :=
    chProd (chProd (chProd choiceStatement choiceMessage) choiceChallenge) choiceResponse.
  Definition choiceBool := 'fin #|'bool|.

  Parameter Sigma_locs : {fset Location}.

  Parameter Simulator_locs : {fset Location}.

  Parameter Commit :
    ∀ (h : choiceStatement) (w : choiceWitness),
      code Sigma_locs [interface] choiceMessage.

  Parameter Response :
    ∀ (h : choiceStatement) (w : choiceWitness)
      (a : choiceMessage) (e : choiceChallenge),
      code Sigma_locs [interface] choiceResponse.

  Parameter Verify :
    ∀ (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge)
      (z : choiceResponse),
      choiceBool.

  Parameter Simulate :
    ∀ (h : choiceStatement) (e : choiceChallenge),
      code Simulator_locs [interface] choiceTranscript.

  Parameter Extractor :
    ∀ (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (e' : choiceChallenge)
      (z : choiceResponse) (z' : choiceResponse),
      'option choiceWitness.

  Parameter KeyGen : ∀ (w : choiceWitness), choiceStatement.

End SigmaProtocolAlgorithms.

Module SigmaProtocol (π : SigmaProtocolParams)
  (Alg : SigmaProtocolAlgorithms π).

  Import π.
  Import Alg.

  Notation " 'chStatement' " :=
    choiceStatement (in custom pack_type at level 2).
  Notation " 'chWitness' " :=
    choiceWitness (in custom pack_type at level 2).
  Notation " 'chChallenge' " :=
    choiceChallenge (in custom pack_type at level 2).
  Notation " 'chRelation' " :=
    (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).
  Definition choiceInput := (chProd (chProd choiceStatement choiceWitness) choiceChallenge).
  Notation " 'chInput' " :=
    choiceInput
    (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chTranscript' " :=
    choiceTranscript (in custom pack_type at level 2).
  Definition Opening := chProd choiceChallenge choiceResponse.
  Notation " 'chSoundness' " :=
    (chProd choiceStatement (chProd choiceMessage (chProd Opening Opening)))
    (in custom pack_type at level 2).

  Definition i_challenge := #|Challenge|.
  Definition i_witness := #|Witness|.

  Definition TRANSCRIPT : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.
  Definition ADV : nat := 3.
  Definition SOUNDNESS : nat := 4.

  Definition i_challenge_pos : Positive i_challenge.
  Proof.
    unfold i_challenge.
    apply Challenge_pos.
  Qed.

  Definition i_witness_pos : Positive i_witness.
  Proof.
    unfold i_witness.
    apply Witness_pos.
  Qed.

  #[local] Existing Instance i_challenge_pos.
  #[local] Existing Instance i_witness_pos.

  #[local] Open Scope package_scope.

  Definition SHVZK_real:
    package Sigma_locs
      [interface]
      [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package
      #def #[ TRANSCRIPT ] (hwe : chInput) : chTranscript
      {
        let '(h,w,e) := hwe in
        #assert (R (otf h) (otf w)) ;;
        a ← Commit h w ;;
        z ← Response h w a e ;;
        @ret choiceTranscript (h,a,e,z)
      }
    ].

  Definition SHVZK_ideal:
    package Simulator_locs
      [interface]
      [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package
      #def #[ TRANSCRIPT ] (hwe : chInput) : chTranscript
      {
        let '(h, w, e) := hwe in
        #assert (R (otf h) (otf w)) ;;
        t ← Simulate h e ;;
        ret t
      }
    ].

  (* Main security statement for Special Honest-Verifier Zero-Knowledge. *)
  Definition ɛ_SHVZK A := AdvantageE SHVZK_real SHVZK_ideal A.

  Definition Special_Soundness_f :
    package fset0
      [interface]
      [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
    :=
    [package
      #def #[ SOUNDNESS ] (t : chSoundness) : 'bool
      {
        let '(h, (a, ((e, z), (e', z')))) := t in
        let v1 := Verify h a e z in
        let v2 := Verify h a e' z' in
        if [&& (e != e') , (otf v1) & (otf v2) ] then
          match Extractor h a e e' z z' with
          | Some w => ret (R (otf h) (otf w))
          | None => ret false
          end
        else ret false
      }
    ].

  Definition Special_Soundness_t :
    package fset0
      [interface]
      [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
    :=
    [package
      #def #[ SOUNDNESS ] (t : chSoundness) : 'bool
      {
        let '(h, (a, ((e, z), (e', z')))) := t in
        let v1 := Verify h a e z in
        let v2 := Verify h a e' z' in
        ret [&& (e != e') , (otf v1) & (otf v2) ]
      }
    ].

  (* Simulation Sound Extractability *)
  (* Main security statement for 2-special soundness. *)
  Definition ɛ_soundness A :=
    AdvantageE Special_Soundness_t Special_Soundness_f A.

  (**************************************)
  (* Start of Commitment Scheme Section *)
  (**************************************)
  Section Commitments.

    Definition HIDING : nat := 5.
    Definition OPEN : nat := 6.
    Definition INIT : nat := 7.
    Definition GET : nat := 8.

    Definition challenge_loc : Location := ('option choiceChallenge; 7%N).
    Definition response_loc : Location := ('option choiceResponse; 8%N).

    Definition Com_locs : {fset Location} :=
      fset [:: challenge_loc ; response_loc ].


    Definition setup_loc : Location := ('bool; 10%N).
    Definition statement_loc : Location := (choiceStatement; 11%N).
    Definition witness_loc : Location := (choiceWitness; 12%N).
    Definition KEY_locs : {fset Location} := fset [:: setup_loc; witness_loc ; statement_loc].

    Definition choiceOpen := (chProd choiceChallenge choiceResponse).
    Notation " 'chOpen' " := choiceOpen (in custom pack_type at level 2).
    Notation " 'chKeys' " := (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).

    Lemma in_fset_left l (L1 L2 : {fset Location}) :
      is_true (l \in L1) →
      is_true (l \in (L1 :|: L2)).
    Proof.
      intros H.
      apply /fsetUP.
      left. assumption.
    Qed.

    Hint Extern 20 (is_true (_ \in (_ :|: _))) =>
      apply in_fset_left; solve [auto_in_fset]
      : typeclass_instances ssprove_valid_db.

    Definition KEY:
      package KEY_locs
        [interface]
        [interface
           #val #[ INIT ] : 'unit → 'unit ;
           #val #[ GET ] : 'unit → chStatement
        ]
      :=
      [package
         #def #[ INIT ] (_ : 'unit) : 'unit
         {
           b ← get setup_loc ;;
           #assert (negb b) ;;
           w ← sample uniform i_witness ;;
           let h := KeyGen w in
           #assert (R (otf h) (otf w)) ;;
           #put setup_loc := true ;;
           #put statement_loc := h ;;
           #put witness_loc := w ;;
           @ret 'unit Datatypes.tt
         }
         ;
         #def #[ GET ] (_ : 'unit) : chStatement
         {
           b ← get setup_loc ;;
           if b then
             h ← get statement_loc ;;
             w ← get witness_loc ;;
             ret h
           else
             fail
         }
      ].

    Definition Sigma_to_Com_locs := (Com_locs :|: Simulator_locs).

    #[tactic=notac] Equations? Sigma_to_Com:
      package Sigma_to_Com_locs
        [interface
          #val #[ INIT ] : 'unit → 'unit ;
          #val #[ GET ] : 'unit → chStatement
        ]
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
      := Sigma_to_Com :=
      [package
        #def #[ COM ] (e : chChallenge) : chMessage
        {
          #import {sig #[ INIT ] : 'unit → 'unit } as key_gen_init ;;
          #import {sig #[ GET ] : 'unit → chStatement } as key_gen_get ;;
          _ ← key_gen_init Datatypes.tt ;;
          h ← key_gen_get Datatypes.tt ;;
          '(h,a,e,z) ← Simulate h e ;;
          #put challenge_loc := Some e ;;
          #put response_loc := Some z ;;
          ret a
        }
       ;
        #def #[ OPEN ] (_ : 'unit) : chOpen
        {
          o_e ← get challenge_loc ;;
          o_z ← get response_loc ;;
          match (o_e, o_z) with
          | (Some e, Some z) => @ret choiceOpen (e, z)
          | _ => fail
          end
        }
        ;
        #def #[ VER ] (t : chTranscript) : 'bool
        {
          let '(h,a,e,z) := t in
          ret (otf (Verify h a e z))
        }
      ].
    Proof.
      unfold Sigma_to_Com_locs.
      ssprove_valid.
      eapply valid_injectLocations.
      1: apply fsubsetUr.
      eapply valid_injectMap.
      2: apply (Simulate x1 x).
      rewrite -fset0E.
      apply fsub0set.
    Qed.

    #[tactic=notac] Equations? Sigma_to_Com_Aux:
      package (setup_loc |: Sigma_to_Com_locs)
        [interface
          #val #[ TRANSCRIPT ] : chInput → chTranscript
        ]
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
      := Sigma_to_Com_Aux :=
      [package
        #def #[ COM ] (e : chChallenge) : chMessage
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript } as RUN ;;
          b ← get setup_loc ;;
          #assert (negb b) ;;
          w ← sample uniform i_witness ;;
          let h := KeyGen w in
          #assert (R (otf h) (otf w)) ;;
          #put setup_loc := true ;;
          '(h, a, e, z) ← RUN (h, w, e) ;;
          #put challenge_loc := Some e ;;
          #put response_loc := Some z ;;
          @ret choiceMessage a
        }
       ;
        #def #[ OPEN ] (_ : 'unit) : chOpen
        {
          o_e ← get challenge_loc ;;
          o_z ← get response_loc ;;
          match (o_e, o_z) with
          | (Some e, Some z) => @ret choiceOpen (e, z)
          | _ => fail
          end
        }
        ;
        #def #[ VER ] (t : chTranscript) : 'bool
        {
          let '(h,a,e,z) := t in
          ret (otf (Verify h a e z))
        }
      ].
    Proof.
      unfold Sigma_to_Com_locs, Com_locs.
      ssprove_valid.
      all: rewrite in_fsetU ; apply /orP ; right.
      all: rewrite in_fsetU ; apply /orP ; left.
      all: rewrite !fset_cons.
      1,3 : rewrite in_fsetU ; apply /orP ; left ; rewrite in_fset1 ; done.
      1,2 : rewrite in_fsetU ; apply /orP ; right ;
            rewrite in_fsetU ; apply /orP ; left ;
            rewrite in_fset1 ; done.
    Qed.

    Notation " 'chHiding' " := (chProd choiceChallenge choiceChallenge) (in custom pack_type at level 2).

    Definition Hiding_E := [interface #val #[ HIDING ] : chHiding → chMessage ].

    (* Commitment to input value*)
    Definition Hiding_real:
      package fset0
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        Hiding_E
      :=
      [package
        #def #[ HIDING ] (ms : chHiding) : chMessage
        {
          #import {sig #[ COM ] : chChallenge → chMessage } as com ;;
          let '(m1, m2) := ms in
          b ← sample uniform 1 ;;
          if Nat.even b then
            a ← com m1 ;;
            ret a
          else
            a ← com m2 ;;
            ret a
        }
      ].

    (* Commitment to random value *)
    Definition Hiding_ideal :
      package fset0
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        Hiding_E
      :=
      [package
        #def #[ HIDING ] (_ : chHiding) : chMessage
        {
          #import {sig #[ COM ] : chChallenge → chMessage } as com ;;
          e ← sample uniform i_challenge ;;
          t ← com e ;;
          ret t
        }
      ].

    Definition ɛ_hiding A :=
      AdvantageE
        (Hiding_real ∘ Sigma_to_Com ∘ KEY)
        (Hiding_ideal ∘ Sigma_to_Com ∘ KEY) (A ∘ (par KEY (ID Hiding_E))).

    Notation inv := (
      heap_ignore (fset [:: statement_loc ; witness_loc])
    ).

    Instance Invariant_inv : Invariant (Sigma_to_Com_locs :|: KEY_locs) (setup_loc |: Sigma_to_Com_locs) inv.
    Proof.
      ssprove_invariant.
      unfold KEY_locs.
      apply fsubsetU ; apply /orP ; left.
      apply fsubsetU ; apply /orP ; right.
      rewrite !fset_cons.
      apply fsubsetU ; apply /orP ; right.
      rewrite fsubUset ; apply /andP ; split.
      - apply fsubsetU ; apply /orP ; right.
        apply fsubsetU ; apply /orP ; left.
        apply fsubsetxx.
      - apply fsubsetU ; apply /orP ; left.
        rewrite fsubUset ; apply /andP ; split.
        + apply fsubsetxx.
        + rewrite -fset0E. apply fsub0set.
    Qed.

    Hint Extern 50 (_ = code_link _ _) =>
      rewrite code_link_scheme
      : ssprove_code_simpl.

    Theorem commitment_hiding :
      ∀ LA A,
        ValidPackage LA [interface
          #val #[ HIDING ] : chHiding → chMessage
        ] A_export (A ∘ (par KEY (ID Hiding_E))) →
        fdisjoint LA KEY_locs ->
        fdisjoint LA Sigma_to_Com_locs ->
        fdisjoint LA (fset [:: setup_loc]) ->
        fdisjoint LA Sigma_locs ->
        fdisjoint LA Simulator_locs ->
        fdisjoint Simulator_locs (fset [:: statement_loc ; witness_loc]) ->
        fdisjoint Sigma_locs (fset [:: statement_loc ; witness_loc]) ->
          (ɛ_hiding A) <= 0 +
           AdvantageE SHVZK_ideal SHVZK_real (((A ∘ par KEY (ID Hiding_E)) ∘ Hiding_real) ∘ Sigma_to_Com_Aux) +
           AdvantageE (Hiding_real ∘ Sigma_to_Com_Aux ∘ SHVZK_real)
             (Hiding_ideal ∘ Sigma_to_Com_Aux ∘ SHVZK_real) (A ∘ par KEY (ID Hiding_E)) +
           AdvantageE SHVZK_real SHVZK_ideal (((A ∘ par KEY (ID Hiding_E)) ∘ Hiding_ideal) ∘ Sigma_to_Com_Aux) +
           0.
    Proof.
      unfold ɛ_hiding, ɛ_SHVZK.
      intros LA A VA Hd1 Hd2 Hd3 HdSigma HdSimulator Hd4 Hd5.
      ssprove triangle (Hiding_real ∘ Sigma_to_Com ∘ KEY) [::
        (Hiding_real ∘ Sigma_to_Com_Aux ∘ SHVZK_ideal) ;
        (Hiding_real ∘ Sigma_to_Com_Aux ∘ SHVZK_real) ;
        (Hiding_ideal ∘ Sigma_to_Com_Aux ∘ SHVZK_real) ;
        (Hiding_ideal ∘ Sigma_to_Com_Aux ∘ SHVZK_ideal)
      ] (Hiding_ideal ∘ Sigma_to_Com ∘ KEY) (A ∘ (par KEY (ID Hiding_E)))
      as ineq.
      eapply le_trans. 1: exact ineq.
      clear ineq.
      repeat eapply lerD.
      - apply eq_ler.
        eapply eq_rel_perf_ind with (inv := inv).
        5: apply VA.
        1:{
          ssprove_valid.
          3: apply fsub0set.
          3: apply fsubsetxx.
          1: instantiate (1 := (Sigma_to_Com_locs :|: KEY_locs)).
          1: apply fsubsetUl.
          1: apply fsubsetUr.
        }
        1:{
          ssprove_valid.
          1: apply fsubsetxx.
          2: apply fsub0set.
          2: apply fsubsetxx.
          unfold Sigma_to_Com_locs.
          apply fsubsetU ; apply /orP ; right.
          apply fsubsetUr.
        }
        3,4: rewrite fdisjointUr ; apply /andP ; split.
        3-4,6: assumption.
        3: rewrite fset1E ; assumption.
        1: exact _.
        rewrite Sigma_to_Com_equation_1.
        rewrite Sigma_to_Com_Aux_equation_1.
        simplify_eq_rel h.
        ssprove_code_simpl.
        destruct h.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        ssprove_sync=>b.
        case (Nat.even b) eqn:Hb ; rewrite Hb.
        + ssprove_sync=> setup.
          ssprove_code_simpl.
          ssprove_code_simpl_more.
          apply r_assertD.
          1: done.
          intros _ _.
          ssprove_sync=> w.
          apply r_assertD.
          1: done.
          intros _ Rel.
          ssprove_swap_seq_lhs [:: 2 ; 1]%N.
          ssprove_contract_put_get_lhs.
          rewrite !cast_fun_K.
          rewrite Rel.
          ssprove_code_simpl.
          ssprove_code_simpl_more.
          ssprove_sync.
          ssprove_swap_lhs 1%N.
          ssprove_contract_put_get_lhs.
          ssprove_swap_seq_lhs [:: 0 ; 1]%N.
          ssprove_contract_put_get_lhs.
          apply r_put_lhs.
          apply r_put_lhs.
          ssprove_restore_pre.
          1: ssprove_invariant.
          eapply rsame_head_alt.
          1: exact _.
          {
            unfold inv.
            intros l lin h1 s' h2.
            apply h2.
            move: Hd4 => /fdisjointP Hd4.
            apply Hd4.
            apply lin.
          }
          {
            unfold inv.
            intros l v lin.
            apply put_pre_cond_heap_ignore.
          }
          intros t.
          destruct t.
          destruct s1.
          destruct s1.
          ssprove_sync.
          ssprove_sync.
          apply r_ret.
          done.
        + ssprove_sync=>setup.
          ssprove_code_simpl.
          ssprove_code_simpl_more.
          apply r_assertD.
          1: done.
          intros _ _.
          ssprove_sync=>w.
          apply r_assertD.
          1: done.
          intros _ Rel.
          ssprove_swap_seq_lhs [:: 2 ; 1]%N.
          ssprove_contract_put_get_lhs.
          rewrite !cast_fun_K.
          rewrite Rel.
          ssprove_code_simpl.
          ssprove_code_simpl_more.
          ssprove_sync.
          ssprove_swap_lhs 1%N.
          ssprove_contract_put_get_lhs.
          ssprove_swap_seq_lhs [:: 0 ; 1]%N.
          ssprove_contract_put_get_lhs.
          apply r_put_lhs.
          apply r_put_lhs.
          ssprove_restore_pre.
          1: ssprove_invariant.
          eapply rsame_head_alt.
          1: exact _.
          {
            unfold inv.
            intros l lin h1 s' h2.
            apply h2.
            move: Hd4 => /fdisjointP Hd4.
            apply Hd4.
            apply lin.
          }
          {
            unfold inv.
            intros l v lin.
            apply put_pre_cond_heap_ignore.
          }
          intros t.
          destruct t.
          destruct s1.
          destruct s1.
          ssprove_sync.
          ssprove_sync.
          apply r_ret.
          done.
      - rewrite -!Advantage_link.
        1: apply eq_ler ; done.
      - done.
      - rewrite -!Advantage_link.
        1: apply eq_ler ; done.
      - apply eq_ler.
        eapply eq_rel_perf_ind with (inv := inv).
        5: apply VA.
        1:{
          ssprove_valid.
          4: apply fsubsetxx.
          3: apply fsub0set.
          2: instantiate (1 := (Simulator_locs :|: (setup_loc |: Sigma_to_Com_locs))).
          - apply fsubsetUr.
          - apply fsubsetUl.
        }
        1:{
          ssprove_valid.
          3: apply fsub0set.
          3: apply fsubsetxx.
          1: instantiate (1 := (Sigma_to_Com_locs :|: KEY_locs)).
          - apply fsubsetUl.
          - apply fsubsetUr.
        }
        3,4: rewrite fdisjointUr ; apply /andP ; split.
        4: rewrite fdisjointUr ; apply /andP ; split.
        3,5-7: assumption.
        3: rewrite fset1E ; assumption.
        {
          ssprove_invariant.
          unfold KEY_locs.
          apply fsubsetU ; apply /orP ; right.
          apply fsubsetU ; apply /orP ; right.
          rewrite !fset_cons.
          apply fsubsetU ; apply /orP ; right.
          rewrite fsubUset ; apply /andP ; split.
          - apply fsubsetU ; apply /orP ; right.
            apply fsubsetU ; apply /orP ; left.
            apply fsubsetxx.
          - apply fsubsetU ; apply /orP ; left.
            rewrite fsubUset ; apply /andP ; split.
            + apply fsubsetxx.
            + rewrite -fset0E. apply fsub0set.
        }
        rewrite Sigma_to_Com_equation_1.
        rewrite Sigma_to_Com_Aux_equation_1.
        simplify_eq_rel h.
        ssprove_code_simpl.
        destruct h.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        ssprove_sync=>e.
        ssprove_sync=> setup.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        apply r_assertD.
        1: done.
        intros _ _.
        ssprove_sync=> w.
        apply r_assertD.
        1: done.
        intros _ Rel.
        ssprove_swap_seq_rhs [:: 2 ; 1]%N.
        ssprove_contract_put_get_rhs.
        rewrite !cast_fun_K.
        rewrite Rel.
        ssprove_code_simpl.
        ssprove_code_simpl_more.
        ssprove_sync.
        ssprove_swap_rhs 1%N.
        ssprove_contract_put_get_rhs.
        ssprove_swap_seq_rhs [:: 0 ; 1]%N.
        ssprove_contract_put_get_rhs.
        apply r_put_rhs.
        apply r_put_rhs.
        ssprove_restore_pre.
        1: ssprove_invariant.
        eapply rsame_head_alt.
        1: exact _.
        {
          unfold inv.
          intros l lin h1 s' h2.
          apply h2.
          move: Hd4 => /fdisjointP Hd4.
          apply Hd4.
          apply lin.
        }
        {
          unfold inv.
          intros l v lin.
          apply put_pre_cond_heap_ignore.
        }
        intros t.
        destruct t.
        destruct s1.
        destruct s1.
        ssprove_sync.
        ssprove_sync.
        apply r_ret.
        done.
    Qed.

    Definition Com_Binding:
      package fset0
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
      :=
      [package
        #def #[ SOUNDNESS ] (t : chSoundness) : 'bool
        {
          #import {sig #[ VER ] : chTranscript → 'bool } as Ver ;;
          let '(h, (a, ((e, z), (e', z')))) := t in
          v1 ← Ver (h, a, e, z) ;;
          v2 ← Ver (h, a, e', z') ;;
          ret [&& (e != e'), v1 & v2]
        }
      ].

    Lemma commitment_binding :
      ∀ LA A,
        ValidPackage LA [interface
          #val #[ SOUNDNESS ] : chSoundness → 'bool
        ] A_export A →
        fdisjoint LA (Sigma_to_Com_locs :|: KEY_locs) →
        AdvantageE (Com_Binding ∘ Sigma_to_Com ∘ KEY) (Special_Soundness_t) A = 0.
    Proof.
      intros LA A VA Hdisj.
      eapply eq_rel_perf_ind_eq.
      4: apply VA.
      1:{
        ssprove_valid.
        3: apply fsub0set.
        1: instantiate (1 := (Sigma_to_Com_locs :|: KEY_locs)).
        2: apply fsubsetUr.
        1: apply fsubsetUl.
        apply fsubsetxx.
      }
      1: ssprove_valid.
      2: assumption.
      2: apply fdisjoints0.
      rewrite Sigma_to_Com_equation_1.
      simplify_eq_rel h.
      ssprove_code_simpl.
      simpl.
      destruct h, s0, s1, s1, s2.
      apply r_ret. auto.
    Qed.

  End Commitments.

  (* This section aim to prove an automatic conversation between the sampling of the random challenge and a random oracle. *)
  (* The main difference is that the random oracle is a query parametrized by the context of the execution. *)

  Module OracleParams <: ROParams.

    Definition Query := prod_finType Statement Message.
    Definition Random := Challenge.

    Definition Query_pos : Positive #|Query|.
    Proof.
      unfold Query. rewrite !card_prod.
      apply Positive_prod.
      - apply Statement_pos.
      - apply Message_pos.
    Qed.

    Definition Random_pos : Positive #|Random| := Challenge_pos.

  End OracleParams.

  Module Oracle := RO OracleParams.

  Import Oracle OracleParams.

  Section FiatShamir.

    Definition RUN : nat := 7.
    Definition VERIFY : nat := 8.
    Definition SIM : nat := 9.

    Context (Sim_locs : {fset Location}).
    Context (Sim : choiceStatement → code Sim_locs [interface] choiceTranscript).

    Definition prod_assoc : chProd choiceStatement choiceMessage → chQuery.
    Proof.
      cbn. intros [statement message].
      rewrite !card_prod.
      apply mxvec_index. all: assumption.
    Qed.

    (* TW: I moved it here because it might induce back-tracking and we want to
       avoid it because of time-consumption.
    *)
    Hint Extern 20 (ValidCode ?L ?I ?c.(prog)) =>
      eapply valid_injectMap ; [| eapply c.(prog_valid) ]
      : typeclass_instances ssprove_valid_db.

    Definition Fiat_Shamir :
      package Sigma_locs
        [interface
          #val #[ INIT ] : 'unit → 'unit ;
          #val #[ QUERY ] : 'query → 'random
        ]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package
        #def #[ VERIFY ] (t : chTranscript) : 'bool
        {
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,a,e,z) := t in
          e ← RO_query (prod_assoc (h, a)) ;;
          ret (otf (Verify h a e z))
        } ;
        #def #[ RUN ] (hw : chRelation) : chTranscript
        {
          #import {sig #[ INIT ] : 'unit → 'unit } as RO_init ;;
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          a ← Commit h w ;;
          RO_init Datatypes.tt ;;
          e ← RO_query (prod_assoc (h, a)) ;;
          z ← Response h w a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition Fiat_Shamir_SIM :
      package Sim_locs
        [interface
          #val #[ QUERY ] : 'query → 'random
        ]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package
        #def #[ VERIFY ] (t : chTranscript) : 'bool
        {
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,a,e,z) := t in
          e ← RO_query (prod_assoc (h, a)) ;;
          ret (otf (Verify h a e z))
        } ;
        #def #[ RUN ] (hw : chRelation) : chTranscript
        {
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          t ← Sim h ;;
          ret t
        }
      ].

    Definition RUN_interactive :
      package Sigma_locs
        [interface]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package
        #def #[ VERIFY ] (t : chTranscript) : 'bool
        {
          let '(h,a,e,z) := t in
          ret (otf (Verify h a e z))
        } ;
        #def #[ RUN ] (hw : chRelation) : chTranscript
        {
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          a ← Commit h w ;;
          e ← sample uniform i_random ;;
          z ← Response h w a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition SHVZK_real_aux :
      package fset0
        [interface #val #[ TRANSCRIPT ] : chInput → chTranscript ]
        [interface #val #[ RUN ] : chRelation → chTranscript ]
      :=
      [package
        #def #[ RUN ] (hw : chRelation) : chTranscript
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript } as SHVZK ;;
          e ← sample uniform i_random ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
      ].

    Lemma run_interactive_shvzk :
      ∀ LA A,
        ValidPackage LA [interface
          #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
        fdisjoint LA Sigma_locs →
        AdvantageE RUN_interactive (SHVZK_real_aux ∘ SHVZK_real) A = 0.
    Proof.
      intros LA A Va Hdisj.
      eapply eq_rel_perf_ind_eq.
      5,6: apply Hdisj.
      4: apply Va.
      2:{
        rewrite <- fsetUid.
        eapply valid_link.
        - eapply (valid_package_inject_locations).
          2: apply SHVZK_real_aux.
          apply fsub0set.
        - apply SHVZK_real.
      }
      1:{
        eapply valid_package_inject_export.
        2: apply RUN_interactive.
        apply fsubset_ext. intros ? ?.
        rewrite fset_cons. apply /fsetUP. right. assumption.
      }
      simplify_eq_rel hw.
      ssprove_code_simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      ssprove_sync_eq. intro rel.
      ssprove_swap_rhs 0%N.
      apply rsame_head. intros [a st].
      ssprove_sync_eq. intro e.
      apply rsame_head. intro z.
      apply r_ret. intuition auto.
    Qed.

    Hint Extern 50 (_ = code_link _ _) =>
      rewrite code_link_scheme
      : ssprove_code_simpl.

    Theorem fiat_shamir_correct :
      ∀ LA A ,
        ValidPackage LA [interface
          #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
        fdisjoint LA (Sigma_locs :|: RO_locs) →
        fdisjoint Sigma_locs RO_locs →
        AdvantageE (Fiat_Shamir ∘ RO) RUN_interactive A = 0.
    Proof.
      intros LA A Va Hdisj Hdisj_oracle.
      eapply eq_rel_perf_ind_ignore.
      6: apply Hdisj.
      6:{
        rewrite fdisjointUr in Hdisj. move: Hdisj => /andP [h _].
        apply h.
      }
      5: apply Va.
      1:{
        ssprove_valid.
        2: apply fsubsetUl.
        2: apply fsubsetUr.
        eapply valid_package_inject_export.
        2: apply Fiat_Shamir.
        apply fsubset_ext. intros.
        rewrite fset_cons. apply /fsetUP. right. assumption.
      }
      1:{
        eapply valid_package_inject_export.
        2: apply RUN_interactive.
        apply fsubset_ext. intros.
        rewrite fset_cons. apply /fsetUP. right. assumption.
      }
      1:{ apply fsubsetU. erewrite fsubsetUr. auto. }
      simplify_eq_rel hw.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_sync. intros rel.
      eapply rsame_head_alt.
      1: exact _.
      1:{
        intros l Il.
        apply get_pre_cond_heap_ignore.
        revert l Il.
        apply /fdisjointP.
        assumption.
      }
      1:{ intros. apply put_pre_cond_heap_ignore. }
      intros [a st].
      ssprove_contract_put_get_lhs.
      rewrite emptymE.
      apply r_put_lhs.
      ssprove_sync. intro e.
      apply r_put_lhs.
      ssprove_restore_pre. 1: ssprove_invariant.
      eapply r_reflexivity_alt.
      - exact _.
      - intros l Il.
        ssprove_invariant.
        revert l Il.
        apply /fdisjointP. assumption.
      - intros. ssprove_invariant.
    Qed.

    (* GOAL: reason about ZK property *)

  End FiatShamir.

End SigmaProtocol.
