
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

  Parameter Sigma_locs : Locations.

  Parameter Simulator_locs : Locations.

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
    package [interface]
      [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package Sigma_locs ;
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
    package [interface]
      [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package Simulator_locs ;
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
    package [interface]
      [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
    :=
    [package emptym ;
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
    package [interface]
      [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
    :=
    [package emptym ;
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

    Definition challenge_loc : Location := (7, 'option choiceChallenge).
    Definition response_loc : Location := (8, 'option choiceResponse).

    Definition Com_locs : Locations :=
      [fmap challenge_loc ; response_loc ].

    Definition setup_loc : Location := (10, 'bool).
    Definition statement_loc : Location := (11, choiceStatement).
    Definition witness_loc : Location := (12, choiceWitness).
    Definition KEY_locs : Locations := [fmap setup_loc; witness_loc ; statement_loc].

    Definition choiceOpen := (chProd choiceChallenge choiceResponse).
    Notation " 'chOpen' " := choiceOpen (in custom pack_type at level 2).
    Notation " 'chKeys' " := (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).

    Definition KEY:
      package [interface]
        [interface
           #val #[ INIT ] : 'unit → 'unit ;
           #val #[ GET ] : 'unit → chStatement
        ]
      :=
      [package KEY_locs ;
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
           @ret 'unit tt
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

    Definition Sigma_to_Com_locs := unionm Com_locs Simulator_locs.


    (* MK: Does this hint induce backtracking? *)
    Hint Extern 10 (ValidCode ?L ?I (prog _)) =>
      eapply valid_injectMap;
        [| eapply valid_injectLocations ];
        [| | apply prog_valid ] 
          : typeclass_instances ssprove_valid_db.

    Context (compatComSim : fcompat Com_locs Simulator_locs).

    Definition Sigma_to_Com :
      package
        [interface
          #val #[ INIT ] : 'unit → 'unit ;
          #val #[ GET ] : 'unit → chStatement
        ]
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ] :=
      [package Sigma_to_Com_locs ;
        #def #[ COM ] (e : chChallenge) : chMessage
        {
          #import {sig #[ INIT ] : 'unit → 'unit } as key_gen_init ;;
          #import {sig #[ GET ] : 'unit → chStatement } as key_gen_get ;;
          _ ← key_gen_init tt ;;
          h ← key_gen_get tt ;;
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

    Definition Sigma_to_Com_Aux:
      package
        [interface
          #val #[ TRANSCRIPT ] : chInput → chTranscript
        ]
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ] :=
      [package unionm [fmap setup_loc] Sigma_to_Com_locs ;
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

    Notation " 'chHiding' " := (chProd choiceChallenge choiceChallenge) (in custom pack_type at level 2).

    Definition Hiding_E := [interface #val #[ HIDING ] : chHiding → chMessage ].

    (* Commitment to input value*)
    Definition Hiding_real:
      package
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        Hiding_E
      :=
      [package emptym ;
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
      package
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        Hiding_E
      :=
      [package emptym ;
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
      heap_ignore [fmap statement_loc ; witness_loc]
    ).

    Instance Invariant_inv : Invariant
      (unionm KEY_locs Sigma_to_Com_locs)
      (unionm (unionm [fmap setup_loc] Sigma_to_Com_locs) Simulator_locs) inv.
    Proof.
      ssprove_invariant.
      fmap_solve.
    Qed.

    Hint Extern 50 (_ = code_link _ _) =>
      rewrite code_link_scheme
      : ssprove_code_simpl.


    Theorem commitment_hiding :
      ∀ LA A,
        ValidPackage LA [interface
          #val #[ HIDING ] : chHiding → chMessage
        ] A_export (A ∘ (par KEY (ID Hiding_E))) →
        fseparate LA KEY_locs ->
        fseparate LA Sigma_to_Com_locs ->
        fseparate LA [fmap setup_loc] ->
        fseparate LA Sigma_locs ->
        fseparate LA Simulator_locs ->
        fseparate Simulator_locs KEY_locs ->
        fseparate Simulator_locs [fmap setup_loc] ->
        fseparate Sigma_locs KEY_locs ->
          (ɛ_hiding A) <= 0 +
           AdvantageE SHVZK_ideal SHVZK_real (((A ∘ par KEY (ID Hiding_E)) ∘ Hiding_real) ∘ Sigma_to_Com_Aux) +
           AdvantageE (Hiding_real ∘ Sigma_to_Com_Aux ∘ SHVZK_real)
             (Hiding_ideal ∘ Sigma_to_Com_Aux ∘ SHVZK_real) (A ∘ par KEY (ID Hiding_E)) +
           AdvantageE SHVZK_real SHVZK_ideal (((A ∘ par KEY (ID Hiding_E)) ∘ Hiding_ideal) ∘ Sigma_to_Com_Aux) +
           0.
    Proof.
      unfold ɛ_hiding, ɛ_SHVZK.
      intros LA A VA Hd1 Hd2 Hd3 HdSigma HdSimulator Hd4 HdS' Hd5.
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
        1,2: ssprove_valid.
        3,4: fmap_solve.
        1: rewrite 2!union0m.
        1: rewrite -> unionmC by fmap_solve.
        1: apply Invariant_inv.
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
            eapply notin_temp; [ eassumption | ].
            apply (fseparate_trans_r _ _ KEY_locs).
            1,2: fmap_solve.
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
            eapply notin_temp; [ eassumption | ].
            apply (fseparate_trans_r _ _ KEY_locs).
            1,2: fmap_solve.
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
        1,2: ssprove_valid.
        3,4: fmap_solve.
        {
          ssprove_invariant.
          fmap_solve. (* MK: long exec time *)
        }
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
          eapply notin_temp; [ eassumption | ].
          apply (fseparate_trans_r _ _ KEY_locs).
          1,2: fmap_solve.
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
      package
        [interface
          #val #[ COM ] : chChallenge → chMessage ;
          #val #[ OPEN ] : 'unit → chOpen ;
          #val #[ VER ] : chTranscript → 'bool
        ]
        [interface #val #[ SOUNDNESS ] : chSoundness → 'bool ]
      :=
      [package emptym ;
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
        fseparate LA Sigma_to_Com_locs →
        fseparate LA KEY_locs →
        fcompat Simulator_locs KEY_locs →
        AdvantageE (Com_Binding ∘ Sigma_to_Com ∘ KEY) (Special_Soundness_t) A = 0.
    Proof.
      intros LA A VA Hd1 Hd2 Hd3.
      eapply eq_rel_perf_ind_eq.
      4: apply VA.
      1,2,4,5: ssprove_valid.
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

    Definition Query : finType := prod Statement Message.
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

    Context (Sim_locs : Locations).
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
      package
        [interface
          #val #[ INIT ] : 'unit → 'unit ;
          #val #[ QUERY ] : 'query → 'random
        ]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package Sigma_locs ;
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
          RO_init tt ;;
          e ← RO_query (prod_assoc (h, a)) ;;
          z ← Response h w a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition Fiat_Shamir_SIM :
      package
        [interface
          #val #[ QUERY ] : 'query → 'random
        ]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package Sim_locs ;
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
      package
        [interface]
        [interface
          #val #[ VERIFY ] : chTranscript → 'bool ;
          #val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package Sigma_locs ;
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
      package
        [interface #val #[ TRANSCRIPT ] : chInput → chTranscript ]
        [interface #val #[ RUN ] : chRelation → chTranscript ]
      :=
      [package Sigma_locs ;
        #def #[ RUN ] (hw : chRelation) : chTranscript
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript } as SHVZK ;;
          e ← sample uniform i_random ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
      ].

    Definition IRUN := [interface #val #[ RUN ] : chRelation → chTranscript].

    Lemma run_interactive_shvzk :
      ∀ LA A,
        ValidPackage LA [interface
          #val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
        fseparate LA Sigma_locs →
        AdvantageE (ID IRUN ∘ RUN_interactive) (SHVZK_real_aux ∘ SHVZK_real) A = 0.
    Proof.
      intros LA A Va Hdisj.
      eapply eq_rel_perf_ind_eq.
      4: apply Va.
      1,2: ssprove_valid.
      2,3: fmap_solve.
      simplify_eq_rel hw.
      ssprove_code_simpl.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_code_simpl_more.
      ssprove_code_simpl.
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

    (* Adequacy: fiat_shamir is not proven equivalent on the VERIFY call *)
    Theorem fiat_shamir_correct :
      ∀ LA A ,
        ValidPackage LA IRUN A_export A →
        fseparate LA Sigma_locs →
        fseparate LA RO_locs →
        fseparate Sigma_locs RO_locs →
        AdvantageE (ID IRUN ∘ Fiat_Shamir ∘ RO) (ID IRUN ∘ RUN_interactive) A = 0.
    Proof.
      intros LA A Va Hd1 Hd2 Hd3.
      eapply eq_rel_perf_ind_ignore.
      5: ssprove_valid.
      1,2: ssprove_valid.
      3,4: fmap_solve.
      1: rewrite union0m; apply fsubmapUl_trans, fsubmapUr; fmap_solve.
      simplify_eq_rel hw.
      destruct hw as [h w].
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_sync. intros rel.
      ssprove_code_simpl.
      eapply rsame_head_alt.
      1: exact _.
      1:{
        intros l Il.
        apply get_pre_cond_heap_ignore.
        fmap_solve.
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
      - intros. ssprove_invariant.
    Qed.

    (* GOAL: reason about ZK property *)

  End FiatShamir.

End SigmaProtocol.
