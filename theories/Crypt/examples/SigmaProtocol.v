
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl
  Package Prelude RandomOracle.

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
Import mc_1_10.Num.Theory.

Import PackageNotation.

#[local] Open Scope ring_scope.

Module Type SigmaProtocolParams.

  Parameter Witness Statement Message Challenge Response State : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.
  Parameter R : Statement → Witness → bool.

  Parameter Statement_pos : Positive #|Statement|.
  Parameter Witness_pos : Positive #|Witness|.
  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.
  Parameter Response_pos : Positive #|Response|.
  Parameter State_pos : Positive #|State|.
  Parameter Bool_pos : Positive #|bool_choiceType|.

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
  #[local] Existing Instance State_pos.

  Definition choiceWitness := 'fin #|Witness|.
  Definition choiceStatement := 'fin #|Statement|.
  Definition choiceMessage := 'fin #|Message|.
  Definition choiceChallenge := 'fin #|Challenge|.
  Definition choiceResponse := 'fin #|Response|.
  Definition choiceTranscript :=
    chProd (chProd (chProd choiceStatement choiceMessage) choiceChallenge) choiceResponse.
  Definition choiceState := 'fin #|State|.
  Definition choiceBool := 'fin #|bool_choiceType|.

  Parameter Sigma_locs : {fset Location}.
  Parameter Simulator_locs : {fset Location}.

  Parameter Commit :
    ∀ (h : choiceStatement) (w : choiceWitness),
      code Sigma_locs [interface] (choiceMessage × choiceState).

  Parameter Response :
    ∀ (h : choiceStatement) (w : choiceWitness) (s : choiceState)
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

End SigmaProtocolAlgorithms.

Module SigmaProtocol (π : SigmaProtocolParams)
  (Alg : SigmaProtocolAlgorithms π).

  Import π.
  Import Alg.

  Notation " 'chStatement' " :=
    choiceStatement (in custom pack_type at level 2).
  Notation " 'chRelation' " :=
    (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).
  Notation " 'chInput' " :=
    (chProd (chProd choiceStatement choiceWitness) choiceChallenge)
    (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chTranscript' " :=
    choiceTranscript (in custom pack_type at level 2).
  Definition Opening := chProd choiceChallenge choiceResponse.
  Notation " 'chSoundness' " :=
    (chProd choiceMessage (chProd Opening Opening))
    (in custom pack_type at level 2).

  Definition i_challenge := #|Challenge|.
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

  #[local] Existing Instance i_challenge_pos.

  #[local] Open Scope package_scope.

  Definition SHVZK_real:
    package Sigma_locs
      [interface]
      [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package
      def #[ TRANSCRIPT ] (hwe: chInput) : chTranscript
      {
        let '(h,w,e) := hwe in
        #assert (R (otf h) (otf w)) ;;
        m ← Commit h w ;;
        let '(a, s) := m in
        z ← Response h w s a e ;;
        @ret choiceTranscript (h,a,e,z)
      }
    ].

  Definition SHVZK_ideal:
    package Simulator_locs
      [interface]
      [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package
      def #[ TRANSCRIPT ] (hwe: chInput) : chTranscript
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
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chSoundness ]
      [interface val #[ SOUNDNESS ] : chStatement → 'bool ]
    :=
    [package
      def #[ SOUNDNESS ] (h : chStatement) : 'bool
      {
        #import {sig #[ ADV ] : chStatement → chSoundness } as A ;;
        '(a, ((e, z), (e', z'))) ← A h ;;
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
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chSoundness ]
      [interface val #[ SOUNDNESS ] : chStatement → 'bool ]
    :=
    [package
      def #[ SOUNDNESS ] (h : chStatement) : 'bool
      {
        #import {sig #[ ADV ] : chStatement → chSoundness } as A ;;
        '(a, ((e, z), (e', z'))) ← A(h) ;;
        let v1 := Verify h a e z in
        let v2 := Verify h a e' z' in
        ret [&& (e != e') , (otf v1) & (otf v2) ]
      }
    ].

  (* Main security statement for 2-special soundness. *)
  Definition ɛ_soundness A Adv :=
    AdvantageE (Special_Soundness_t ∘ Adv) (Special_Soundness_f ∘ Adv) A.

  (**************************************)
  (* Start of Commitment Scheme Section *)
  (**************************************)
  Section Commitments.

    Definition HIDING : nat := 5.
    Definition OPEN : nat := 6.

    Definition challenge_loc : Location := ('option choiceChallenge; 7%N).
    Definition response_loc : Location := ('option choiceResponse; 8%N).

    Definition Com_locs : {fset Location} := fset [:: challenge_loc ; response_loc].

    Definition choiceOpen := (chProd choiceChallenge choiceResponse).
    Notation " 'chOpen' " := choiceOpen (in custom pack_type at level 2).

    Lemma in_fset_left l (L1 L2 : {fset Location}):
        is_true (l \in L1) →
        is_true (l \in (L1 :|: L2)).
    Proof.
      intros H.
      apply /fsetUP.
      left. assumption.
    Qed.

    Hint Extern 20 (is_true (_ \in (_ :|: _))) =>
      apply in_fset_left; solve [auto_in_fset] : typeclass_instances ssprove_valid_db.

    Definition Sigma_to_Com:
      package (Com_locs :|: Sigma_locs)
        [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
        [interface
          val #[ COM ] : chInput → chMessage ;
          val #[ OPEN ] : 'unit → chOpen ;
          val #[ VER ] : chTranscript → 'bool]
      :=
      [package
        def #[ COM ] (hwe : chInput) : chMessage
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript} as run ;;
          '(h,a,e,z) ← run hwe ;;
          put challenge_loc := Some e ;;
          put response_loc := Some z ;;
          ret a
        } ;
        def #[ OPEN ] (_ : 'unit) : chOpen
        {
          o_e ← get challenge_loc ;;
          o_z ← get response_loc ;;
          match (o_e, o_z) with
            | (Some e, Some z) => @ret choiceOpen (e, z)
            | _ => fail
          end
        }
        ;
        def #[ VER ] (t : chTranscript) : 'bool
        {
          let '(h,a,e,z) := t in ret (otf (Verify h a e z))
        }
      ].

    (* Commitment to input value*)
    Definition Hiding_real :
      package fset0
        [interface
          val #[ COM ] : chInput → chMessage ;
          val #[ OPEN ] : 'unit → chOpen ;
          val #[ VER ] : chTranscript → 'bool]
        [interface val #[ HIDING ] : chInput → chMessage]
      :=
      [package
        def #[ HIDING ] (hwe : chInput) : chMessage
        {
          #import {sig #[ COM ] : chInput → chMessage} as com ;;
          _ ← sample uniform i_challenge ;;
          a ← com hwe ;;
          ret a
        }
      ].

    (* Commitment to random value *)
    Definition Hiding_ideal :
      package fset0
        [interface
          val #[ COM ] : chInput → chMessage ;
          val #[ OPEN ] : 'unit → chOpen ;
          val #[ VER ] : chTranscript → 'bool]
        [interface val #[ HIDING ] : chInput → chMessage]
      :=
      [package
        def #[ HIDING ] (hwe : chInput) : chMessage
        {
          #import {sig #[ COM ] : chInput → chMessage} as com ;;
          let '(h,w,_) := hwe in
          e ← sample uniform i_challenge ;;
          t ← com (h,w,e) ;;
          ret t
        }
      ].

    Definition ɛ_hiding A :=
      AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_real) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_real) A.

    Theorem commitment_hiding :
      ∀ LA A eps,
        ValidPackage LA [interface
          val #[ HIDING ] : chInput → chMessage
        ] A_export A →
        (∀ A',
          ValidPackage (LA :|: Com_locs :|: Sigma_locs) [interface
            val #[ TRANSCRIPT ] : chInput → chTranscript
          ] A_export A' →
          ɛ_SHVZK A' <= eps
        ) →
        AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A <=
        (ɛ_hiding A) + eps + eps.
    Proof.
      unfold ɛ_hiding, ɛ_SHVZK.
      intros LA A eps Va Hadv.
      ssprove triangle (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) [::
        (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_real) ;
        (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_real)
      ] (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A
      as ineq.
      apply: ler_trans. 1: exact ineq.
      clear ineq.
      rewrite -!Advantage_link.
      eapply ler_add.
      1: rewrite GRing.addrC ; eapply ler_add.
      1: apply lerr.
      1: have := Hadv (A ∘ Hiding_real ∘ Sigma_to_Com).
      2: have := Hadv (A ∘ Hiding_ideal ∘ Sigma_to_Com).
      all:
        rewrite -link_assoc Advantage_sym ;
        intros H ; apply H ;
        ssprove_valid.
      1,5: apply fsub0set.
      1,4: apply fsubsetxx.
      1,3: eapply fsubset_trans; apply fsubsetUl.
      1,2: eapply fsetSU; apply fsubsetUr.
    Qed.

    Definition Com_Binding :
      package Sigma_locs
        [interface val #[ ADV ] : chStatement → chSoundness ]
        [interface val #[ SOUNDNESS ] : chStatement → 'bool ]
      :=
      [package
        def #[ SOUNDNESS ] (h : chStatement) : 'bool
        {
          #import {sig #[ ADV ] : chStatement → chSoundness} as A ;;
          '(a, ((e, z), (e', z'))) ← A h ;;
          let v1 := Verify h a e z in
          let v2 := Verify h a e' z' in
          ret [&& (e != e') , (otf v1) & (otf v2) ]
        }
      ].

    Lemma commitment_binding :
      ∀ LA A LAdv Adv,
        ValidPackage LA [interface
          val #[ SOUNDNESS ] : chStatement → 'bool
        ] A_export A →
        ValidPackage LAdv [interface] [interface
          val #[ ADV ] : chStatement → chSoundness
        ] Adv →
        fdisjoint LA (Sigma_locs :|: LAdv) →
        AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <=
        ɛ_soundness A Adv.
    Proof.
      intros LA A LAdv Adv VA VAdv Hdisj.
      ssprove triangle (Com_Binding ∘ Adv) [::
        (Special_Soundness_t ∘ Adv)
      ] (Special_Soundness_f ∘ Adv) A as ineq.
      apply: ler_trans. 1: exact ineq.
      rewrite ger_addr.
      apply eq_ler.
      eapply eq_rel_perf_ind_eq.
      4: apply VA.
      1,2: eapply valid_link ; last first ; [ apply VAdv | trivial ].
      1: apply Com_Binding.
      1: apply Special_Soundness_t.
      2,3: assumption.
      simplify_eq_rel h.

      destruct (Adv ADV).
      2:{ apply r_ret => ?? ->. split. all: reflexivity. }

      destruct t, s.
      repeat destruct chUniverse_eqP.
      2,3: apply r_ret=> ?? -> ; split ; reflexivity.
      apply rsame_head => run.
      ssprove_code_simpl.
      destruct run.
      destruct s0.
      destruct s0, s1.
      apply r_ret.
      auto.
    Qed.

  End Commitments.

  (* This section aim to prove an automatic conversation between the sampling of the random challenge and a random oracle. *)
  (* The main difference is that the random oracle is a query parametrized by the context of the execution. *)
  Import RandomOracle.

  Module OracleParams <: ROParams.

    Definition Query := prod_finType Statement Message.
    Definition Random := Challenge.

    Definition Query_pos : Positive #|Query|.
    Proof.
      unfold Query. rewrite !card_prod.
      repeat apply Positive_prod.
      - apply Statement_pos.
      - apply Message_pos.
    Qed.

    Definition Random_pos : Positive #|Random| := Challenge_pos.

  End OracleParams.

  Module Oracle := RO OracleParams.

  Import Oracle OracleParams.

  Section FiatShamir.

    Definition RUN : nat := 6.
    Definition VERIFY : nat := 7.

    Definition prod_assoc : chProd choiceStatement choiceMessage → chQuery.
    Proof.
      cbn.
      apply prod_curry.
      intros statement message.
      rewrite !card_prod.
      repeat apply mxvec_index ; assumption.
    Qed.

    (* TW: I moved it here because it might induce back-tracking and we want to
      avoid it because of time-consumption.
    *)
    Hint Extern 20 (ValidCode ?L ?I ?c.(prog)) =>
      eapply valid_injectMap ; [| eapply c.(prog_valid) ]
      : typeclass_instances ssprove_valid_db.

    Definition Fiat_Shamir:
      package Sigma_locs
        [interface
          val #[ INIT ] : 'unit → 'unit ;
          val #[ QUERY ] : 'query → 'random]
        [interface
          val #[ VERIFY ] : chTranscript → 'bool ;
          val #[ RUN ] : chRelation → chTranscript]
      :=
      [package
        def #[ VERIFY ] (t: chTranscript) : 'bool
        {
          #import {sig #[ QUERY ] : 'query → 'random} as RO_query ;;
          let '(h,a,e,z) := t in
          e ← RO_query (prod_assoc (h, a)) ;;
          ret (otf (Verify h a e z))
        } ;
        def #[ RUN ] (hw: chRelation) : chTranscript
        {
          #import {sig #[ INIT ] : 'unit → 'unit} as RO_init ;;
          #import {sig #[ QUERY ] : 'query → 'random} as RO_query ;;
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          '(a,st) ← Commit h w ;;
          RO_init Datatypes.tt ;;
          e ← RO_query (prod_assoc (h, a)) ;;
          z ← Response h w st a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition RUN_interactive :
      package Sigma_locs
        [interface]
        [interface
          val #[ VERIFY ] : chTranscript → 'bool ;
          val #[ RUN ] : chRelation → chTranscript]
      :=
      [package
        def #[ VERIFY ] (t: chTranscript) : 'bool
        {
          let '(h,a,e,z) := t in ret (otf (Verify h a e z))
        } ;
        def #[ RUN ] (hw: chRelation) : chTranscript
        {
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          '(a,st) ← Commit h w ;;
          e ← sample uniform i_random ;;
          z ← Response h w st a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition SHVZK_real_aux :
      package Sigma_locs
        [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
        [interface val #[ RUN ] : chRelation → chTranscript]
      :=
      [package
        def #[ RUN ] (hw: chRelation) : chTranscript
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript} as SHVZK ;;
          e ← sample uniform i_random ;;
          t ← SHVZK (hw, e) ;;
          ret t
        }
      ].

    Lemma run_interactive_shvzk :
      ∀ LA A,
        ValidPackage LA [interface
          val #[ RUN ] : chRelation → chTranscript
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
        - apply SHVZK_real_aux.
        - apply SHVZK_real.
      }
      1: eapply valid_package_inject_export.
      2: apply RUN_interactive.
      { apply fsubset_ext=> x xin.
        rewrite fset_cons.
        apply /fsetUP.
        right. apply xin. }
      simplify_eq_rel hw.
      ssprove_code_simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_code_simpl_more.
      ssprove_swap_rhs 0%N.
      ssprove_sync_eq=> rel.
      ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      1: eapply rsamplerC.
      apply rsame_head=> m.
      destruct m as [a st].
      ssprove_sync_eq=> e.
      apply rsame_head=> z.
      apply r_ret=> s0 s1 ->.
      split; reflexivity.
    Qed.

    Hint Extern 50 (_ = code_link _ _) =>
      rewrite code_link_scheme
      : ssprove_code_simpl.

    Theorem fiat_shamir_correct :
      ∀ LA A ,
        ValidPackage LA [interface
          val #[ RUN ] : chRelation → chTranscript
        ] A_export A →
        fdisjoint LA (Sigma_locs :|: RO_locs) →
        fdisjoint Sigma_locs RO_locs →
        AdvantageE (Fiat_Shamir ∘ RO) RUN_interactive A = 0.
    Proof.
      intros LA A Va Hdisj Hdisj_oracle.
      eapply eq_rel_perf_ind_ignore.
      6: apply Hdisj.
      6:{
        rewrite fdisjointUr in Hdisj.
        case (fdisjoint LA Sigma_locs) eqn:eq.
        2: discriminate.
        apply eq.
      }
      5: apply Va.
      1: ssprove_valid; [idtac | apply fsubsetUl |apply fsubsetUr].
      1:{ eapply valid_package_inject_export.
           2: apply Fiat_Shamir.
           apply fsubset_ext=> x xin.
           rewrite fset_cons.
           apply /fsetUP.
           right. apply xin. }
      1:{ eapply valid_package_inject_export.
           2: apply RUN_interactive.
           apply fsubset_ext=> x xin.
           rewrite fset_cons.
           apply /fsetUP.
           right. apply xin. }
      1:{ apply fsubsetU.
           by erewrite fsubsetUr. }
      simplify_eq_rel hw.
      ssprove_code_simpl.
      destruct hw as [h w].
      ssprove_sync=> rel.
      eapply rsame_head_alt.
      1: exact _.
      1:{
        intros l Il.
        apply get_pre_cond_heap_ignore.
        move: l Il.
        apply /fdisjointP.
        assumption.
      }
      1:{ intros. apply put_pre_cond_heap_ignore. }
      intros m.
      destruct m as [a st].
      ssprove_contract_put_get_lhs.
      rewrite emptymE.
      apply r_put_lhs.
      ssprove_sync => e.
      apply r_put_lhs.
      ssprove_restore_pre.
      1: ssprove_invariant.
      eapply r_reflexivity_alt.
      - exact _.
      - intros l Il.
        ssprove_invariant.
        move: l Il.
        apply /fdisjointP. assumption.
      - intros. ssprove_invariant.
    Qed.

    (* GOAL: reason about ZK property *)

  End FiatShamir.

End SigmaProtocol.
