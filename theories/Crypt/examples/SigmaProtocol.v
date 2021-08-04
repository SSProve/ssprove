
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

Local Open Scope ring_scope.

Module Type SigmaProtocolParams.

  Parameter Witness Statement Message Challenge Response State : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.
  Parameter R : Statement -> Witness -> bool.

End SigmaProtocolParams.

Module Type SigmaProtocolAlgorithms (π : SigmaProtocolParams).

  Import π.

  Local Open Scope package_scope.

  Parameter Statement_pos : Positive #|Statement|.
  Parameter Witness_pos : Positive #|Witness|.
  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.
  Parameter Response_pos : Positive #|Response|.
  Parameter State_pos : Positive #|State|.
  Parameter Bool_pos : Positive #|bool_choiceType|.

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
  Definition choiceTranscript := chProd (chProd choiceMessage choiceChallenge) choiceResponse.
  Definition choiceState := 'fin #|State|.
  Definition choiceBool := 'fin #|bool_choiceType|.

  Parameter Sigma_locs : {fset Location}.
  Parameter Simulator_locs : {fset Location}.

  Parameter Commit :
    ∀ (h : choiceStatement) (w : choiceWitness),
      code Sigma_locs [interface] (choiceMessage × choiceState).

  Parameter Response :
    ∀ (h : choiceStatement) (w : choiceWitness) (s : choiceState) (a : choiceMessage) (e : choiceChallenge),
      code Sigma_locs [interface] choiceResponse.

  Parameter Verify :
    ∀ (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge) (z : choiceResponse), choiceBool.

  Parameter Simulate :
    ∀ (h : choiceStatement) (e : choiceChallenge),
      code Simulator_locs [interface] choiceTranscript.

  Parameter Extractor :
    ∀ (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (e' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse), 'option choiceWitness.

End SigmaProtocolAlgorithms.

Module SigmaProtocol (π : SigmaProtocolParams)
                     (Alg : SigmaProtocolAlgorithms π).

  Import π.
  Import Alg.

  Notation " 'chStatement' " := choiceStatement (in custom pack_type at level 2).
  Notation " 'chRelation' " := (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).
  Notation " 'chInput' " := (chProd (chProd choiceStatement choiceWitness) choiceChallenge) (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chTranscript' " := choiceTranscript (in custom pack_type at level 2).
  Definition Opening := chProd choiceChallenge choiceResponse.
  Notation " 'chSoundness' " := (chProd choiceMessage (chProd Opening Opening))
                                  (in custom pack_type at level 2).




  Definition i_challenge := #|Challenge|.
  Definition TRANSCRIPT : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.
  Definition ADV : nat := 3.
  Definition SOUNDNESS : nat := 4.

  Definition i_challenge_pos : Positive i_challenge.
  Proof. unfold i_challenge. apply Challenge_pos. Qed.
  #[local] Existing Instance i_challenge_pos.

  Local Open Scope package_scope.

  Definition SHVZK_real:
    package Sigma_locs
      [interface]
      [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript] :=
    [package
     def #[ TRANSCRIPT ] (hwe: chInput) : 'option chTranscript
      {
        let '(h,w,e) := hwe in
        if (R (otf h) (otf w)) then
          m ← Commit h w ;;
          let '(a, s) := m in
          z ← Response h w s a e ;;
          ret (Some (a,e,z))
        else ret None
      }
    ].
  
  Definition SHVZK_ideal:
    package Simulator_locs
      [interface]
      [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript] :=
    [package
     def #[ TRANSCRIPT ] (hwe: chInput) : 'option chTranscript
      {
        let '(h, w, e) := hwe in
        if (R (otf h) (otf w)) then
          t ← Simulate h e ;;
          ret (Some t)
        else ret None
      }
    ].

  (* Main security game for Special Honest-Verifier Zero-Knowledge. *)
  Definition SHVZK:
    loc_GamePair [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript] :=
    fun b => if b then {locpackage SHVZK_ideal} else {locpackage SHVZK_real }.

  Definition Special_Soundness_f:
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chSoundness]
      [interface val #[ SOUNDNESS ] : chStatement → 'bool] :=
    [package
     def #[ SOUNDNESS ] (h : chStatement) : 'bool
      {
        #import {sig #[ ADV ] : chStatement → chSoundness} as A ;;
        '(a, tmp) ← A(h) ;;
        let '(c1, c2) := tmp in
        let '(e, z) := c1 in
        let '(e', z') := c2 in
        let v1 := Verify h a e z in
        let v2 := Verify h a e' z' in
        if (andb (e != e') (andb (otf v1) (otf v2))) then
            match Extractor h a e e' z z' with
            | Some w => ret (R (otf h) (otf w))
            | None => ret false
            end
        else ret false
      }
    ].

  Definition Special_Soundness_t:
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chSoundness]
      [interface val #[ SOUNDNESS ] : chStatement → 'bool] :=
    [package
     def #[ SOUNDNESS ] (h : chStatement) : 'bool
      {
        #import {sig #[ ADV ] : chStatement → chSoundness} as A ;;
        '(a, tmp) ← A(h) ;;
        let '(c1, c2) := tmp in
        let '(e, z) := c1 in
        let '(e', z') := c2 in
        let v1 := Verify h a e z in
        let v2 := Verify h a e' z' in
        if (andb (e != e') (andb (otf v1) (otf v2))) then
            ret true
        else ret false
      }
    ].

  (* Main security statement for 2-special soundness. *)
  Definition ɛ_soundness A Adv := AdvantageE (Special_Soundness_t ∘ Adv) (Special_Soundness_f ∘ Adv) A.


  (**************************************)
  (* Start of Commitment Scheme Section *)
  (**************************************)
  Section Commitments.

    Definition HIDING : nat := 5.

    Notation " 'chOpen' " := (chProd choiceStatement 'option choiceTranscript) (in custom pack_type at level 2).

    Definition Sigma_to_Com:
      package Sigma_locs
        [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript]
        [interface val #[ COM ] : chInput → 'option chTranscript ;
                   val #[ VER ] : chOpen → 'bool] :=
      [package
      def #[ COM ] (hwe : chInput) : 'option chTranscript
      {
        #import {sig #[ TRANSCRIPT ] : chInput → 'option chTranscript} as run ;;
        t ← run hwe ;;
        ret t
      }
      ;
      def #[ VER ] (open : chOpen) : 'bool
      {
        match open with
          | (h, Some (a,e,z)) => ret (otf (Verify h a e z))
          | _ => ret false
        end
      }
      ].

    (* Commitment to input value*)
    Definition Hiding_real :
      package Sigma_locs
        [interface val #[ COM ] : chInput → 'option chTranscript ;
                  val #[ VER ] : chOpen → 'bool]
        [interface val #[ HIDING ] : chInput → 'option chMessage] :=
      [package
      def #[ HIDING ] (hwe : chInput) : 'option chMessage
      {
        #import {sig #[ COM ] : chInput → 'option chTranscript} as com ;;
        _ ← sample uniform i_challenge ;;
        t ← com hwe ;;
        match t with
          | Some (a,e,z) => ret (Some a)
          | _ => ret None
        end
      }
      ].

    (* Commitment to random value *)
    Definition Hiding_ideal :
      package Sigma_locs
        [interface val #[ COM ] : chInput → 'option chTranscript ;
                  val #[ VER ] : chOpen → 'bool]
        [interface val #[ HIDING ] : chInput → 'option chMessage] :=
      [package
      def #[ HIDING ] (hwe : chInput) : 'option chMessage
      {
        #import {sig #[ COM ] : chInput → 'option chTranscript} as com ;;
        let '(h,w,_) := hwe in
        e ← sample uniform i_challenge ;;
        t ← com (h,w,e) ;;
        match t with
          | Some (a,e,z) => ret (Some a)
          | _ => ret None
        end
      }
      ].

    Definition ɛ_hiding A :=
      AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false) A.


    Theorem commitment_hiding :
      ∀ LA A eps,
        ValidPackage LA [interface val #[ HIDING ] : chInput → 'option chMessage] A_export A →
        (∀ A',
          ValidPackage (fsetU LA Sigma_locs) [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript] A_export A' →
          Advantage SHVZK A' <= eps) →
        AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A <= (ɛ_hiding A) + eps + eps.
    Proof.
      intros LA A eps Va Hadv.
      ssprove triangle (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) [::
              (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) ;
              (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false)
            ] (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A
        as ineq.
      apply: ler_trans. 1: exact ineq.
      clear ineq.
      unfold ɛ_hiding.
      rewrite -!Advantage_link.
      eapply ler_add.
      1: rewrite GRing.addrC; eapply ler_add.
      1: apply lerr.
      - have := Hadv (A ∘ Hiding_real ∘ Sigma_to_Com).
        assert (ValidPackage (fsetU LA Sigma_locs) [interface val #[TRANSCRIPT] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_real ∘ Sigma_to_Com)).
        + rewrite link_assoc.
          have -> : LA :|: Sigma_locs = LA :|: Sigma_locs :|: Sigma_locs.
          { rewrite - fsetUA fsetUid. reflexivity. }
          eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript ;
                                            val #[ VER ] : chOpen → 'bool].
          2 : { apply valid_package_from_class; apply Sigma_to_Com. }
          eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
          ++ assumption.
          ++ apply Hiding_real.
        + move=> Hadv'.
          apply Hadv' in H.
          rewrite Advantage_sym -link_assoc.
          assumption.
      - have := Hadv (A ∘ Hiding_ideal ∘ Sigma_to_Com).
        assert (ValidPackage (fsetU LA Sigma_locs) [interface val #[TRANSCRIPT] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_ideal ∘ Sigma_to_Com)).
        + rewrite link_assoc.
          have -> : LA :|: Sigma_locs = LA :|: Sigma_locs :|: Sigma_locs.
          { rewrite - fsetUA fsetUid. reflexivity. }
          eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript ;
                                            val #[ VER ] : chOpen → 'bool].
          2 : { apply valid_package_from_class; apply Sigma_to_Com. }
          eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
          ++ assumption.
          ++ apply Hiding_ideal.
        + move=> Hadv'.
          apply Hadv' in H.
          rewrite -link_assoc.
          assumption.
    Qed.

    Definition Com_Binding:
      package Sigma_locs
        [interface val #[ ADV ] : chStatement → chSoundness]
        [interface val #[ SOUNDNESS ] : chStatement → 'bool] :=
      [package
      def #[ SOUNDNESS ] (h : chStatement) : 'bool
        {
          #import {sig #[ ADV ] : chStatement → chSoundness} as A ;;
          '(a, tmp) ← A h ;;
          let '(c1, c2) := tmp in
          let '(e, z) := c1 in
          let '(e', z') := c2 in
          let v1 := Verify h a e z in
          let v2 := Verify h a e' z' in
          ret (andb (e != e') (andb (otf v1) (otf v2)))
        }
      ].

    Lemma commitment_binding:
      ∀ LA A LAdv Adv,
        ValidPackage LA [interface val #[ SOUNDNESS ] : chStatement → 'bool] A_export A →
        ValidPackage LAdv [interface] [interface val #[ ADV ] : chStatement → chSoundness] Adv →
        fdisjoint LA (Sigma_locs :|: LAdv) →
        AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <= (ɛ_soundness A Adv).
      intros LA A LAdv Adv VA VAdv Hdisj.
      ssprove triangle (Com_Binding ∘ Adv) [::
              (Special_Soundness_t ∘ Adv)
            ] (Special_Soundness_f ∘ Adv) A as ineq.
      apply: ler_trans. 1: exact ineq.
      rewrite ger_addr.

      assert (AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_t ∘ Adv) A = 0) as ɛ_Adv.
      2: rewrite ɛ_Adv; apply lerr.

      eapply eq_rel_perf_ind_eq.
      4: apply VA.
      1,2: eapply valid_link; last first; [apply VAdv | trivial].
      1: apply Com_Binding.
      1: apply Special_Soundness_t.
      2,3: assumption.
      simplify_eq_rel h.

      destruct (Adv ADV).
      2: { apply r_ret => ?? ->. split; reflexivity. }

      destruct t, s.
      repeat destruct chUniverse_eqP.
      2,3:  apply r_ret=> ?? ->; split; reflexivity.
      apply rsame_head=> run.
      destruct run.
      destruct s0.
      destruct s0, s1.

      match goal with
          | [ |- context[if ?b then _ else _]] => case b eqn:rel
      end.
      all: apply r_ret; auto.
    Qed.

  End Commitments.

  (* This section aim to prove an automatic conversation between the sampling of the random challenge and a random oracle. *)
  (* The main difference is that the random oracle is a query parametrized by the context of the execution. *)
  Import RandomOracle.
  Module OracleParams <: ROParams.
    Definition Query := (prod_finType Statement Message).
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
    Notation " 'chNI' " := (chProd choiceMessage choiceResponse) (in custom pack_type at level 2).
    Notation " 'chNIRel' " := (chProd choiceStatement (chProd choiceMessage choiceResponse)) (in custom pack_type at level 2).


    Definition prod_assoc : (chProd choiceStatement choiceMessage) -> chQuery.
    Proof.
      cbn.
      apply prod_curry.
      intros statement message.
      rewrite !card_prod.
      repeat apply mxvec_index; assumption.
    Qed.


    Definition VERIFY_non_interactive:
      package Sigma_locs
        [interface val #[ INIT ] : 'unit → 'unit ;
                   val #[ QUERY ] : 'query → 'random]
        [interface val #[ RUN ] : chNIRel → 'bool] :=
      [package
         def #[ RUN ] (ht: chNIRel) : 'bool
         {
           #import {sig #[ INIT ] : 'unit → 'unit} as RO_init ;;
           #import {sig #[ QUERY ] : 'query → 'random} as RO_query ;;
           let '(h,t) := ht in
           let '(a,z) := t in
           RO_init Datatypes.tt ;;
           e ← RO_query (prod_assoc (h, a)) ;;
           ret (otf (Verify h a e z))
         }
      ].

    Definition RUN_non_interactive:
      package Sigma_locs
        [interface val #[ INIT ] : 'unit → 'unit ;
                   val #[ QUERY ] : 'query → 'random]
        [interface val #[ RUN ] : chRelation → 'option chTranscript] :=
      [package
         def #[ RUN ] (hw: chRelation) : 'option chTranscript
         {
           #import {sig #[ INIT ] : 'unit → 'unit} as RO_init ;;
           #import {sig #[ QUERY ] : 'query → 'random} as RO_query ;;
           let '(h,w) := hw in
           if (R (otf h) (otf w))
             then '(m,st) ← Commit h w ;;
                  RO_init Datatypes.tt ;;
                  e ← RO_query (prod_assoc (h, m)) ;;
                  z ← Response h w st m e ;;
                  ret (Some (m,e,z))
             else ret None
         }
      ].

    Definition RUN_interactive:
      package Sigma_locs
        [interface]
        [interface val #[ RUN ] : chRelation → 'option chTranscript] :=
      [package
         def #[ RUN ] (hw: chRelation) : 'option chTranscript
         {
           let '(h,w) := hw in
           if (R (otf h) (otf w))
             then '(m,st) ← Commit h w ;;
                  e ← sample uniform i_random ;;
                  z ← Response h w st m e ;;
                  ret (Some (m,e,z))
             else ret None
         }
      ].

    Definition SHVZK_real_aux:
      package Sigma_locs
        [interface val #[ TRANSCRIPT ] : chInput → 'option chTranscript]
        [interface val #[ RUN ] : chRelation → 'option chTranscript] :=
      [package
         def #[ RUN ] (hw: chRelation) : 'option chTranscript
         {
           #import {sig #[ TRANSCRIPT ] : chInput → 'option chTranscript} as SHVZK ;;
           e ← sample uniform i_random ;;
           t ← SHVZK (hw, e) ;;
           ret t
         }
      ].

    Lemma run_interactive_shvzk:
      ∀ LA A,
        ValidPackage LA [interface val #[ RUN ] : chRelation → 'option chTranscript] A_export A →
        fdisjoint LA Sigma_locs →
      AdvantageE RUN_interactive (SHVZK_real_aux ∘ SHVZK_real) A = 0.
    Proof.
      intros LA A Va Hdisj.
      eapply eq_rel_perf_ind_eq.
      5,6: apply Hdisj.
      4: apply Va.
      2: { rewrite <-  fsetUid.
           eapply valid_link.
           - apply SHVZK_real_aux.
           - apply SHVZK_real. }
      1: apply RUN_interactive.
      simplify_eq_rel hw.
      ssprove_code_simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl.
      destruct hw as [h w].
      case (R (otf h) (otf w)).
      - simpl.
        ssprove_swap_rhs 0%N.
        1: apply rsamplerC.
        apply rsame_head=> m.
        destruct m as [a st].
        ssprove_sync_eq=> e.
        apply rsame_head=> z.
        apply r_ret=> s0 s1 ->.
        split; reflexivity.
      - simpl.
        apply r_dead_sample_R.
        1: apply LosslessOp_uniform.
        apply r_ret=> s0 s1 ->.
        split; reflexivity.
    Qed.

    Hint Extern 50 (_ = code_link _ _) =>
      rewrite code_link_scheme
      : ssprove_code_simpl.

    Theorem fiat_shamir_correct:
      ∀ LA A ,
        ValidPackage LA [interface val #[ RUN ] : chRelation → 'option chTranscript] A_export A →
        fdisjoint LA (Sigma_locs :|: RO_locs) →
        fdisjoint Sigma_locs RO_locs →
      AdvantageE (RUN_non_interactive ∘ RO) RUN_interactive A = 0.
    Proof.
      intros LA A Va Hdisj Hdisj_oracle.
      eapply eq_rel_perf_ind_ignore.
      6: apply Hdisj.
      6: { rewrite fdisjointUr in Hdisj.
           case (fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) LA Sigma_locs) eqn:eq.
           2: discriminate.
           apply eq. }
      5: apply Va.
      1: { eapply valid_link.
           - apply RUN_non_interactive.
           - apply RO. }
      1: apply RUN_interactive.
      1: { apply fsubsetU.
           by erewrite fsubsetUr. }
      simplify_eq_rel hw.
      ssprove_code_simpl.
      destruct hw as [h w].
      case (R (otf h) (otf w)); simpl.
      2: apply r_ret; intros ???; split; [done | assumption].
      ssprove_code_simpl.
      eapply rsame_head_alt.
      1: apply Commit.
      { intros locs Iloc.
        apply get_pre_cond_heap_ignore.
        move: locs Iloc.
        apply /fdisjointP.
        assumption. }
      { intros; apply put_pre_cond_heap_ignore. }
      intros m.
      destruct m as [a st].
      ssprove_contract_put_get_lhs.
      rewrite emptymE.
      apply r_put_lhs.
      ssprove_sync=>e.
      apply r_put_lhs.
      ssprove_restore_pre.
      { ssprove_invariant. }
      eapply r_reflexivity_alt.
      - exact _.
      - intros l Il.
        ssprove_invariant.
        move: l Il.
        apply /fdisjointP; assumption.
      - intros. ssprove_invariant.
    Qed.

    (* GOAL: reason about ZK property *)

  End FiatShamir.

End SigmaProtocol.
