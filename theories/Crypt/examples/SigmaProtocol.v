
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

  Definition choiceWitness := 'fin #|Witness|.
  Definition choiceStatement := 'fin #|Statement|.
  Definition choiceMessage := 'fin #|Message|.
  Definition choiceChallenge := 'fin #|Challenge|.
  Definition choiceResponse := 'fin #|Response|.
  Definition choiceTranscript :=
    chProd (chProd (chProd choiceStatement choiceMessage) choiceChallenge) choiceResponse.
  Definition choiceBool := 'fin #|bool_choiceType|.

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
      def #[ TRANSCRIPT ] (hwe : chInput) : chTranscript
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
      [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
    :=
    [package
      def #[ TRANSCRIPT ] (hwe : chInput) : chTranscript
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

    Definition Com_locs : {fset Location} :=
      fset [:: challenge_loc ; response_loc].

    Definition choiceOpen := (chProd choiceChallenge choiceResponse).
    Notation " 'chOpen' " := choiceOpen (in custom pack_type at level 2).

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

    (* Lemma test n m k I: (is_true *)
    (*                        ((n + m) *)
    (*                           \notin [seq (let '(i, _) := x in i) *)
    (*                                     | x <- [:: (n + k , I)]])). *)

    (* Lemma test n m k : *)
    (*   m <> k → *)
    (*   (is_true ((n + m)%N \notin [:: (n + k)%N])). *)
    (* Proof. *)
    (*   intros h. *)
    (*   unfold "\notin", "\in". *)
    (*   simpl. *)
    (*   apply /orP. *)
    (*   unfold not. *)
    (*   intros contra. *)
    (*   destruct contra=>//. *)
    (*   rewrite eqn_add2l in H. *)
    (*   apply h. apply /eqP. *)
    (*   assumption. *)
    (* Qed. *)

    (* #[local] Hint Extern 20 (is_true *)
    (*                            (?I1 \notin [seq (let '(i, _) := x in i) *)
    (*                                        | x <- [:: (?I2, ?E)]])) => *)
    (*   unfold I1, I2 ; simpl ; apply test ; auto *)
    (*   : typeclass_instances ssprove_valid_db. *)


    (* Hint Extern 20 (is_true ((?n+?m)%N \notin [:: (?n + ?k)])) => *)
    (*   apply test ; auto *)
    (*   : typeclass_instances ssprove_valid_db. *)

    (* Lemma notin_cons : *)
    (*   ∀ (T : eqType) (y : T) (s : seq T) (x : T), *)
    (*     (x \notin y :: s) = (x != y) && (x \notin s). *)
    (* Proof. *)
    (*   intros T y s x. *)
    (*   rewrite in_cons. *)
    (*   rewrite Bool.negb_orb. reflexivity. *)
    (* Qed. *)

    (* Lemma add_neq (m n k : nat): *)
    (*   n <> k -> *)
    (*   (m + n)%N != (m + k)%N. *)
    (* Proof. *)
    (*   intros h. *)
    (*   rewrite eqn_add2l. *)
    (*   apply /negP. *)
    (*   unfold not. *)
    (*   intros contra. *)
    (*   apply h. *)
    (*   apply /eqP. *)
    (*   assumption. *)
    (* Qed. *)

    (* Hint Extern 20 (is_true (?m + ?n)%N != (?m + ?k)%N) => *)
    (*   simpl ; try apply add_neq ; auto *)
    (*   : typeclass_instances ssprove_valid_db. *)

    (* Lemma test2 (m n : nat): *)
    (*   m != n → *)
    (*   (is_true (m \notin [:: n])). *)
    (* Proof. *)
    (*   unfold "\notin", "\in". *)
    (*   intros h. *)
    (*   apply /orP. *)
    (*   intros contra. *)
    (*   destruct contra=>//. *)
    (*   rewrite H in h. *)
    (*   rewrite boolp.falseE in h. *)
    (*   apply h. *)
    (* Qed. *)

    (* Lemma test3 (m n k : nat): *)
    (*   n <> k → *)
    (*   (m + n)%N <> (m + k)%N. *)
    (* Proof. *)
    (*   intros. *)
    (*   intros contra. *)
    (*   apply H. *)
    (* Admitted. *)

    (* Ltac imports_disjoint_auto := *)
    (*   match goal with *)
    (*     | [ |- is_true ((?m + ?n)%N <> (?m + ?n)%N) ] => apply test3 *)
    (*     | [ |- is_true ((?m + ?n)%N != (?m + ?n)%N) ] => apply add_neq ; auto *)
    (*     | [ |- is_true (?m != ?n) ] => unfold m ; unfold n *)
    (*   end. *)

    (* Hint Extern 20 (is_true ((?m + ?n)%N != (?m + ?k))) => *)
    (*   simpl ; try apply test3 *)
    (*   : typeclass_instances ssprove_valid_db. *)

    (* Hint Extern 20 (is_true (?m != ?n)) => *)
    (*   imports_disjoint_auto *)
    (*   : typeclass_instances ssprove_valid_db. *)

    (* Hint Extern 20 (is_true (?m \notin [:: ?n])) => *)
    (*   simpl ; try apply test2 ; auto *)
    (*   : typeclass_instances ssprove_valid_db. *)

    (* Hint Extern 20 (is_true (?A \notin [seq (let '(i, _) := x in i) *)
    (*                                    | x <- ?xs])) => *)
    (*   simpl ; rewrite in_cons ; rewrite Bool.negb_orb ; apply /andP ; split ; auto ; simpl *)
    (*   : typeclass_instances ssprove_valid_db. *)

    Definition Sigma_to_Com:
      package Com_locs
        [interface val #[ TRANSCRIPT ] : chInput → chTranscript]
        [interface
          val #[ COM ] : chInput → chMessage ;
          val #[ OPEN ] : 'unit → chOpen ;
          val #[ VER ] : chTranscript → 'bool
        ]
      :=
      [package
        def #[ COM ] (hwe : chInput) : chMessage
        {
          #import {sig #[ TRANSCRIPT ] : chInput → chTranscript } as run ;;
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
          let '(h,a,e,z) := t in
          ret (otf (Verify h a e z))
        }
      ].

    (* Commitment to input value*)
    Definition Hiding_real :
      package fset0
        [interface
          val #[ COM ] : chInput → chMessage ;
          val #[ OPEN ] : 'unit → chOpen ;
          val #[ VER ] : chTranscript → 'bool
        ]
        [interface val #[ HIDING ] : chInput → chMessage ]
      :=
      [package
        def #[ HIDING ] (hwe : chInput) : chMessage
        {
          #import {sig #[ COM ] : chInput → chMessage } as com ;;
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
          val #[ VER ] : chTranscript → 'bool
        ]
        [interface val #[ HIDING ] : chInput → chMessage]
      :=
      [package
        def #[ HIDING ] (hwe : chInput) : chMessage
        {
          #import {sig #[ COM ] : chInput → chMessage } as com ;;
          let '(h,w,_) := hwe in
          e ← sample uniform i_challenge ;;
          t ← com (h,w,e) ;;
          ret t
        }
      ].

    Definition ɛ_hiding A :=
      AdvantageE
        (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_real)
        (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_real) A.


    Theorem commitment_hiding :
      ∀ LA A eps,
        ValidPackage LA [interface
          val #[ HIDING ] : chInput → chMessage
        ] A_export A →
        (∀ B,
          ValidPackage (LA :|: Com_locs) [interface
            val #[ TRANSCRIPT ] : chInput → chTranscript
          ] A_export B →
          ɛ_SHVZK B <= eps
        ) →
        AdvantageE
          (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal)
          (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A
        <=
        (ɛ_hiding A) + eps + eps.
    Proof.
      unfold ɛ_hiding, ɛ_SHVZK.
      intros LA A eps Va Hadv.
      ssprove triangle (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) [::
        (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_real) ;
        (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_real)
      ] (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A
      as ineq.
      eapply le_trans. 1: exact ineq.
      clear ineq.
      rewrite <- !Advantage_link.
      eapply ler_add.
      - rewrite GRing.addrC. eapply ler_add. 1: apply lexx.
        specialize (Hadv (A ∘ Hiding_real ∘ Sigma_to_Com)).
        rewrite <- link_assoc. rewrite Advantage_sym.
        apply Hadv. ssprove_valid.
        + apply fsub0set.
        + apply fsubsetxx.
        + apply fsubsetUl.
        + apply fsubsetUr.
      - specialize (Hadv (A ∘ Hiding_ideal ∘ Sigma_to_Com)).
        rewrite <- link_assoc.
        apply Hadv. ssprove_valid.
        + apply fsub0set.
        + apply fsubsetxx.
        + apply fsubsetUl.
        + apply fsubsetUr.
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

    Theorem commitment_binding :
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
      eapply le_trans. 1: exact ineq.
      clear ineq.
      rewrite ger_addr.
      apply eq_ler.
      eapply eq_rel_perf_ind_eq.
      4: apply VA.
      1:{
        eapply valid_link. 2: apply VAdv.
        ssprove_valid.
      }
      1:{
        eapply valid_link. 2: apply VAdv.
        ssprove_valid.
      }
      2,3: assumption.
      simplify_eq_rel h.

      destruct (Adv ADV) as [[? []]|].
      2:{ apply r_ret. intuition auto. }

      repeat destruct chUniverse_eqP.
      2:{ apply r_ret. intuition auto. }
      2:{ apply r_ret. intuition auto. }

      ssprove_code_simpl.
      apply rsame_head. intros [? [[] []]].
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

    (* TW: I moved it here because it might induce back-tracking and we want to *)
  (*     avoid it because of time-consumption. *)
  (*   *)
    Hint Extern 20 (ValidCode ?L ?I ?c.(prog)) =>
      eapply valid_injectMap ; [| eapply c.(prog_valid) ]
      : typeclass_instances ssprove_valid_db.

    Definition Fiat_Shamir :
      package Sigma_locs
        [interface
          val #[ QUERY ] : 'query → 'random
        ]
        [interface
          val #[ VERIFY ] : chTranscript → 'bool ;
          val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package
        def #[ VERIFY ] (t : chTranscript) : 'bool
        {
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,a,e,z) := t in
          e ← RO_query (prod_assoc (h, a)) ;;
          ret (otf (Verify h a e z))
        } ;
        def #[ RUN ] (hw : chRelation) : chTranscript
        {
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          a ← Commit h w ;;
          e ← RO_query (prod_assoc (h, a)) ;;
          z ← Response h w a e ;;
          @ret choiceTranscript (h,a,e,z)
        }
      ].

    Definition Fiat_Shamir_SIM :
      package Sim_locs
        [interface
          val #[ QUERY ] : 'query → 'random
        ]
        [interface
          val #[ VERIFY ] : chTranscript → 'bool ;
          val #[ RUN ] : chRelation → chTranscript
        ]
      :=
      [package
        def #[ VERIFY ] (t : chTranscript) : 'bool
        {
          #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
          let '(h,a,e,z) := t in
          e ← RO_query (prod_assoc (h, a)) ;;
          ret (otf (Verify h a e z))
        } ;
        def #[ RUN ] (hw : chRelation) : chTranscript
        {
          let '(h,w) := hw in
          #assert (R (otf h) (otf w)) ;;
          t ← Sim h ;;
          ret t
        }
      ].

    Definition ϵ_fiat_shamir_zk A :=
      AdvantageE (Fiat_Shamir ∘ Oracle.RO) (Fiat_Shamir_SIM ∘ Oracle.RO) A.

  End FiatShamir.

End SigmaProtocol.
