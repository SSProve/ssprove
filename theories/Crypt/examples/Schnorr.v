
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_code pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

Module Type GroupParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].

End GroupParam.

Module Schnorr (GP : GroupParam).

Import GP.

(* order of g *)
Definition q : nat := #[g].

Module MyParam <: SigmaProtocolParams.

  Definition Witness : finType := [finType of 'Z_q].
  Definition Statement : finType := FinGroup.arg_finType gT.
  Definition Message : finType := FinGroup.arg_finType gT.
  Definition Challenge : finType := [finType of 'Z_q].
  Definition Response : finType :=  [finType of 'Z_q].
  Definition Transcript :=
    prod_finType (prod_finType Message Challenge) Response.

  Definition w0 : Witness := 0.
  Definition e0 : Challenge := 0.
  Definition z0 : Response := 0.

  Definition R : Statement -> Witness -> bool :=
    (λ (h : Statement) (w : Witness), h == (g ^+ w)).

  #[export] Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  #[export] Instance Witness_pos : Positive #|Witness|.
  Proof.
    apply /card_gt0P. exists w0. auto.
  Qed.

  Definition Statement_pos : Positive #|Statement| := _.
  Definition Message_pos : Positive #|Message| := _.
  Definition Challenge_pos : Positive #|Challenge| := _.
  Definition Response_pos : Positive #|Response| := _.
  Definition Bool_pos : Positive #|bool_choiceType|.
  Proof.
    rewrite card_bool. done.
  Defined.

End MyParam.

Module MyAlg <: SigmaProtocolAlgorithms MyParam.

  Import MyParam.

  #[local] Existing Instance Bool_pos.

  Definition choiceWitness : choice_code := 'fin #|Witness|.
  Definition choiceStatement : choice_code := 'fin #|Statement|.
  Definition choiceMessage : choice_code := 'fin #|Message|.
  Definition choiceChallenge : choice_code := 'fin #|Challenge|.
  Definition choiceResponse : choice_code := 'fin #|Response|.
  Definition choiceTranscript : choice_code :=
    chProd
      (chProd (chProd choiceStatement choiceMessage) choiceChallenge)
      choiceResponse.
  Definition choiceBool := 'fin #|bool_choiceType|.

  Definition i_witness := #|Witness|.

  Definition HIDING : nat := 0.
  Definition SOUNDNESS : nat := 1.

  Definition commit_loc : Location := (choiceWitness; 2%N).

  Definition Sigma_locs : {fset Location} := fset [:: commit_loc].
  Definition Simulator_locs : {fset Location} := fset0.

  Definition Commit (h : choiceStatement) (w : choiceWitness):
    code Sigma_locs [interface] choiceMessage :=
    {code
      r ← sample uniform i_witness ;;
      #put commit_loc := r ;;
      ret (fto (g ^+ (otf r)))
    }.

  Definition Response (h : choiceStatement) (w : choiceWitness) (a : choiceMessage) (e : choiceChallenge) :
    code Sigma_locs [interface] choiceResponse :=
    {code
      r ← get commit_loc ;;
      ret (fto (otf r + otf e * otf w))
    }.

  Definition Simulate (h : choiceStatement) (e : choiceChallenge) :
    code Simulator_locs [interface] choiceTranscript :=
    {code
      z ← sample uniform i_witness ;;
      ret (h, fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z)
    }.

  Definition Verify (h : choiceStatement) (a : choiceMessage)
    (e : choiceChallenge) (z : choiceResponse) : choiceBool :=
    fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e)).

  Definition Extractor (h : choiceStatement) (a : choiceMessage)
    (e : choiceChallenge) (e' : choiceChallenge)
    (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
    Some (fto ((otf z - otf z') / (otf e - otf e'))).

End MyAlg.


#[local] Open Scope package_scope.

Module Sigma := SigmaProtocol MyParam MyAlg.

Import MyParam MyAlg Sigma.

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

Lemma group_prodC :
  ∀ (x y : gT), x * y = y * x.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT.
  }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT.
  }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.

Lemma group_prodA :
  ∀ (x y z : gT), x * (y * z) = (x * y) * z.
Proof.
  move => x y z.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT.
  }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT.
  }
  have Hz: exists iz, z = g^+iz.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT.
  }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].

  subst.
  repeat rewrite -expgD addnC addnA.
  rewrite mulgA.
  reflexivity.
Qed.

#[local] Definition f (e w : Witness) :
  Arit (uniform i_witness) → Arit (uniform i_witness) :=
  λ z, fto (otf z + e * w).

Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
Proof.
  apply Zp_cast, prime_gt1, prime_order.
Qed.

Lemma bij_f w e : bijective (f w e).
Proof.
  unfold f.
  exists (λ x, fto (otf x - w * e)).
  all: intro x ; unfold fto, otf ; rewrite !enum_rankK.
  - by rewrite addrK enum_valK.
  - by rewrite subrK enum_valK.
Qed.


(* Main theorem. *)
(* Proves that Schnorr is a ∑-protocol with perfect special honest-verifier
  zero-knowledge *)
Theorem schnorr_SHVZK :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[ TRANSCRIPT ] : chInput → chTranscript
    ] A_export A →
    fdisjoint LA Sigma_locs →
    ɛ_SHVZK A = 0.
Proof.
  intros LA A Va Hdisj.
  apply: eq_rel_perf_ind.
  all: ssprove_valid.
  3: apply fdisjoints0.
  1:{ instantiate (1 := heap_ignore Sigma_locs).
      ssprove_invariant.
      apply fsubsetUl. }
  simplify_eq_rel hwe.
  (* Programming logic part *)
  destruct hwe as [[h w] e].
  (* We can only simulate if the relation is valid *)
  ssprove_sync_eq. intros rel.
  (* When relation holds we can reconstruct the first message from the response *)
  unfold R in rel. apply reflection_nonsense in rel.
  eapply r_uniform_bij with (1 := bij_f (otf w) (otf e)). intros z_val.
  ssprove_contract_put_get_lhs.
  apply r_put_lhs.
  ssprove_restore_pre.
  1: ssprove_invariant.
  apply r_ret.
  (* Ambient logic proof of post condition *)
  intros s₀ s₁ Hs.
  unfold f.
  rewrite rel.
  split.
  2: apply Hs.
  simpl.
  rewrite otf_fto expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite expgD - !expgVn.
  rewrite group_prodC group_prodA group_prodC group_prodA /=.
  rewrite expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite -expgM -expgMn.
  2: apply group_prodC.
  rewrite mulgV expg1n mul1g.
  cbn. rewrite Zp_mulC.
  reflexivity.
Qed.

Lemma otf_neq :
  ∀ (a b : choiceChallenge),
    a != b → otf a != otf b.
Proof.
  intros a b.
  apply: contra => H.
  rewrite bij_eq in H.
  - assumption.
  - apply enum_val_bij.
Qed.

Lemma neq_pos :
  ∀ (q : nat) (a b : Zp_finZmodType q),
    a != b →
    a - b != 0.
Proof.
  intros q a b.
  apply contraPneq => H_eq.
  assert (H : (a - b == 0)).
  { by rewrite H_eq. }
  rewrite subr_eq0 in H.
  apply reflection_nonsense in H.
  rewrite H.
  unfold not => contra.
  rewrite eq_refl in contra.
  discriminate.
Qed.

(* Lemma proving that the output of the extractor defined for Schnorr's
  protocol is perfectly indistinguishable from real protocol execution.
*)
Lemma extractor_success:
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface
      #val #[ SOUNDNESS ] : chStatement → 'bool
    ] A_export A →
    ValidPackage LAdv [interface] [interface
      #val #[ ADV ] : chStatement → chSoundness
    ] Adv →
    fdisjoint LA (Sigma_locs :|: LAdv) →
    ɛ_soundness A Adv = 0.
Proof.
  intros LA A LAdv Adv VA VAdv Hdisj.
  apply: eq_rel_perf_ind_eq.
  2,3: apply Hdisj.
  simplify_eq_rel h.
  (* This program is composed with abstract adversarial code. *)
  (* We need to ensure that the composition is valid. *)
  destruct (Adv ADV) as [[? []]|].
  2:{ apply r_ret. auto. }
  repeat destruct choice_code_eqP.
  2,3: apply r_ret ; auto.
  apply rsame_head. intros [s [[s0 s3] [s1 s2]]].
  ssprove_code_simpl. simpl.
  match goal with
  | |- context [ if ?b then _ else _ ] => case b eqn:rel
  end.
  2: apply r_ret ; intuition auto.
  apply r_ret.
  intros. intuition auto.
  (* Algebraic proof that the produced witness satisfies the relation. *)
  unfold R.
  unfold "&&" in rel.
  inversion rel.
  repeat match goal with
  | |- context [ if ?b then _ else _ ] => case b eqn:?
  end.
  2,3: discriminate.
  rewrite otf_fto in Heqs4.
  rewrite otf_fto in rel.
  apply reflection_nonsense in rel.
  apply reflection_nonsense in Heqs4.
  rewrite H1.
  rewrite otf_fto expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite expgM expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite expgD -FinRing.zmodVgE expg_zneg.
  2: apply cycle_id.
  rewrite Heqs4 rel !expgMn.
  2-3: apply group_prodC.
  rewrite invMg !expgMn.
  2: apply group_prodC.
  rewrite !group_prodA.
  rewrite group_prodC 2!group_prodA -expgMn.
  2: apply group_prodC.
  rewrite mulVg expg1n mul1g -expg_zneg.
  2:{
    have Hx : exists ix, otf h = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    destruct Hx as [ix ->].
    apply mem_cycle.
  }
  rewrite expgAC.
  rewrite [otf h ^+ (- otf s1) ^+ _] expgAC.
  rewrite -expgD -expgM.
  have <- := @expg_mod _ q.
  2:{
    have Hx : exists ix, otf h = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    destruct Hx as [ix ->].
    rewrite expgAC /q.
    rewrite expg_order.
    apply expg1n.
  }
  rewrite -modnMmr.
  have -> :
    (modn
       (addn (@nat_of_ord (S (S (Zp_trunc q))) (@otf Challenge s0))
             (@nat_of_ord (S (S (Zp_trunc q)))
                          (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                      (@otf Challenge s1)))) q) =
    (@nat_of_ord (S (S (Zp_trunc q)))
                   (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1)))).
  { simpl.
    rewrite modnDmr.
    destruct (otf s1) as [a Ha].
    destruct a as [| Pa].
    - simpl.
      rewrite subn0 modnn addn0 modnDr.
      rewrite -> order_ge1 at 3.
      rewrite modn_small.
      + reflexivity.
      + rewrite <- order_ge1 at 2. apply ltn_ord.
    - simpl.
      rewrite <- order_ge1 at 4.
      rewrite modnDmr.
      reflexivity.
  }
  have -> :
    (modn
       (muln (@nat_of_ord (S (S (Zp_trunc q)))
                          (@GRing.inv (FinRing.UnitRing.unitRingType (Zp_finUnitRingType (Zp_trunc q)))
                                      (@GRing.add (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                                  (@otf Challenge s0)
                                                  (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                                              (@otf Challenge s1)))))
             (@nat_of_ord (S (S (Zp_trunc q)))
                          (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1))))) q) =
    (Zp_mul
       (@GRing.inv (FinRing.UnitRing.unitRingType (Zp_finUnitRingType (Zp_trunc q)))
                   (@GRing.add (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                               (@otf Challenge s0)
                               (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                           (@otf Challenge s1))))
       (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1)))).
  { simpl.
    rewrite modnDmr.
    rewrite <- order_ge1 at 9.
    rewrite modnMmr.
    reflexivity.
  }
  rewrite Zp_mulVz.
  1: cbn ; by rewrite eq_refl.
  rewrite -> order_ge1 at 1.
  apply otf_neq in Heqb.
  rewrite prime_coprime.
  2: apply prime_order.
  rewrite gtnNdvd.
  - done.
  - rewrite lt0n.
    apply neq_pos.
    assumption.
  - destruct (otf s0 - otf s1) as [k Hk].
    simpl.
    rewrite order_ge1 in Hk.
    apply Hk.
Qed.

Lemma hiding_adv :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[ HIDING ] : chInput → chMessage
    ] A_export A →
    fdisjoint LA Com_locs →
    fdisjoint LA Sigma_locs →
    ɛ_hiding A = 0.
Proof.
  intros LA A Va Hdisj0 Hdisj1.
  unfold ɛ_hiding.
  eapply eq_rel_perf_ind.
  1,2: exact _.
  1:{
    instantiate (1 := (heap_ignore Com_locs)).
    ssprove_invariant.
    unfold Sigma_locs.
    rewrite !fset0U.
    apply fsubsetU.
    apply /orP. left.
    apply fsubsetU.
    apply /orP. left.
    apply fsubsetxx.
  }
  3,4:
    rewrite ?fset0U ; unfold Sigma_locs;
    repeat rewrite fdisjointUr ;
    apply /andP ; split ; eassumption.
  2: apply Va.
  simplify_eq_rel hwe.
  ssprove_code_simpl.
  simplify_linking.
  destruct hwe as [[h w] e].
  apply r_const_sample_R.
  1: apply LosslessOp_uniform.
  intros e'.
  rewrite !cast_fun_K.
  ssprove_code_simpl.
  ssprove_code_simpl_more.
  ssprove_sync_eq=> rel.
  ssprove_sync=> x.
  ssprove_contract_put_get_lhs.
  ssprove_contract_put_get_rhs.
  eapply r_put_vs_put.
  eapply r_put_vs_put.
  eapply r_put_vs_put.
  ssprove_restore_pre. 1: ssprove_invariant.
  apply r_ret. intuition auto.
Qed.

(* Main theorem proving that the Schnorr protocol has perfect hiding. *)
Theorem schnorr_com_hiding :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[ HIDING ] : chInput → chMessage
    ] A_export A →
    fdisjoint LA Com_locs →
    fdisjoint LA Sigma_locs →
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK_ideal) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK_ideal) A <= 0.
Proof.
  intros LA A Va Hdisj0 Hdisj1.
  have H := commitment_hiding LA A 0 Va.
  rewrite !GRing.addr0 in H.
  have HS := schnorr_SHVZK _ _ _.
  rewrite hiding_adv in H.
  2,3: assumption.
  apply AdvantageE_le_0 in H.
  1: rewrite H ; trivial.
  intros B Vb.
  have -> := HS _ B Vb.
  2:{ erewrite fdisjointUl.
      apply /andP.
      split.
      - assumption.
      - unfold Com_locs, Sigma_locs.
        rewrite -fset1E.
        rewrite fdisjoints1.
        in_fset_auto. }
  done.
Qed.

(* Main theorem *)
(* The commitment scheme instantiated from Schnorr' protocol *)
(* is binding equal to the hardness of the relation *)
(* (I.e. how hard is it to produce a valid witness for a fixed public input)*)
Theorem schnorr_com_binding :
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface
      #val #[ SOUNDNESS ] : chStatement → 'bool
    ] A_export A →
    ValidPackage LAdv [interface] [interface
      #val #[ ADV ] : chStatement → chSoundness
    ] Adv →
    fdisjoint LA (Sigma_locs :|: LAdv) →
    AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <= 0.
Proof.
  intros LA A LAdv Adv VA VAdv Hdisj.
  have H := commitment_binding LA A LAdv Adv VA VAdv Hdisj.
  rewrite extractor_success in H. 2: apply Hdisj.
  apply H.
Qed.

End Schnorr.

Module GP_Z3 <: GroupParam.

  Definition gT : finGroupType := Zp_finGroupType 2.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := Zp1.

  Lemma g_gen : ζ = <[g]>.
  Proof.
    unfold ζ, g. apply Zp_cycle.
  Qed.

  Lemma prime_order : prime #[g].
  Proof.
    unfold g.
    rewrite order_Zp1.
    reflexivity.
  Qed.

End GP_Z3.

Module Schnorr_Z3 := Schnorr GP_Z3.
