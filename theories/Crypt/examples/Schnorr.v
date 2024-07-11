
From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol Casts.

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

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

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

  Definition Witness : finType := Finite.clone _ 'Z_q.
  Definition Statement : finType := gT.
  Definition Message : finType := gT.
  Definition Challenge : finType := Finite.clone _ 'Z_q.
  Definition Response : finType :=  Finite.clone _ 'Z_q.
  Definition Transcript : finType :=
    prod (prod Message Challenge) Response.

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
  Definition Bool_pos : Positive #|(bool:choiceType)|.
  Proof.
    rewrite card_bool. done.
  Defined.

End MyParam.

Module MyAlg <: SigmaProtocolAlgorithms MyParam.

  Import MyParam.

  #[local] Existing Instance Bool_pos.

  Definition choiceWitness : choice_type := 'fin #|Witness|.
  Definition choiceStatement : choice_type := 'fin #|Statement|.
  Definition choiceMessage : choice_type := 'fin #|Message|.
  Definition choiceChallenge : choice_type := 'fin #|Challenge|.
  Definition choiceResponse : choice_type := 'fin #|Response|.
  Definition choiceTranscript : choice_type :=
    chProd
      (chProd (chProd choiceStatement choiceMessage) choiceChallenge)
      choiceResponse.
  Definition choiceBool := 'fin #|bool_choiceType|.

  Definition i_witness := #|Witness|.

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

  Definition KeyGen (w : choiceWitness) := fto (g ^+ w).

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
  ∀ (q : nat) (a b : ('Z_q:finZmodType)),
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
  ∀ LA A,
    ValidPackage LA [interface
      #val #[ SOUNDNESS ] : chSoundness → 'bool
    ] A_export A →
    ɛ_soundness A = 0.
Proof.
  intros LA A VA.
  apply: eq_rel_perf_ind_eq.
  2,3: apply fdisjoints0.
  simplify_eq_rel h.
  destruct h as [? [? [? [? [? ?]]]]].
  destruct s1.
  case [&& _ & _] eqn:e.
  all: apply r_ret; auto.
  intros h1 h2 ->.
  (* Algebraic proof that the produced witness satisfies the relation. *)
  unfold R.
  unfold "&&" in e.
  inversion e.
  repeat match goal with
  | |- context [ if ?b then _ else _ ] => case b eqn:?
  end.
  2,3: discriminate.
  rewrite otf_fto in Heqs4.
  rewrite otf_fto in e.
  apply reflection_nonsense in e.
  apply reflection_nonsense in Heqs4.
  rewrite H0.
  rewrite otf_fto expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite expgM expg_mod.
  2: rewrite order_ge1 ; apply expg_order.
  rewrite expgD -FinRing.zmodVgE expg_zneg.
  2: apply cycle_id.
  rewrite Heqs4 e !expgMn.
  2-3: apply group_prodC.
  rewrite invMg !expgMn.
  2: apply group_prodC.
  rewrite !group_prodA.
  rewrite group_prodC 2!group_prodA -expgMn.
  2: apply group_prodC.
  rewrite mulVg expg1n mul1g -expg_zneg.
  2:{
    have Hx : exists ix, otf s = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    destruct Hx as [ix ->].
    apply mem_cycle.
  }
  rewrite expgAC.
  rewrite [otf s ^+ (- otf s2) ^+ _] expgAC.
  rewrite -expgD -expgM.
  have <- := @expg_mod _ q.
  2:{
    have Hx : exists ix, otf s = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    destruct Hx as [ix ->].
    rewrite expgAC /q.
    rewrite expg_order.
    apply expg1n.
  }
  rewrite -modnMmr.
  have -> :
    (modn
       (addn (@nat_of_ord (S (S (Zp_trunc q))) (@otf Challenge s1))
             (@nat_of_ord (S (S (Zp_trunc q)))
                (GRing.opp
                   (@otf Challenge s2))))
       q) =
    (@nat_of_ord (S (S (Zp_trunc q)))
                   (@Zp_add (S (Zp_trunc q)) (@otf Challenge s1) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s2)))).
  { simpl.
    rewrite modnDmr.
    destruct (otf s2) as [a Ha].
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
                (GRing.inv
                   (GRing.add
                      (@otf Challenge s1)
                      (GRing.opp
                         (@otf Challenge s2)))))
          (@nat_of_ord (S (S (Zp_trunc q)))
             (@Zp_add (S (Zp_trunc q)) (@otf Challenge s1) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s2))))) q) =
    (Zp_mul
       (GRing.inv
          (GRing.add
             (@otf Challenge s1)
             (GRing.opp
                (@otf Challenge s2))))
       (@Zp_add (S (Zp_trunc q)) (@otf Challenge s1) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s2)))).
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
  - destruct (otf s1 - otf s2) as [k Hk].
    simpl.
    rewrite order_ge1 in Hk.
    apply Hk.
Qed.

(* Main theorem proving that the Schnorr protocol has perfect hiding. *)
Theorem schnorr_com_hiding :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[HIDING] : (chChallenge) × (chChallenge) → chMessage
    ] A_export (A ∘ par KEY (ID Hiding_E)) ->
    fdisjoint LA KEY_locs ->
    fdisjoint LA Sigma_to_Com_locs ->
    fdisjoint LA (fset [:: setup_loc]) ->
    fdisjoint LA Sigma_locs ->
    fdisjoint LA Simulator_locs ->
    ɛ_hiding A <= 0.
Proof.
  intros LA A VA Hd1 Hd2 Hd3 Hd4 Hd5.
  eapply le_trans.
  1: eapply commitment_hiding with (LA := LA).
  all: try assumption.
  1: apply fdisjoint0s.
  {
    unfold Sigma_locs.
    unfold commit_loc.
    unfold statement_loc.
    unfold witness_loc.
    rewrite !fset_cons.
    rewrite -fset0E.
    rewrite fdisjointUr ; apply /andP ; split.
    - rewrite fdisjoints1.
      rewrite fset1E.
      rewrite fsetU0.
      rewrite -fset1E.
      unfold "\notin".
      rewrite in_fset1.
      case (_ == _) eqn:e.
      2: done.
      move: e => /eqP.
      done.
    - rewrite fdisjointUr ; apply /andP ; split.
      + rewrite fdisjoints1.
        rewrite fset1E.
        rewrite fsetU0.
        rewrite -fset1E.
        unfold "\notin".
        rewrite in_fset1.
        case (_ == _) eqn:e.
        2: done.
        move: e => /eqP.
        done.
      + apply fdisjoints0.
  }
  rewrite addr0.
  rewrite add0r.
  erewrite schnorr_SHVZK.
  2: {
    ssprove_valid.
    1: instantiate (1 := (LA :|: (setup_loc |: Sigma_to_Com_locs))).
    3: apply fsubsetxx.
    2: apply fsub0set.
    - apply fsubsetUl.
    - apply fsubsetU ; apply /orP ; right.
      apply fsubsetxx.
  }
  2: {
    (* unfold Sigma_locs. *)
    unfold Sigma_to_Com_locs.
    unfold Simulator_locs.
    rewrite fsetU0.
    rewrite fdisjointUl ; apply /andP ; split.
    - assumption.
    - unfold Sigma_locs.
      rewrite fdisjointUl ; apply /andP ; split.
      + rewrite fdisjoint1s.
        unfold "\notin".
        rewrite -fset1E.
        rewrite in_fset1.
        done.
      + unfold Com_locs.
        rewrite fset_cons.
        rewrite fdisjointUl ; apply /andP ; split.
        ++ rewrite fdisjoint1s.
           rewrite -fset1E.
           unfold "\notin".
           rewrite in_fset1.
           done.
        ++ 
           rewrite -!fset1E.
           rewrite fdisjoint1s.
            unfold "\notin".
            rewrite in_fset1.
            done.
  }
  rewrite Advantage_sym.
  erewrite schnorr_SHVZK.
  2: {
    ssprove_valid.
    1: instantiate (1 := (LA :|: (setup_loc |: Sigma_to_Com_locs))).
    3: apply fsubsetxx.
    2: apply fsub0set.
    - apply fsubsetUl.
    - apply fsubsetU ; apply /orP ; right.
      apply fsubsetxx.
  }
  2: {
    (* unfold Sigma_locs. *)
    unfold Sigma_to_Com_locs.
    unfold Simulator_locs.
    rewrite fsetU0.
    rewrite fdisjointUl ; apply /andP ; split.
    - assumption.
    - unfold Sigma_locs.
      rewrite fdisjointUl ; apply /andP ; split.
      + rewrite fdisjoint1s.
        unfold "\notin".
        rewrite -fset1E.
        rewrite in_fset1.
        done.
      + unfold Com_locs.
        rewrite fset_cons.
        rewrite fdisjointUl ; apply /andP ; split.
        ++ rewrite fdisjoint1s.
           rewrite -fset1E.
           unfold "\notin".
           rewrite in_fset1.
           done.
        ++ 
           rewrite -!fset1E.
           rewrite fdisjoint1s.
            unfold "\notin".
            rewrite in_fset1.
            done.
  }
  rewrite addr0 add0r.
  apply eq_ler.
  eapply eq_rel_perf_ind.
  1,2: exact _.
  1:{
    instantiate (1 := (heap_ignore Com_locs)).
    ssprove_invariant.
    unfold Sigma_to_Com_locs.
    rewrite !fset0U.
    apply fsubsetU; apply /orP; left.
    apply fsubsetU; apply /orP; left.
    apply fsubsetU; apply /orP; right.
    apply fsubsetU; apply /orP; left.
    apply fsubsetxx.
  }
  2: apply VA.
  3: {
    rewrite fset0U.
    rewrite fdisjointUr ; apply /andP ; split.
    2: assumption.
    rewrite fdisjointUr ; apply /andP ; split.
    2: assumption.
    rewrite fset1E. assumption.
  }
  2: {
    rewrite fset0U.
    rewrite fdisjointUr ; apply /andP ; split.
    2: assumption.
    rewrite fdisjointUr ; apply /andP ; split.
    2: assumption.
    rewrite fset1E. assumption.
  }
  rewrite Sigma_to_Com_Aux_equation_1.
  simplify_eq_rel hwe.
  ssprove_code_simpl.
  simplify_linking.
  destruct hwe as [e e'].
  apply r_const_sample_R.
  1: apply LosslessOp_uniform.
  intros e_rand.
  rewrite !cast_fun_K.
  ssprove_code_simpl.
  ssprove_code_simpl_more.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros b.
  simpl.
  case (Nat.even b) eqn:hb.
  - rewrite hb ; clear hb.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_sync=>setup.
    apply r_assertD.
    1: done.
    intros _ _.
    ssprove_sync=> w.
    apply r_assertD.
    1: done.
    intros _ _.
    ssprove_sync.
    apply r_assertD.
    1: done.
    intros _ rel.
    ssprove_sync=>x.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    eapply r_put_vs_put.
    eapply r_put_vs_put.
    eapply r_put_vs_put.
    ssprove_restore_pre. 1: ssprove_invariant.
    apply r_ret. intuition auto.
  - rewrite hb ; clear hb.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_sync=>setup.
    apply r_assertD.
    1: done.
    intros _ _.
    ssprove_sync=> w.
    apply r_assertD.
    1: done.
    intros _ _.
    ssprove_sync.
    apply r_assertD.
    1: done.
    intros _ rel.
    ssprove_sync=>x.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    eapply r_put_vs_put.
    eapply r_put_vs_put.
    eapply r_put_vs_put.
    ssprove_restore_pre. 1: ssprove_invariant.
    apply r_ret. intuition auto.
Qed.


End Schnorr.

Module GP_Z3 <: GroupParam.

  Definition gT : finGroupType := 'Z_2.
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
