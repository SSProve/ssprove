From Equations Require Import Equations.
From Coq Require Import Morphisms.
From mathcomp Require Import all_ssreflect.
From Mon Require Import SPropBase Base.
From Mon Require Import SpecificationMonads.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd LiftStateful OrderEnrichedRelativeAdjunctions OrderEnrichedRelativeAdjunctionsExamples TransformingLaxMorph StateTransformingLaxMorph ThetaDex FreeProbProg LaxComp LaxFunctorsAndTransf Axioms UniversalFreeMap RelativeMonadMorph_prod.

(*the file is broken but we never use it (cf _CoqProject) *)

Import SPropNotations.

Section RetrieveRlmmParameters.
  Context {C D1 D2 : ord_category} {J1 : ord_functor C D1} {J12 : ord_functor D1 D2}
    {J2 : ord_functor C D2}.
  Context  {Chi : natIso J2 (ord_functor_comp J1 J12)}.
  Context {M1 : ord_relativeMonad J1} {M2 : ord_relativeMonad J2}.

  Definition rlmm_getBaseIso (θ : relativeLaxMonadMorphism J12 Chi M1 M2) := Chi.

End RetrieveRlmmParameters.

Section Aux.
  Notation dnib := ord_relmon_bind.
  Notation η := ord_relmon_unit.

  Let Jspec :=
  (ord_functor_comp Theta_exCP.F_choice_prod SubDistr.chDiscr).
  Context {W : ord_relativeMonad Jspec}.

  Context {AA BB : prod_cat ord_choiceType ord_choiceType}.
  Context (f f' : OrdCat ⦅ Jspec AA; W BB ⦆).
  Context (Hf: f ⪷ f').
  Context (x x' : dfst (W AA)).
  Context (Hx : x ≤ x').

  Lemma monmonBind : (dnib W f)∙1 x ≤ (dnib W f')∙1 x'.
  Proof.
    assert (H : (dnib W f) ⪷ (dnib W f')).
      apply ord_relmon_bind_proper. assumption.
    transitivity ((dnib W f')∙1 x).
      apply H.
    apply monotonic_bind.
    assumption.
  Qed.

  Context (U : Type) (P : U -> Prop).
  Context (z : U) (ez : P z).
  Lemma etaSigRule : exist P (exist P z ez)∙1 ez = exist P z ez.
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma injSigProj : forall(r1 r2 : {x : U | P x}), r1 ∙1 = r2 ∙1 -> r1 = r2.
  Proof.
    move=> r1 r2. move=> Hr.
    destruct r1 as [r1 r1prf]. destruct r2 as [r2 r2prf].
    cbn in Hr. move: r2prf r1prf. rewrite Hr.
    move=> r2prf r1prf.
    assert (Hp : r2prf = r1prf).
      apply proof_irrelevance.
    rewrite Hp.
    reflexivity.
  Qed.

  Lemma etaSigRule' : forall (r : {x : U | P x}) (er_bis : P r∙1), exist P r∙1 er_bis = r.
  Proof.
    move=> [r er]. cbn. move=> er_bis.
    assert (er = er_bis).
      apply proof_irrelevance.
    rewrite H.
    reflexivity.
  Qed.


  Lemma v_nonsense : forall (A1 A2 : ord_choiceType) (a1 : A1) (a2 : A2),
  ((Theta_exCP.v ⟨ A1, A2 ⟩) ∙1 (a1, a2)) = ⟨a1,a2⟩.
  Proof.
   move=> [A1 chA1] [A2 chA2]. move=> a1 a2.
   cbn. reflexivity.
  Qed.


End Aux.



Section AbstractLiftOplaxness.
  Notation dnib := ord_relmon_bind.
  Notation η := ord_relmon_unit.

  Context {S1 S2 : choiceType}.


  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.


  (*untransformed relative lax monad morphism*)
  Context {M1 M2 : ord_relativeMonad choice_incl}.
  Let Mprod := product_rmon M1 M2.
  Let Jcomp := prod_functor choice_incl choice_incl.

  Let Jspec :=
  (ord_functor_comp Theta_exCP.F_choice_prod SubDistr.chDiscr).
  Context {W : ord_relativeMonad Jspec}.

  (*We prove lift oplaxness for a morphism ressembling thetaDex*)
  Let thetaDex_filled :=  @thetaDex probE chUniverse chElement prob_handler.
  Context (θ : relativeLaxMonadMorphism _ (rlmm_getBaseIso thetaDex_filled)
  Mprod W).


  (*transformed lax morphism*)

  Let StT_M := AdjTransform Mprod _ _ (Chi_DomainStateAdj S1 S2).
  Let StT_W := AdjTransform W _ _ (Chi_CodomainStateAdj S1 S2).

  (* Goal True. *)
  (*   pose (bla := Transformed_lmla θ *)
  (*   (Chi_DomainStateAdj S1 S2) (Chi_CodomainStateAdj S1 S2) ). *)
  (*   cbn in bla. *)
  (*   unshelve epose (blou := bla _). *)

  Let myStateBeta' :=  @state_beta' S1 S2.
  Program Definition mystT_θ_adj :=
    Transformed_lmla θ
    (Chi_DomainStateAdj S1 S2) (Chi_CodomainStateAdj S1 S2) myStateBeta' _ _.
  Next Obligation.
    move=> [A1 A2 [a1 a2] [s1 s2]].
    (*Unfortunately we have to manually destruct A1 and A2 because functions were defined like this in
     Theta_exCP.v*)
    move: A1 a1. move=> [A1 chA1] a1.
    move: A2 a2. move=> [A2 chA2] a2.
    cbv. reflexivity.
  Qed.
  Next Obligation.
    move=> [[A1 chA1] [A2 chA2]] [Y1 Y2] [g1 g2]. simpl.
    apply sig_eq. simpl. apply boolp.funext. move=> [[a1 s1] [a2 s2]].
    simpl. reflexivity.
  Qed.

  Let myStTθ := rlmm_from_lmla mystT_θ_adj.

  (*Liftings*)
  (*computational lift*)
  Let compLift_filled := @StatefulCompLift M1 M2 S1 S2.
  (*Specification lift*)
  Let specLift_filled := @StatefulSpecLift S1 S2 W.


  (*StT(θ) ∘ complift*)
  Let StTθ_of_complift :=
  rlmm_comp _ _ _ _ _ _ _ compLift_filled myStTθ.

  (*speclift ∘ θ*)
  Let speclift_of_θ := rlmm_comp _ _ _ _ _ _ _ θ specLift_filled.


  Lemma abstract_lift_oplaxness : forall (A1 A2 : ord_choiceType),
  StTθ_of_complift ⟨A1,A2⟩ ⪷ speclift_of_θ ⟨A1,A2⟩.
  Proof.
    move=> A1 A2. move=> [m1 m2]. move=> [is1 is2].
    cbn.
    rewrite /TransformingLaxMorph.post_smAlpha''_obligation_1.
    rewrite /TransformingLaxMorph.Kl_alpha_obligation_1.
    rewrite /Theta_exCP.F_choice_prod_obj.
    rewrite /TransformingLaxMorph.pre_smAlpha''_obligation_1.
    rewrite /TransformingLaxMorph.Kl_beta_obligation_1.
    cbn. rewrite /Theta_exCP.F_choice_prod_obj.
    rewrite !ord_relmon_law1. cbn.
    unfold comp.
    rewrite etaSigRule. rewrite etaSigRule'.
    rewrite (ord_relmon_law1 W). cbn.
    unshelve epose (θbind := (rlmm_law2 _ _ _ _ θ) _ _ _ _).
      exact ⟨A1,A2⟩.
      exact ⟨ prod_choiceType A1 S1, prod_choiceType A2 S2 ⟩.
      constructor.
        cbn. exact (fun a : A1 => η M1 (prod_choiceType A1 S1) (a, is1)).
        cbn. exact (fun a : A2 => η M2 (prod_choiceType A2 S2) (a, is2)).
      cbn. exact ⟨m1,m2⟩. cbn in θbind.
    etransitivity.
      apply θbind. clear θbind.
    unfold comp. cbn.
    unshelve epose (θret := rlmm_law1 _ _ _ _ θ _).
      exact ⟨ prod_choiceType A1 S1, prod_choiceType A2 S2 ⟩.
    cbn in θret.
    apply monmonBind.
    move=> [a1 a2]. cbn.
    etransitivity.
    apply (  let x:= (a1,a2) in θret ⟨(nfst ((Theta_exCP.v ⟨ A1, A2 ⟩) ∙1 x), is1),
          (nsnd ((Theta_exCP.v ⟨ A1, A2 ⟩) ∙1 x), is2)⟩   ).
    unfold Theta_exCP.v_inv0. cbn.
    rewrite v_nonsense.
    reflexivity. reflexivity.
  Qed.



End AbstractLiftOplaxness.



Section LiftOplaxness.
  Notation dnib := ord_relmon_bind.
  Notation η := ord_relmon_unit.

  Context {S1 S2 : choiceType}.


  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.

  (*The untransformed concrete lax morphism θdex : FrP² → Wrelprop*)
  Let thetaDex_filled := @thetaDex probE chUniverse chElement prob_handler.
  (*the two computational monads*)
  Let M1 := rFreePr probE chUniverse chElement.
  Let M2 := rFreePr probE chUniverse chElement.

  (*The transformed morphism*)
  Let stT_thetaDex_filled := @stT_thetaDex probE chUniverse chElement prob_handler S1 S2.

  (*The computational lift*)
  Definition Lift_stComp := @StatefulCompLift M1 M2 S1 S2.

  (*The specification lift*)
  Let Lift_stSpec := @StatefulSpecLift S1 S2 (rlmm_codomain thetaDex_filled).

  Definition stTθdex_of_lift :=
  rlmm_comp _ _ _ _ _ _ _ Lift_stComp stT_thetaDex_filled.

  Definition lift_of_θdex :=
  rlmm_comp _ _ _ _ _ _ _ thetaDex_filled Lift_stSpec.

  Lemma Lift_oplaxness :
  forall (A1 A2 : ord_choiceType),
  stTθdex_of_lift ⟨A1,A2⟩ ⪷ lift_of_θdex ⟨A1,A2⟩.
  Proof.
    move=> A1 A2.
    apply (@abstract_lift_oplaxness S1 S2 probE chUniverse chElement prob_handler
  _ _ _ thetaDex_filled).
  Qed.

End LiftOplaxness.


Section unary_FreeProb_Into_FreeProbState.
  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.
  Context {S : choiceType}. (*either S1 or S2*)

  (*unary free prob*)
  Let FrP := rFreePr probE chUniverse chElement.

  (*unary free prob+state*)
  Let FrStP_filled := @FrStP probE chUniverse chElement S.

  Let probOps := Prob_ops_collection probE chUniverse chElement.
  Let probAr := Prob_arities probE chUniverse chElement.

  Let probStateOps :=  @ops_StP probE chUniverse chElement S.
  Let probStateAr :=  @ar_StP probE chUniverse chElement S.

  Definition iotaSigMap :
  forall op : probOps,
  FrStP_filled (probAr op) := fun probop =>
    callrFree _ _ (inr probop).

  (*unary morphism*)
  Definition unary_freeprob_into_freestateprob :
  relativeMonadMorphism _  trivialChi FrP FrStP_filled :=
  outOfFree iotaSigMap.


(*We describe a preimage morphism on Ty/chTy , of the inclusion morphism above.
  In other words we describe a point in the fiber
     Fr^{-1}(morph above : FrP -> FrStP) : sigProb -> sigStateProb *)

  Definition sigMap_Pr_into_StPr : probOps -> probStateOps.
    move=> probop.
    right. exact probop.
  Defined.

  Lemma slice_Pr_into_StPr : forall probop : probOps,
  probStateAr ( sigMap_Pr_into_StPr (probop) ) = probAr probop.
  Proof.
    move=> probop. cbn. reflexivity.
  Qed.


  Context (smprobop : probOps).
  Program Definition helpUnify :
  rFreeF probStateOps probStateAr (probAr smprobop)
  := callrFree (probStateOps) (probStateAr) (sigMap_Pr_into_StPr smprobop).

  Context (Ops : Type) (Ar : Ops -> choiceType) (Z : choiceType) (op : Ops)
       (opk :  Ar op -> rFreeF Ops Ar Z).
  Lemma ropr_vs_bind :
  ropr Ops Ar Z op opk = bindrFree Ops Ar (callrFree Ops Ar op) opk.
  Proof.
    cbn. reflexivity.
  Qed.


End unary_FreeProb_Into_FreeProbState.




Section FreeProb_Into_FreeProbState.
  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.
  Context {S1 S2 : choiceType}.

  Let incl_filled := @unary_freeprob_into_freestateprob probE chUniverse chElement.
  Definition FrPsqu_into_FrStPsqu := prod_relativeMonadMorphism (incl_filled S1) (incl_filled S2).

End FreeProb_Into_FreeProbState.


Section EquivalentCompLift.

  Context (probE : Type -> Type) (chUniverse : Type) (chElement : chUniverse -> choiceType)
         (S1 S2 : choiceType) (prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T).

  Notation ProbSig := (Prob_ops_collection probE chUniverse chElement).
  Notation probAnsType := (Prob_arities probE chUniverse chElement).


  Let probStateOps1 :=  @ops_StP probE chUniverse chElement S1.
  Let probStateAr1 :=  @ar_StP probE chUniverse chElement S1.


  Arguments bindrFree {_ _ _ _}.
  Arguments ropr {_ _ _}.

  Let justInterpState_filled :=
  @justInterpState probE chUniverse chElement S1 S2 prob_handler.

  Let iotaSqu :=  @FrPsqu_into_FrStPsqu probE chUniverse chElement S1 S2.

  Let M1 := rFreePr probE chUniverse chElement.
  Let M2 := rFreePr probE chUniverse chElement.
  Let myCompLift := @StatefulCompLift M1 M2 S1 S2.

  Let jis_of_iota := rlmm_comp _ _ _ _ _ _ _ iotaSqu justInterpState_filled.

  (* Goal True. *)
  (*   epose (bla := rlmm_law2 _ _ _ _ jis_of_iota _ _ ?[f]). *)
  (*   cbn in bla. *)
  (*   move: bla=> [bla1 bla2]. *)
  (*   epose (bla1' := bla1 ?[m1]).  *)
  (*   rewrite {+}/FreeProbProg.rFree_obligation_2 in bla1'. *)
  (*   Abort. *)


  Lemma equivalentCompLift :
  forall (A1 A2 : ord_choiceType),
  jis_of_iota ⟨A1,A2⟩ = myCompLift ⟨A1,A2⟩.
  Proof.
    move=> A1 A2.
    cbn. rewrite /StatefulCompLift0. f_equal.
    - apply boolp.funext. move=> m1.

      elim: m1 => [a1 |// probop k Hind].
        cbn. reflexivity.
      rewrite ropr_vs_bind.
      unshelve epose (localOutOfFree := outOfFree iotaSigMap).
        exact probE. exact chUniverse. exact chElement. exact S1.
      epose (localOutOfFree_bind := rmm_law2 _ _ _ _ localOutOfFree _ _ _).
        eapply equal_f in localOutOfFree_bind.
        cbn in localOutOfFree_bind.
        rewrite /FreeProbProg.rFree_obligation_2 in localOutOfFree_bind.
      erewrite localOutOfFree_bind. clear localOutOfFree_bind localOutOfFree.
      (*external*)
      unshelve epose (localOutOfFree := outOfFree sigMap).
        exact probE. exact chUniverse. exact chElement. exact S1.
      epose (localOutOfFree_bind := rmm_law2 _ _ _ _ localOutOfFree _ _ _).
        eapply equal_f in localOutOfFree_bind.
        cbn in localOutOfFree_bind.
        unfold FreeProbProg.rFree_obligation_2 in localOutOfFree_bind.
      erewrite localOutOfFree_bind. clear localOutOfFree_bind localOutOfFree.

      rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
      apply boolp.funext ; move=> s1.
      eassert (outOfFree_vs_callrFree' :
(UniversalFreeMap.outOfFree_obligation_1 iotaSigMap (probAnsType probop)
          (callrFree ProbSig probAnsType probop))
=
callrFree _ _ (inr probop) ).
      cbn. unfold callrFree.
      reflexivity.
      erewrite outOfFree_vs_callrFree'. clear outOfFree_vs_callrFree'.
      (* unshelve epose (bla := outOfFree_vs_callrFree _ _ _ sigMap). *)
      (*   exact probE. exact chUniverse. exact chElement. exact S1. *)
      (* specialize (bla (inr probop)). *)
      eassert ( vs_callrFree'' :
UniversalFreeMap.outOfFree_obligation_1 sigMap (probAnsType probop)
       (callrFree (state_ops S1 + ProbSig) (ar_StP S1) (inr probop))
=
sigMap (inr probop) ).
      unshelve epose (coucou := outOfFree_vs_callrFree _ _ _ sigMap (inr probop)).
        exact S1.
      rewrite -coucou.
      reflexivity.
      erewrite vs_callrFree''. clear vs_callrFree''.
      assert (simplCont :
    (fun ans_s1 : probAnsType probop * S1 =>
     let (ans, s1) := ans_s1 in
     UniversalFreeMap.outOfFree_obligation_1 sigMap A1
       (UniversalFreeMap.outOfFree_obligation_1 iotaSigMap A1 (k ans)) s1)
=
    (fun ans_ss : probAnsType probop * S1 =>
     let (ans, ss) := ans_ss in
    ord_relmon_bind M1
            (fun a : choice_incl A1 => ord_relmon_unit M1 (prod_choiceType A1 S1) (a, ss))
            (k ans) )
  ).
        apply boolp.funext. move=> [ans ss]. cbn. rewrite Hind. reflexivity.
      rewrite simplCont. clear simplCont.
      assert (sigMap_gives_probop :
(sigMap (inr probop) s1) = ropr probop (fun ans => retrFree _ _ _ (ans,s1)) ).
        cbn. destruct probop as [X op].
        cbn. reflexivity.
      rewrite sigMap_gives_probop.
      cbn. f_equal.
    - apply boolp.funext. move=> m2.

      elim: m2 => [a2 |// probop k Hind].
        cbn. reflexivity.
      cbn.
      rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
      rewrite /Theta_exCP.F_choice_prod_obj.
      apply boolp.funext. move=> s2.
      rewrite /FreeProbProg.rFree_obligation_2.
      eassert (sigMap_gives_probop :
(sigMap (inr probop) s2) = ropr probop (fun ans => retrFree _ _ _ (ans,s2)) ).
        cbn. destruct probop. reflexivity.
      cbn in sigMap_gives_probop. rewrite sigMap_gives_probop. clear sigMap_gives_probop.
      cbn.
      eassert (simplCont :
(fun p : probAnsType probop =>
     UniversalFreeMap.outOfFree_obligation_1 sigMap A2
       (UniversalFreeMap.outOfFree_obligation_1 iotaSigMap A2 (k p)) s2)
=
(fun p : probAnsType probop =>
ord_relmon_bind M2
            (fun a : choice_incl A2 => ord_relmon_unit M2 (prod_choiceType A2 S2) (a, s2))
            (k p))
).
        apply boolp.funext. move=> ans. rewrite Hind. reflexivity.
      rewrite simplCont. reflexivity.
  Qed.

End EquivalentCompLift.


Section ExtendedLiftOplaxness.
  Notation "β \O α" := (rlmm_comp _ _ _ _ _ _ _ α β) (at level 70).
  Notation dnib := ord_relmon_bind.
  Notation η := ord_relmon_unit.

  Context {S1 S2 : choiceType}.

  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.

  Let FrP := rFreePr probE chUniverse chElement.
  Let θprob := @thetaDex probE chUniverse chElement prob_handler.
  Let Wprob := rlmm_codomain θprob.
  Let θStProb :=  @thetaFstdex probE chUniverse chElement S1 S2 prob_handler.
  Let WStProb := rlmm_codomain θStProb.
  Let specLift := @StatefulSpecLift S1 S2 Wprob.
  Let iiota :=  @FrPsqu_into_FrStPsqu probE chUniverse chElement S1 S2.
  Let stTθ :=  @stT_thetaDex probE chUniverse chElement prob_handler S1 S2.
  Let compLift := @StatefulCompLift FrP FrP S1 S2.
  Let justIntState_filled :=
  @justInterpState probE chUniverse chElement S1 S2 prob_handler.
  Let stT_thetaDex_filled :=
  @stT_thetaDex probE chUniverse chElement prob_handler S1 S2.

  Let θStProb_of_iiota :=
  rlmm_comp _ _ _ _ _ _ _ iiota θStProb.

  Let specLift_of_θprob :=
  rlmm_comp _ _ _ _ _ _ _ θprob specLift.

  Let stTθ_of_complift :=
  rlmm_comp _ _ _ _ _ _ _ compLift stTθ.

  (* Lemma whiskered_EquCompLift : *)
  (* forall {A1 A2 : ord_choiceType}, *)
  (* θStProb_of_iiota ⟨A1,A2⟩ = stTθ_of_complift ⟨A1,A2⟩. *)
  (* move=> A1 A2. *)

  Lemma extended_liftOplaxness :
  forall {A1 A2 : ord_choiceType},
  θStProb_of_iiota ⟨A1,A2⟩ ⪷ specLift_of_θprob ⟨A1,A2⟩.
  Proof.
    move=> A1 A2.
    rewrite (rlmm_comp_assoc iiota justIntState_filled stT_thetaDex_filled ⟨A1,A2⟩ ).
    rewrite /right_assoc_rlmm_comp.
    rewrite rlmm_comp_pointwise_formula.
    assert ( ecl : (justIntState_filled \O iiota) ⟨ A1, A2 ⟩ = compLift ⟨A1,A2⟩ ).
      apply equivalentCompLift.
    rewrite ecl. clear ecl.
    transitivity (stTθ_of_complift ⟨A1,A2⟩). reflexivity.
    apply Lift_oplaxness.
  Qed.


End ExtendedLiftOplaxness.


Section MonotonicSpecLift.
  Context {S1 S2 : choiceType}.

  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.

  Let θprob := @thetaDex probE chUniverse chElement prob_handler.
  Let Wprob := rlmm_codomain θprob.
  Let θStProb :=  @thetaFstdex probE chUniverse chElement S1 S2 prob_handler.
  Let WStProb := rlmm_codomain θStProb.

  Context {A1 A2 : choiceType}.
  Context (w1 w2  : Base.dfst (Wprob ⟨ A1, A2 ⟩)).
  Hypothesis (Hw : w1 ≤ w2).

  Let specLift := @StatefulSpecLift S1 S2 Wprob.
  Lemma monSpecLift : (specLift ⟨A1,A2⟩)∙1 w1 ≤ (specLift ⟨A1,A2⟩)∙1 w2.
  Proof.
    destruct (specLift ⟨A1,A2⟩) as [specLift_map specLift_mon].
    apply specLift_mon.
    apply Hw.
  Qed.

End MonotonicSpecLift.

Section LiftJudgment.
  Notation "β \O α" := (rlmm_comp _ _ _ _ _ _ _ α β) (at level 70).
  Notation dnib := ord_relmon_bind.
  Notation η := ord_relmon_unit.

  Context {S1 S2 : choiceType}.

  Context {probE : Type -> Type} {chUniverse : Type} {chElement : chUniverse -> choiceType} {prob_handler : forall T : choiceType, probE T -> SubDistr.SDistr T}.

  (*unary free probabilistic monad "Fr[P]"*)
  Let FrP := rFreePr probE chUniverse chElement.

  (*unary free prob+state monad "Fr[St,P]"*)
  Let FrStP_filled1 := @FrStP probE chUniverse chElement S1.
  Let FrStP_filled2 := @FrStP probE chUniverse chElement S2.

  (*operations and arities for the various free monads involved*)
  Let probOps := Prob_ops_collection probE chUniverse chElement.
  Let probAr := Prob_arities probE chUniverse chElement.

  Let probStateOps1 :=  @ops_StP probE chUniverse chElement S1.
  Let probStateAr1 :=  @ar_StP probE chUniverse chElement S1.

  Let probStateOps2 :=  @ops_StP probE chUniverse chElement S2.
  Let probStateAr2 :=  @ar_StP probE chUniverse chElement S2.


  (*prob signature is included in state+prob signature*)
  Let iiota :=  @FrPsqu_into_FrStPsqu probE chUniverse chElement S1 S2.
  Let iota1 := @unary_freeprob_into_freestateprob probE chUniverse chElement S1.
  Let iota2 := @unary_freeprob_into_freestateprob probE chUniverse chElement S2.


  Lemma iiota_compononents :
    iiota = prod_relativeMonadMorphism iota1 iota2.
  Proof.
    unfold iiota. reflexivity.
  Qed.

  Let θprob := @thetaDex probE chUniverse chElement prob_handler.
  Let Wprob := rlmm_codomain θprob.
  Let θStProb :=  @thetaFstdex probE chUniverse chElement S1 S2 prob_handler.
  Let WStProb := rlmm_codomain θStProb.


  Context {A1 A2 : ord_choiceType}.
  Context (m1 : FrP A1) (m2 : FrP A2).
  Context (w  : Base.dfst (Wprob ⟨ A1, A2 ⟩)).
  Hypothesis ( judg_prob : (θprob ⟨A1,A2⟩)∙1 ⟨m1,m2⟩ ≤ w ). (*relational prob judg*)

  Let specLift := @StatefulSpecLift S1 S2 Wprob.
  Lemma lift_probrules :
  (θStProb ⟨A1,A2⟩)∙1 ⟨iota1 _ m1, iota2 _ m2⟩
  ≤
  (specLift ⟨A1,A2⟩)∙1 w.
  Proof.
    assert (lhs :
    (θStProb ⟨ A1, A2 ⟩) ∙1 ⟨ iota1 A1 m1, iota2 A2 m2 ⟩ =
    ((θStProb \O iiota) ⟨A1,A2⟩)∙1 ⟨m1,m2⟩ ).
      cbn. reflexivity.
    rewrite lhs.
    pose elo :=
    @extended_liftOplaxness S1 S2 probE chUniverse chElement prob_handler A1 A2.
    etransitivity.
    specialize (elo ⟨m1,m2⟩). eapply elo.
    rewrite rlmm_comp_pointwise_formula.
    eapply monSpecLift.
    apply judg_prob.
  Qed.


End LiftJudgment.


