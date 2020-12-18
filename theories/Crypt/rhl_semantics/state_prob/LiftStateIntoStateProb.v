From mathcomp Require Import all_ssreflect all_algebra.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd SubDistr InitialRelativeMonad TransformingLaxMorph StateTransformingLaxMorph OrderEnrichedRelativeAdjunctionsExamples LaxFunctorsAndTransf ThetaDex FreeProbProg OrderEnrichedRelativeAdjunctions OrderEnrichedRelativeAdjunctionsExamples UniversalFreeMap RelativeMonadMorph_prod LaxComp Theta_exCP.

(*We define the computational lift state -> state + prob which relies on StT(η)
for η : "id" → Fr[P]² *)
Section LiftOfStateComp.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).

  Context {S1 S2 : choiceType}.


  Let thetaDex_filled := @thetaDex probE rel_choiceTypes chEmb prob_handler.
  Let Frp_squ := rlmm_domain thetaDex_filled.

  Let myJ := prod_functor choice_incl choice_incl.
  Let myJRmon :=  @initRmon _ _ myJ.

  Let eta_Frp_squ :=  @etaAsRmm _ _ myJ Frp_squ.

  
  Local Program  Definition myBet : lnatTrans
    (lord_functor_comp (strict2laxFunc (binaryToTheS S1 S2))
       (strict2laxFunc (ord_functor_id (prod_cat TypeCat TypeCat))))
    (lord_functor_comp (strict2laxFunc (ord_functor_id (prod_cat TypeCat TypeCat)))
       (strict2laxFunc (binaryToTheS S1 S2))) := mkLnatTrans _ _.
  Next Obligation.
    move=> [A1 A2]. constructor.
    exact (fun bla => bla). exact (fun bla=> bla).
  Defined.
  

  Program Definition stT_eta_Frp_squ_adj :=  Transformed_lmla eta_Frp_squ (Chi_DomainStateAdj S1 S2) (Chi_DomainStateAdj S1 S2) myBet _ _.
  Next Obligation.
    move=> [A1 A2]. move=> [Y1 Y2]. cbn. move=> [f1 f2]. f_equal.
    - apply boolp.funext. move=> [a s]. reflexivity.
    - apply boolp.funext. move=> [a s]. reflexivity.
  Qed.

  Definition stT_eta_Frp_squ := rlmm_from_lmla stT_eta_Frp_squ_adj.

  Definition State_squ := rlmm_domain stT_eta_Frp_squ.
    

  (*We now make the domain of the computational lift free*)
  (*First step: Fr[St]² → StT(choice_incl)²*)
  Let FrSt1 := rFree (state_ops S1) (state_ar S1).
  Let FrSt2 := rFree (state_ops S2) (state_ar S2).

  Definition FrSt_squ := product_rmon FrSt1 FrSt2.

  Let unaryJ_forSt := @initRmon _ _ choice_incl.
  Definition unarySt1 := AdjTransform unaryJ_forSt _ _ (@unaryStTransfromingAdj S1).
  Definition unarySt2 := AdjTransform unaryJ_forSt _ _ (@unaryStTransfromingAdj S2).

  (*qSt_i : Fr[St] → St (with S_i)*)
  Program Definition qSt_1 : relativeMonadMorphism _ trivialChi FrSt1 unarySt1 :=
    @outOfFree (state_ops S1) (state_ar S1) unarySt1 _.
  Next Obligation.
    move=> [aget|aput]. all: cbn.
      move: aget => [|]. 
        exact (fun s => (s,s)). (*true get*)
        exact (fun s _ => (tt,tt) ). (*false get*)
      move: aput => [|].
        exact (fun s => (s,s)).
        move=> new_s. exact (fun _ => (tt,new_s)).
  Defined.
        
  Program Definition qSt_2 : relativeMonadMorphism _ trivialChi FrSt2 unarySt2 :=
    @outOfFree (state_ops S2) (state_ar S2) unarySt2 _.
  Next Obligation.
    move=> [aget|aput]. all: cbn.
      move: aget => [|]. 
        exact (fun s => (s,s)). (*true get*)
        exact (fun s _ => (tt,tt) ). (*false get*)
      move: aput => [|].
        exact (fun s => (s,s)).
        move=> new_s. exact (fun _ => (tt,new_s)).
  Defined.


  Definition pre_qSt : relativeMonadMorphism _  _ FrSt_squ (product_rmon unarySt1 unarySt2) :=
    prod_relativeMonadMorphism qSt_1 qSt_2.

  (*Second step: StT(choice_incl)² → StT(choice_incl²)*)
  Local Program Definition smPhi : natIso myJ
         (ord_functor_comp (prod_functor choice_incl choice_incl)
            (ord_functor_id (prod_cat TypeCat TypeCat))) := mkNatIso _ _ _ _ _ _ _.
  Next Obligation.
    easy.
  Defined.
  Next Obligation.
    easy.
  Defined.


  Program Definition post_qSt : relativeMonadMorphism (ord_functor_id _) smPhi
  (product_rmon unarySt1 unarySt2) State_squ := mkRelMonMorph  _ _ _ _ _ _ _.
  Next Obligation.
    easy.
  Defined.

  (*Def of qSt now. qSt : Fr[St]^2 → StT(choice_incl^2)*)
  Definition qSt  :=
    rlmm_comp _ _ _ _ _ _ _ pre_qSt post_qSt.

  (*And now we can define the computational lift for state*)
  Definition lift_of_statecomp := rlmm_comp _ _ _ _ _ _ _ qSt stT_eta_Frp_squ.

  Goal True.
    pose (bla := stT_eta_Frp_squ). cbn in bla.

End LiftOfStateComp.


(*Next we define a relational effect observation for state *)
(*as: θSt := stT(η^W) after qSt*)
Section StateEffObs.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).

  Context {S1 S2 : choiceType}.


  Let StT_W := AdjTransform WRelProp _ _ (Chi_CodomainStateAdj S1 S2).

  Let eta_WRelProp := etaAsRmm WRelProp.

  (*We have to state transform the above*)
  (* Check eta_WRelProp. *)
  
  
  





