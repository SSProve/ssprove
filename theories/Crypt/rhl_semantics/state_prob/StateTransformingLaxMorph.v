(* From Coq Require Import Program.Wf. *)
From Coq Require Import Relation_Definitions.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Mon Require Import SPropBase.
From mathcomp Require Import all_ssreflect (*boolp*).
From Crypt Require Import Axioms OrderEnrichedRelativeAdjunctions LaxFunctorsAndTransf LaxMorphismOfRelAdjunctions TransformingLaxMorph OrderEnrichedRelativeAdjunctionsExamples ThetaDex SubDistr Theta_exCP ChoiceAsOrd only_prob.FreeProbProg UniversalFreeMap RelativeMonadMorph_prod LaxComp.
(* From Crypt Require Import only_prob.Rules. *)

Import SPropNotations.

(*In this file we transform the lax relative monad morphism thetaDex : FreeProb² → Wrelprop
into a stateful effect observation stT_thetaDex : StT(FreeProb²) → StT(Wrelprop)*)

(*
We also subsequently make the domain of stT_thetaDex free by precomposing with a morphism
with type FreeStateProb² → StT(FreeProb²)
*)

Section StT_thetaDex_definition.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).


  (*thetaDex filled with the relevant parameters*)
  Let myThetaDex :=  @thetaDex probE rel_choiceTypes chEmb prob_handler.

  Context {S1 S2 : choiceType}.
  Let TingAdj1_0 := Chi_DomainStateAdj S1 S2.
  Let TingAdj2_0 :=  Chi_CodomainStateAdj S1 S2.

  Let myJMWprod :=
    @RelativeMonadMorph_prod.JMWprod _ _ (ord_functor_id TypeCat) _ _ (ord_functor_id TypeCat).

  Program Definition state_beta' :  lnatTrans
    (lord_functor_comp (strict2laxFunc (binaryToTheS S1 S2))
       (strict2laxFunc (ord_functor_comp myJMWprod Jprod)))
    (lord_functor_comp (strict2laxFunc (ord_functor_comp myJMWprod Jprod))
       (strict2laxFunc (ToTheS_OrdCat S1 S2))) :=
    mkLnatTrans _ _.
  Next Obligation.
    move=> [A1 A2]. simpl.
    unshelve econstructor.
    move=> [g1 g2]. unshelve econstructor.
    move=> [s1 s2]. exact ⟨ g1 s1 , g2 s2 ⟩.
    cbv. move=> x y. move=> Hxy. destruct Hxy. reflexivity.
    cbv. move=> x y. move=> Hxy. move=> [s1 s2]. destruct Hxy. reflexivity.
  Defined.

  (*this is a morphism between the transformed adjunctions. see rlmm_from_lmla below
   to conclude the def of stT_thetaDex*)
  Program Definition stT_thetaDex_adj :=
    Transformed_lmla myThetaDex TingAdj1_0 TingAdj2_0 state_beta' _ _.
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

  Definition stT_thetaDex := rlmm_from_lmla stT_thetaDex_adj.


End StT_thetaDex_definition.

Section GetDomainAndCodomain.
  Context {C D1 D2 : ord_category} {J1 : ord_functor C D1} {J12 : ord_functor D1 D2} {J2 : ord_functor C D2}
          {phi : natIso J2 (ord_functor_comp J1 J12)} (psi := ni_inv phi)
          {M1 : ord_relativeMonad J1} {M2: ord_relativeMonad J2}.


  Definition rlmm_domain (smTheta :  relativeLaxMonadMorphism J12 phi M1 M2)
    : ord_relativeMonad J1
    := M1.
  Definition rlmm_codomain (smTheta :  relativeLaxMonadMorphism J12 phi M1 M2)
    : ord_relativeMonad J2
    := M2.

End GetDomainAndCodomain.


(*
Here we build a unary choiceType relative monad, free, with a stateful-probabilistic
signature.
*)
Section FreeStateProbMonad.
  (*some context for the probabilistic signature*)
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).


  (*what about the state signature?*)
  Context (S : choiceType). (*the set of states is itself a choiceType*)
    (*a state event is either a gett or a putt. If it is a gett, we expect the environement
     to yield a state after we issue the gett command. If it is a putt, we have to
     specify a new state s:S in order to overwrite the current state. No information
     is returned by the environement after we issue this command (hence the unit type)*)
  Inductive stateE : Type -> Type :=
  |gett : stateE S
  |putt : S -> stateE unit.

  (*Lemma S_vs_unit : forall (x : stateE unit), x = gett -> S = unit_choiceType.*)


  (*In terms of operations and arities...*)
  (*how to build the type of all (putt s) operations?*)
  Definition state_ops := sum (stateE S) (stateE unit).
  (*what about arities*)
  Program Definition state_ar : state_ops -> choiceType := fun sop =>
    match sop with
    |inl _ => S
    |inr _ => unit_choiceType
    end.

  (*this is a free choiceType relative monad with a stateful signature.*)
  (* Check rFree state_ops state_ar. *)


  (*Now how can we combine state and probabilities?*)
    (*operations are either stateful or probabilistic...*)
  Let prob_ops :=  Prob_ops_collection probE rel_choiceTypes chEmb.
  Definition ops_StP := sum state_ops prob_ops.

    (*arities of an operation stpOp: is it stateful or probabilistic? answer is
     given accordingly*)
  Let prob_ar :=  Prob_arities probE rel_choiceTypes chEmb.
  Definition ar_StP : ops_StP -> choiceType := fun stpOp =>
    match stpOp with
    |inl sop => state_ar sop
    |inr probop => prob_ar probop
    end.

  (*Here is our free choiceType relative monad with a stateful probabilistic signature*)
  Definition FrStP := rFree ops_StP ar_StP.


End FreeStateProbMonad.

(*Now we build a relative monad morphism from FrStP to StT(Frp). In other words
we interpret the stateful part of the signature of FrStP, but not the probabilistic
one*)
Section UnaryInterpretState.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.

  Context {S : choiceType}.


  (*The domain of the intended morphism is FrStP ...*)
  Let FrStP_filled := @FrStP probE rel_choiceTypes chEmb S.


  (*The codomain is StT(Frp)*)

  Let prob_ops :=  Prob_ops_collection probE rel_choiceTypes chEmb.
  Let prob_ar :=  Prob_arities probE rel_choiceTypes chEmb.

  Definition Frp :=  rFree prob_ops prob_ar.
  Let myLflat :=  unaryTimesS1 S.
  Let myR := ToTheS S.
  Notation FrpF := (rFreeF prob_ops prob_ar).


  Program Definition unaryStTransfromingAdj :
  leftAdjunctionSituation choice_incl (ord_functor_comp myLflat choice_incl) myR :=
    mkNatIso _ _ _ _ _ _ _.
  Next Obligation. (*ni_map*)
    move=> [A T]. simpl. unshelve econstructor.
      move=> g a s. exact (g (a,s)).
      cbv. move=> g1 g2. move=> Hg12. move=> a.
      apply boolp.funext. move=> s.
      move: Hg12 => /(_ (a,s)) Hg12.
      assumption.
  Defined.
  Next Obligation. (*ni_inv*)
    move=> [A T]. simpl. unshelve econstructor.
    move=> g [a s]. exact (g a s).
    cbv. move=> g1 g2. move=> Hg12. move=> [a s].
    move: Hg12 => /(_ a) Hg12.
    destruct Hg12. reflexivity.
  Defined.
  Next Obligation.
    move=> [A T]. move=> [A' T'].
    move=> [p q]. simpl in *.
    apply sig_eq. simpl. apply boolp.funext. move=> g.
    apply boolp.funext. move=> a'. apply boolp.funext.
    move=> s. simpl.
    unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A T].
    apply sig_eq. simpl.
    apply boolp.funext. move=> g. cbv.
    apply boolp.funext. move=> a. reflexivity.
  Qed.
  Next Obligation.
    move=> [A T].
    apply sig_eq. simpl.
    apply boolp.funext. move=> g. cbv.
    apply boolp.funext. move=> [a s].
    reflexivity.
  Qed.


  (*This is StT(Frp)*)
  Definition stT_Frp := AdjTransform Frp myLflat myR unaryStTransfromingAdj.

  (*Let us define get and put in this monad ...*)
  Let retrFree_filled (X:choiceType) := retrFree prob_ops prob_ar X.

  Definition getStP : stT_Frp S :=
    fun s : S => retrFree_filled (F_choice_prod_obj ⟨ S, S ⟩) (s, s).

  Definition putStP : S -> stT_Frp unit_choiceType := fun new_s old_s =>
    retrFree_filled (F_choice_prod ⟨ unit_choiceType, S ⟩) (tt, new_s).


  Definition probopStP {T : rel_choiceTypes} : probE (chEmb T) -> stT_Frp (chEmb T).
    move=> probop. move=> s. simpl.
    unshelve eapply ropr.
      unshelve econstructor. exact T. exact probop.
    simpl. move=> x. eapply retrFree_filled. simpl. exact ( (x,s) ).
  Defined.

  
  Let ops_StP_filled :=  @ops_StP probE rel_choiceTypes chEmb S.
  Let ar_StP_filled := @ar_StP probE rel_choiceTypes chEmb S.
  

  Definition sigMap : forall op : ops_StP_filled, stT_Frp( ar_StP_filled op ).
  move=> op. cbv in op.
  move: op => [[aget|aput]|aprobop].
    (*get case*)
    unfold ar_StP_filled. unfold ar_StP. unfold state_ar.
    move: aget=> [|].
    - exact getStP. (*true get*)
    - move=> new_s. move=> old_s. simpl. apply retrFree_filled. exact (old_s,new_s). (*flase get*)
    (*put case*)
    unfold ar_StP_filled. unfold ar_StP. unfold state_ar.
    move: aput=> [|].
      - simpl. move=> s. apply retrFree_filled. exact (tt,s). (*false put*)
      - exact putStP. (*true put*)
    (*probop case*)
    move: aprobop => [X op].
    cbn. exact (probopStP op).
  Defined.

  Definition unaryIntState
  : relativeMonadMorphism _ _ (FrStP_filled) stT_Frp
  := @outOfFree (ops_StP S) (ar_StP S) stT_Frp sigMap.


End UnaryInterpretState.



(*now we square this morphism to get a relative monad morphism FrStP² → stT(Frp)²*)
Section SquareUnaryIntState.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.

  Context {S1 S2 : choiceType}.

  Let unaryIntState_filled_left := @unaryIntState probE rel_choiceTypes chEmb S1.
    Let unaryIntState_filled_right := @unaryIntState probE rel_choiceTypes chEmb S2.
  Definition preInterpretState :=
  prod_relativeMonadMorphism
    unaryIntState_filled_left unaryIntState_filled_right.

End SquareUnaryIntState.


(*We also need an additional bit stT(Frp)² → stT(Frp²), the latter being the domain
of stT_thetaDex *)
Section StT_vs_squaredMonads.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.

  Context {S1 S2 : choiceType}.
  Context {prob_handler : forall (T:choiceType),
    probE T -> SDistr T}.



  Let preInterpretState_filled := @preInterpretState probE rel_choiceTypes chEmb S1 S2.
  Let stT_thetaDex_filled := @stT_thetaDex probE rel_choiceTypes chEmb prob_handler S1 S2.

  (*domain of the additional morphism*)
  Let squOf_stT_Frp := rlmm_codomain preInterpretState_filled.
  (*and codomain*)
  Let stT_squOf_Frp := rlmm_domain stT_thetaDex_filled.

  (*base square*)
  Definition BinaryTrivialChi :
  natIso ( prod_functor choice_incl choice_incl )
         (ord_functor_comp (prod_functor choice_incl choice_incl)
                           (ord_functor_id (prod_cat TypeCat TypeCat))).
  apply natIso_sym. apply ord_functor_unit_right.
  Defined.

  Notation Frpp := (rFreeF (Prob_ops_collection probE rel_choiceTypes chEmb)
      (Prob_arities probE rel_choiceTypes chEmb)).

  Program Definition additionalIntState :
  relativeMonadMorphism (ord_functor_id _) BinaryTrivialChi squOf_stT_Frp stT_squOf_Frp :=
    mkRelMonMorph (ord_functor_id _) BinaryTrivialChi squOf_stT_Frp stT_squOf_Frp _ _ _.
  Next Obligation.
    move=> [A1 A2]. unshelve econstructor.
      easy.
      easy.
  Defined.

End StT_vs_squaredMonads.


(*And now we are finally ready to define the intended theta *)
Section MakeTheDomainFree.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.

  Context {S1 S2 : choiceType}.
  Context {prob_handler : forall (T:choiceType),
    probE T -> SDistr T}.

  Let preInterpretState_filled := @preInterpretState probE rel_choiceTypes chEmb S1 S2.
  Let addIntState_filled := @additionalIntState probE rel_choiceTypes chEmb S1 S2 prob_handler.
  Let stT_thetaDex_filled := @stT_thetaDex probE rel_choiceTypes chEmb prob_handler S1 S2.

  (*FrStP² → stT(Frp²) part*)
  Definition justInterpState :=
  rlmm_comp _ _ _ _ _ _ _ preInterpretState_filled addIntState_filled.

  (*the other part is stT_thetaDex : stT(Frp²) → Wstrelprop*)
  (* Check stT_thetaDex_filled. *)

  (*we now combine those two morphisms *)
  Definition thetaFstdex := rlmm_comp _ _ _ _ _ _ _ justInterpState stT_thetaDex_filled.

  (*
    Fstdex because:
       start with theta dex = θex ∘ θdens : Frp² → Wrelprop
       then state transform ; stT( θdex ) : StT( Frp² ) → WStRelprop
       then make the domain free ; θFstdex : FrStP ² → WStRelprop

  *)

  (*thetaFdex : FrStP² → Wrelprop *)
(*
  Eval hnf in rlmm_domain thetaFstdex.
  Eval hnf in rlmm_codomain thetaFstdex.
*)

End MakeTheDomainFree.

