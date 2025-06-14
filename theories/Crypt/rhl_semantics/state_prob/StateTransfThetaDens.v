From Stdlib Require Import RelationClasses.
From SSProve.Mon Require Import SPropBase.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import ChoiceAsOrd OrderEnrichedRelativeAdjunctions OrderEnrichedRelativeAdjunctionsExamples TransformingLaxMorph SubDistr Theta_dens LaxFunctorsAndTransf UniversalFreeMap FreeProbProg StateTransformingLaxMorph LaxComp.

Import SPropNotations.

(*
In this file we state transform this morphism
θdens : Frp → Sdistr
into
StT(θdens) : StT(Frp) → StT(SDistr)

We also subsequently make its domain free
θFstd : FrStP → StT(Frp) → stT(SDistr)
*)

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


Section StT_unaryThetaDens.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {choice_type : Type}
          {chElement : choice_type -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).

  Context {S : choiceType}.

  (*we wish to transform this monad morphism*)
  Let θdens_filled :=
  @unary_theta_dens.

  (*domain and codomain*)
  Let Frp := rlmm_domain θdens_filled.
  (* Eval hnf in rlmm_codomain θdens_filled. (*SDistr*) *)



  (*state transform the domain*)

  Program Definition unaryStateTingAdj :
  leftAdjunctionSituation choice_incl
         (ord_functor_comp (unaryTimesS1 S) choice_incl)
         (ToTheS S) :=
    mkNatIso _ _ _ _ _ _ _.
  Next Obligation.
    move=> [A X]. unshelve econstructor.
      simpl. move=> g a s. exact (g (a,s)).
      move=> g g'. simpl in g. simpl in g'.
      move=> Hg. unfold extract_ord. simpl.
      move=> a.
      unfold extract_ord in Hg. simpl in Hg.
      apply boolp.funext. move=> s.
      apply Hg.
  Defined.
  Next Obligation.
    move=> [A X]. unshelve econstructor.
      simpl. move=> g. move=> [a s]. exact (g a s).
      simpl. move => g g'.
      unfold extract_ord. simpl.
      move=> Hg. move=> [a s].
      specialize (Hg a). destruct Hg.
      reflexivity.
  Defined.
  Next Obligation.
    move=> [A X] [A' X']. move=> [fA fX]. simpl in *.
    apply sig_eq. simpl. apply boolp.funext. move=> g.
    apply boolp.funext. move=> a'. apply boolp.funext. move=> s.
    simpl.
    rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A X].
    apply sig_eq. simpl. apply boolp.funext. move=> g.
    simpl. apply boolp.funext. move=> a. reflexivity.
  Qed.
  Next Obligation.
    move=> [A X].
    apply sig_eq. simpl. apply boolp.funext. move=> g.
    simpl. apply boolp.funext. move=> [a s]. reflexivity.
  Qed.

  Program Definition unaryStateBeta' :
  lnatTrans (lord_functor_comp
                      (strict2laxFunc (ToTheS S))
                      (strict2laxFunc (ord_functor_id TypeCat)))
            (lord_functor_comp
                      (strict2laxFunc (ord_functor_id TypeCat))
                      (strict2laxFunc (ToTheS S))) :=
    mkLnatTrans _ _.

  Program Definition stT_thetaDens_adj :=
  Transformed_lmla θdens_filled unaryStateTingAdj unaryStateTingAdj unaryStateBeta' _ _.
  Next Obligation.
    move=> A Y. move=> g.
    apply boolp.funext. move=> [ a s]. cbv. reflexivity.
  Qed.

  Definition stT_thetaDens :=  rlmm_from_lmla stT_thetaDens_adj.

End StT_unaryThetaDens.



Section MakeTheDomainFree.
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {choice_type : Type}
          {chElement : choice_type -> choiceType}.
  Context {prob_handler : forall (T:choiceType),
    probE T -> SDistr T}.

  Context {S : choiceType}.

  Let unaryIntState_filled :=
  @unaryIntState S.

  Let stT_thetaDens_filled :=
  @stT_thetaDens S.



  (*an auxiliary morphism to connect the dots*)
  Program Definition bridgg :
  relativeMonadMorphism (ord_functor_id _) (trivialChi)
     (rlmm_codomain unaryIntState_filled)
     (rlmm_domain stT_thetaDens_filled) :=
    mkRelMonMorph _ _ _ _ _ _ _.

  (*now... unaryIntState_filled ; bridgg = ppre*)
  Let ppre := rlmm_comp _ _ _ _ _ _ _ (unaryIntState_filled) bridgg.

  (*and then ppre ; stT_thetaDens_filled*)
  Definition thetaFstd := rlmm_comp _ _ _ _ _ _ _ ppre stT_thetaDens_filled.


End MakeTheDomainFree.
