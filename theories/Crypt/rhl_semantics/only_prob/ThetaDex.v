From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import Theta_dens Theta_exCP SubDistr LaxComp ChoiceAsOrd RelativeMonadMorph_prod.
From mathcomp Require Import all_ssreflect.

(*
we have at our disposal θex : SDistr² → Wrelprop . We turn this lax morphism
into θdex : FreeProb² → Wrelprop by precomposing it with θdens : FreeProb² → SDistr².
*)
Section ThetaDexDef.
  (*some context for theta_dens*)
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).


  Let theta_dens_filled :=  @theta_dens probE rel_choiceTypes chEmb prob_handler.
  Let ltheta_dens :=  relativeMonadMorphism_to_lax _ _ _ _ (theta_dens_filled).

  Definition thetaDex := rlmm_comp _ _ _ _ _ _ _ ltheta_dens θ_morph.


End ThetaDexDef.
