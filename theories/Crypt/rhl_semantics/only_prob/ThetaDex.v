From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import Theta_dens Theta_exCP SubDistr LaxComp ChoiceAsOrd RelativeMonadMorph_prod.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".

(*
we have at our disposal θex : SDistr² → Wrelprop . We turn this lax morphism
into θdex : FreeProb² → Wrelprop by precomposing it with θdens : FreeProb² → SDistr².
*)
Section ThetaDexDef.

  Let ltheta_dens :=  relativeMonadMorphism_to_lax _ _ _ _ theta_dens.

  Definition thetaDex := rlmm_comp _ _ _ _ _ _ _ ltheta_dens θ_morph.

End ThetaDexDef.
