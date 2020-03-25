From mathcomp Require Import all_ssreflect all_algebra reals.


Import ssrnum.Num.Theory.
Local Open Scope ring_scope.

Parameter (R:realType).
Parameter  (absord : R -> R -> bool). 
Parameter (unlock_absord : absord = (fun x y : R => x <= y)).

From Coq Require Export Logic.ProofIrrelevance.
From Coq Require Export FunctionalExtensionality.

(*now an equivalence between SProp and Prop. An equivalence of
truth collections.*)
Parameter (Prop2SProp : Prop -> SProp).
Parameter (SProp2Prop : SProp -> Prop).

Axiom (PSP_retr :  forall Q : Prop , SProp2Prop (Prop2SProp Q) = Q ).
Axiom (PSP_sect : forall Q' : SProp, Prop2SProp( SProp2Prop Q' ) = Q').

Axiom (Prop2SProp_truthMorphism_leftRight :
forall Q : Prop, Q -> (Prop2SProp Q)).
Axiom (Prop2SProp_truthMorphism_rightLeft :
forall Q : Prop, (Prop2SProp Q) -> Q).

Axiom (SProp2Prop_truthMorphism_leftRight :
forall Q' : SProp, Q' -> SProp2Prop Q').
Axiom (SProp2Prop_truthMorphism_rightLeft :
forall Q' : SProp, SProp2Prop Q' -> Q').
