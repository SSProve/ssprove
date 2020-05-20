(*********************************************************)
(**       Relational reasoning on ND                    **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality Arith.PeanoNat List.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads Monoid DijkstraMonadExamples.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

Set Primitive Projections.
Set Universe Polymorphism.

Section NDDs.

  Let M1 := NDSet.
  Let M2 := NDSet.

  Let Wun := @MonoContProp.

  Import SPropNotations.
  Import FunctionalExtensionality.

  Program Definition θNDD12 : MonadMorphism NDSet Wun := @mkMorphism M1 Wun (fun _ P => ⦑fun p => s∀ x, P x -> p x⦒) _ _.
  Next Obligation. cbv; intuition. Qed.
  Next Obligation. cbv; intuition. apply sig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. destruct H0; assumption. Qed.
  Next Obligation. cbv; intuition. apply sig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. Qed.

  Program Definition θforallrel :=
    commute_effObs Wun M1 M2 θNDD12 θNDD12 _.
  Next Obligation.
    cbv; intuition; apply sig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. Qed.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θforallrel _ _ c1 c2 w).

  Program Definition demonic_left_rule_w {A2 : Type} (a2:A2) : dfst (Commutativity.Wrel Wun ⟨ bool, A2 ⟩). apply (exist _ (fun post => post ⟨true, a2⟩ s/\ post ⟨false, a2⟩)). cbv; intuition.
  Defined.

  Lemma demonic_left_rule {A2 : Set} (a2:A2) :
    ⊨ pick_set ≈ ret a2 [{ demonic_left_rule_w a2 }].
  Proof. cbv ; intuition. destruct H0; destruct x; assumption. Qed.

  Lemma demonicInterpretationExplicitFormula A1 A2 c1 c2 (post : A1 × A2 -> Prop):
    ((θforallrel ⟨A1, A2⟩)∙1 ⟨c1,c2⟩)∙1 post s<-> forall a1 a2, c1 a1 -> c2 a2 -> post ⟨a1,a2⟩.
  Proof. cbv; intuition. Qed.

End NDDs.
