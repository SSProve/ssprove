(*********************************************************)
(**       Relational reasoning on ND (angelic)          **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality Arith.PeanoNat List.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads Monoid DijkstraMonadExamples.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

Set Primitive Projections.
Set Universe Polymorphism.

Section NDAs.

  Let M1 := NDSet.
  Let M2 := NDSet.

  Let Wun := @MonoContSProp.

  Import SPropNotations.
  Import FunctionalExtensionality.

  Program Definition θNDA12 : MonadMorphism NDSet Wun := @mkMorphism M1 Wun (fun _ P => ⦑fun p => s∃ x, P x s/\ p x⦒) _ _.
  Next Obligation. cbv; intuition. destruct H1. exists x0. intuition. Qed.
  Next Obligation. cbv; intuition. apply Ssig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. destruct p0; assumption. Qed.
  Next Obligation. cbv; intuition. apply Ssig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. Qed.

  Program Definition θexistsrel :=
    commute_effObs Wun M1 M2 θNDA12 θNDA12 _.
  Next Obligation.
    cbv; intuition; apply Ssig_eq; simpl; extensionality p; apply SPropAxioms.sprop_ext; firstorder. Qed.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θexistsrel _ _ c1 c2 w).

  Program Definition angelic_rule_w : dfst (Commutativity.Wrel Wun ⟨ bool, bool ⟩). apply (Sexists _ (fun post => post ⟨true, true⟩ s\/ post ⟨true, false⟩ s\/ post ⟨false, true⟩ s\/ post ⟨false, false⟩)). cbv; intuition.
  Defined.

  Lemma angelic_rule :
    ⊨ pick_set ≈ pick_set [{ angelic_rule_w }].
  Proof. cbv ; intuition; firstorder. Qed.
End NDAs.
