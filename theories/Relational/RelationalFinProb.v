(*********************************************************)
(**       Relational reasoning on Finite Probabilities  **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality Arith.PeanoNat List.
From mathcomp Require Import all_ssreflect all_algebra reals distr.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads Monoid DijkstraMonadExamples.
From Relational Require Import RelativeMonads RelativeMonadExamples GenericRulesSimple Commutativity.

From Mon.sprop Require Import  FiniteProbabilities.

Section RelFinProb.
  Context (R:realType).

  Let M1 := ProbM R.
  Let M2 := ProbM R.

  Let WI := WI R.
  Let Wrel := Wrel WI.

  Definition θRelProb :=
    let x := fromFreeCommute WI (wopProb R) (wopProb R) (self_commute R) in
    commute_effObs WI M1 M2 _ _ x.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θRelProb _ _ c1 c2 w).

  Import GRing.Theory Num.Theory.
  Local Open Scope ring_scope.

  Definition toss1 (p : unit_interval R) : M1 bool := op (ProbAr _) p.
  Definition toss2 (p : unit_interval R) : M2 bool := op (ProbAr _) p.

  Import SPropNotations.

  Hint Resolve I_ge0.
  Hint Resolve I_le1.

  Program Definition toss1_spec {A2} (a2:A2) (p:unit_interval R) : dfst (Wrel ⟨bool,A2⟩) :=
    ⦑fun post => barycentric_sum R p (post ⟨true,a2⟩) (post ⟨false, a2⟩)⦒.
  Next Obligation.
    rewrite /Irel /=; apply:its_true_anyway.
    rewrite ler_add // ler_pmul //; try by apply since_its_true, H.
    by rewrite (I_ge0 _ (negI _ p)).
  Qed.

  Program Definition toss2_spec {A1} (a1:A1) (p:unit_interval R) : dfst (Wrel ⟨A1,bool⟩) :=
    ⦑fun post => barycentric_sum R p (post ⟨a1,true⟩) (post ⟨a1,false⟩)⦒.
  Next Obligation.
    rewrite /Irel /=; apply:its_true_anyway.
    rewrite ler_add // ler_pmul //; try by apply since_its_true, H.
    by rewrite (I_ge0 _ (negI _ p)).
  Qed.

  Lemma coin_toss_rule1 {A2} : forall p (a2:A2),
      ⊨ toss1 p ≈ ret a2 [{ toss1_spec a2 p }].
  Proof.
    move=> *; rewrite /semantic_judgement=> /= post; by apply its_true_anyway.
  Qed.

  Lemma coin_toss_rule2 {A1} : forall p (a1:A1),
      ⊨ ret a1 ≈ toss2 p [{ toss2_spec a1 p }].
  Proof.
    move=> *; rewrite /semantic_judgement=> /= post; by apply its_true_anyway.
  Qed.


End RelFinProb.