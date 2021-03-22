From Mon Require Import
     FiniteProbabilities
     SPropMonadicStructures
     SpecificationMonads
     MonadExamples
     SPropBase.

From Relational Require Import
     OrderEnrichedCategory
     OrderEnrichedRelativeMonadExamples
     Commutativity
     GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings Theta_dens
  Theta_exCP LaxComp FreeProbProg RulesStateProb UniformDistrLemmas chUniverse
  pkg_core_definition pkg_composition pkg_rhl Package Prelude
  StateTransformingLaxMorph.
Set Warnings "-custom-entry-overriden".
From Crypt Require Import pkg_notation.
Set Warnings "custom-entry-overriden".
From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.

Import SPropNotations.
Import Num.Theory.

Local Open Scope ring_scope.

(* general Rules + Rules for uniform distributions over a finite
    family of non-empty finite types *)

(* #[local] Definition FrStP := MyRulesU.FrStP.
#[local] Definition θ0 { S } { A } (c : FrStP S A) := @MyRulesU.θ0 S A c.
#[local] Definition θ_dens { S } { X } := @MyRulesU.θ_dens S X. *)

(* Uniform distribution over F *)
Definition Uniform_F { i : positive } { S : choiceType } : @FrStP S (chFin i).
Proof.
  unshelve eapply ropr.
  { apply samplee. exists (chFin i).
    eapply @uniform_F. exists 0%N. apply i.
  }
  rewrite /= => w.
  constructor.
  exact w.
Defined.

Definition Fail { S : choiceType } : @FrStP S chUnit.
Proof.
  unshelve eapply ropr.
  { apply samplee. exists chUnit. exact dnull. }
  rewrite /= => w.
  constructor.
  exact w.
Defined.

Definition Assert {S : choiceType} (b : bool) : @FrStP S chUnit.
Proof.
  destruct b.
  - constructor.
    exact Datatypes.tt.
  - exact Fail.
Defined.

Lemma destruct_pair_eq {R : ringType} {A B : eqType} {a b : A} {c d : B}
  : ((a, c) == (b, d))%:R = (a == b)%:R * (c == d)%:R :> R.
Proof.
  destruct (a == b) eqn:ab, (c == d) eqn:cd.
  all: cbn; rewrite ab cd /=; try rewrite GRing.mulr1; try rewrite GRing.mulr0; reflexivity.
Qed.

Import RSemanticNotation.
#[local] Open Scope rsemantic_scope.

Theorem _assert_rule { S1 S2 : choiceType }  (b b' : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = b' ⦄ (Assert b) ≈ (Assert b') ⦃ fun _ _ => b = true /\ b' = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b, b'.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
  - discriminate.
  - exists dnull.
    split.
    + unfold coupling.
      split.
      * unfold SDistr_bind.
        unfold lmg. apply distr_ext.
        move => x0. rewrite !dlet_null.
        reflexivity.
      * unfold SDistr_bind.
        unfold rmg. apply distr_ext.
        move => x0. rewrite !dlet_null.
        reflexivity.
    + intros [a1 s1'] [a2 s2'].
      rewrite dnullE.
      rewrite mc_1_10.Num.Theory.ltrr.
      auto.
Qed.

Theorem assert_rule { S1 S2 : choiceType }  (b b' : bool)
        {pre : S1 * S2 -> Prop} {post : chUnit * S1 -> chUnit * S2 -> Prop}
        {pre_bb : forall st, pre st -> b = b'}
        {post_bb : forall st1 st2, b = true /\ b' = true -> post st1 st2} :
  ⊨ ⦃ pre ⦄ (Assert b) ≈ (Assert b') ⦃ post ⦄.
Proof.
  pose H := _assert_rule b b'.
  eapply pre_weaken_rule.
  eapply post_weaken_rule.
  apply H.
  - intros p1 p2 [Hb Hb'].
    apply post_bb.
    split; subst; reflexivity.
  - intros p1 p2 Hpre. simpl.
    apply (pre_bb (p1, p2)).
    assumption.
Qed.

Theorem assert_rule_left { S1 S2 : choiceType }  (b : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = true ⦄ (Assert b) ≈ (retF Datatypes.tt) ⦃ fun _ _ => b = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
Qed.

Theorem assert_rule_right { S1 S2 : choiceType }  (b : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = true ⦄ (retF Datatypes.tt) ≈ (Assert b) ⦃ fun _ _ => b = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
Qed.

Open Scope fset_scope.
