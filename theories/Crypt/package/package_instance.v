(** Useful instance of packages with uniform distributions and assert

  This module provides an instance to the functor for use in the examples.
  This is a temporary measure pending the removal of functors in packages.

  This also introduces useful lemmata and rules as well as syntax for uniform
  distributions and assert.

  When the large-scale refactoring is concluded, this file should go away,
  its contents distributed, mainly in pkg_rhl.

*)

From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.
From Crypt Require Import Prelude Package RulesStateProb SubDistr
  UniformStateProb ChoiceAsOrd FreeProbProg.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.
Set Keyed Unification.

(* Empty instance for probE *)
Inductive probEmpty : Type → Type :=.

Module genparam <: RulesParam.

  Definition probE : Type → Type := probEmpty.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intros T v. inversion v.
  Defined.

End genparam.

Module Rules := DerivedRulesUniform genparam.
Export Rules.

Module Package := Package_Make myparamU.
Export Package.

Import PackageNotation.
#[local] Open Scope package_scope.

(** Syntax for uniform distributions

  TODO: See if we don't want something more explicit like [uniform].

*)
Definition U (i : nat) `{Positive i} : Op :=
  existT _ ('fin i) (inl (Uni_W (mkpos i))).

(** Rules on uniform distributions *)

Lemma r_uniform_bij :
  ∀ {A₀ A₁ : ord_choiceType} i j `{Positive i} `{Positive j} pre post f
    (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
    bijective f →
    (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄
      x ← sample U i ;; c₀ x ≈
      x ← sample U j ;; c₁ x
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ i j pi pj pre post f c₀ c₁ bijf h.
  rewrite rel_jdgE.
  change (repr (sampler (U ?i) ?k))
  with (bindrFree (@Uniform_F (mkpos i) heap_choiceType) (λ x, repr (k x))).
  eapply bind_rule_pp.
  - eapply Uniform_bij_rule. eauto.
  - intros a₀ a₁. simpl.
    rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
    move: e => /eqP e. subst.
    eapply rpre_weaken_rule. 1: eapply h.
    intros h₀ h₁. simpl. intros [? ?]. subst. auto.
Qed.