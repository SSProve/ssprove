(** Tactics to help write packages

  In this module we define handy tactics to deal with obligations generated
  by packages operations and packages in general.

  - in_fset_auto
    This tactic should solve goals of the form
    x \in S
    where S is a concrete finite set that contains x.

  - inseq_try
    This tactic should solve goals of the form
    x \in S
    where S is a sequence that contains x syntactically.

  - inset_try
    Similar to inseq_try but for fset.
    It is slightly stronger than in_fset_auto in that it also works in case
    the mem predicate doesn't compute in itself.

  - package_obtac
    This tactic can be used as an obligation tactic for Program or Equations
    mode.
    It can be set with
    Obligation Tactic := package_obtac.

**)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype seq eqtype choice.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset.
From Crypt Require Import Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

Require Equations.Prop.DepElim.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Ltac in_fset_auto :=
  rewrite extructures.fset.in_fset ; reflexivity.

(* Succeeds for x \in S if S contains syntactically x, S seq *)
Ltac inseq_try :=
  apply/orP ; first [
    left ; apply/eqP ; reflexivity
  | right ; inseq_try
  ].

Ltac inset_try :=
  rewrite in_fset ; inseq_try.

Ltac package_obtac :=
  (* Or try (Tactics.program_simpl; fail); simpl ? *)
  Tactics.program_simplify ;
  CoreTactics.equations_simpl ;
  try Tactics.program_solve_wf ;
  try in_fset_auto ;
  try inset_try.

Module PackageTactics (π : RulesParam).

  Include (PkgNotation π).
  Include (DerivedRules π).

  (* With the following, one can rewrite under λ with setoid_rewrite *)

  Instance pointwise_eq_ext {A B : Type} {RB : relation B} (sb : subrelation RB eq) :
    subrelation (pointwise_relation A RB) eq.
  Proof.
    intros f g Hfg.
    apply functional_extensionality.
    intro x. apply sb. apply Hfg.
  Qed.

  (** Rewriting under binders with setoid_rewrite *)

  Instance opr_morphism (A : choiceType) o :
    Proper (eq ==> pointwise_relation (tgt o) eq ==> eq) (@opr A o).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Instance getr_morphism (A : choiceType) l :
    Proper (pointwise_relation (Value l.π1) eq ==> eq) (@getr A l).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Instance sampler_morphism (A : choiceType) o :
    Proper (pointwise_relation (Arit o) eq ==> eq) (@sampler A o).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Instance bind_morphism (A B : choiceType) :
    Proper (eq ==> pointwise_relation A eq ==> eq) (@bind A B).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Definition tac_mark {A} (x : A) := x.
  Definition tac_intro_mark {A} (x : A) := x.

  Ltac mark_abstract_packages :=
    repeat match goal with
    | |- context [ mkpackage ?p ?h ] =>
      let h' := fresh "h" in
      set (h' := h) ;
      let p' := fresh "p" in
      set (p' := mkpackage p h') ;
      clearbody h' ;
      change (mkpackage p h') with (tac_mark (mkpackage p h')) in p' ;
      lazymatch type of h' with
      | ?T => change T with (tac_intro_mark T) in h'
      end
    end.

  Ltac unmark_packages :=
    repeat match goal with
    | p := tac_mark ?t |- _ =>
      change (tac_mark t) with t in p ;
      subst p
    end.

  Ltac revert_tac_intro :=
    repeat match goal with
    | h : tac_intro_mark ?t |- _ =>
      revert h
    end.

  Ltac package_before_rewrite :=
    mark_abstract_packages ;
    unmark_packages ;
    revert_tac_intro.

  Ltac intro_tac_intro :=
    repeat match goal with
    | |- ∀ h : tac_intro_mark ?A, _ =>
      intro h ;
      change (tac_intro_mark A) with A in h
    end.

  Ltac package_after_rewrite :=
    intro_tac_intro.

End PackageTactics.
