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
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq eqtype
  choice.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Prelude Axioms pkg_core_definition
  pkg_composition pkg_notation choice_type fmap_extra.
From Stdlib Require Import Utf8 Setoids.Setoid Classes.Morphisms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Import PackageNotation.
#[local] Open Scope package_scope.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Ltac package_obtac :=
  (* Or try (Tactics.program_simpl; fail); simpl ? *)
  Tactics.program_simplify ;
  CoreTactics.equations_simpl ;
  try Tactics.program_solve_wf ;
  try fmap_solve.

(* With the following, one can rewrite under λ with setoid_rewrite *)

#[export] Instance pointwise_eq_ext {A B : Type} {RB : relation B} (sb : subrelation RB eq) :
  subrelation (pointwise_relation A RB) eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality.
  intro x. apply sb. apply Hfg.
Qed.

(** Rewriting under binders with setoid_rewrite *)

#[export] Instance opr_morphism (A : choiceType) o :
  Proper (eq ==> pointwise_relation (tgt o) eq ==> eq) (@opr A o).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance getr_morphism (A : choiceType) (l : Location) :
  Proper (pointwise_relation (Value l) eq ==> eq) (@getr A l).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance sampler_morphism (A : choiceType) o :
  Proper (pointwise_relation (Arit o) eq ==> eq) (@sampler A o).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance bind_morphism (A B : choiceType) :
  Proper (eq ==> pointwise_relation A eq ==> eq) (@bind A B).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance cmd_bind_morphism (A B : choiceType) :
  Proper (eq ==> pointwise_relation A eq ==> eq) (@cmd_bind A B).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance bindrFree_morphism (A B : choiceType) c k :
  Proper (eq ==> pointwise_relation A eq ==> eq) (@FreeProbProg.bindrFree c k A B).
Proof.
  simpl_relation.
  f_equal. apply functional_extensionality. auto.
Qed.

Lemma valid_empty_package :
  ∀ L I,
    ValidPackage L I [interface] emptym.
Proof.
  intros L I.
  split; [ split |].
  - intros H. exfalso. apply (fhas_empty _ H).
  - intros [f H]. exfalso. apply (fhas_empty _ H).
  - intros n F x H. exfalso. apply (fhas_empty _ H).
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [::])) =>
  try (replace E with [interface] by eapply fset0E) ;
  eapply valid_empty_package
  : typeclass_instances ssprove_valid_db.

Lemma valid_package_cons :
  ∀ L I i A B f E p,
    ValidPackage L I (mkfmap E) (mkfmap p) →
    (∀ x, ValidCode L I (f x)) →
    ValidPackage L I (mkfmap ((i, (A, B)) :: E))
      (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros L I n A B f E p h c.
  split; [ split |].
  - move: o => [m [S T]].
    rewrite //= 2!setmE.
    destruct (m == n) eqn:e.
    + move: e => /eqP e o.
      noconf e. noconf o. by exists f.
    + destruct h as [he _].
      specialize (he (m, (S, T))).
      simpl in he.
      by rewrite he.
  - move: o => [m [S T]].
    rewrite //= 2!setmE.
    destruct (m == n) eqn:e.
    + intros [g H].
      by noconf H.
    + intros [g H].
      destruct h as [he _].
      specialize (he (m, (S, T))).
      simpl in he.
      rewrite he.
      by exists g.
  - intros m F x.
    rewrite //= setmE.
    destruct (m == n) eqn:e.
    + move: e => /eqP e o.
      noconf e. noconf o. apply c.
    + destruct h as [_ hi].
      apply hi.
Qed.

Lemma valid_package_cons_upto :
  ∀ L I i A B A' B' f E p,
    ValidPackage L I (mkfmap E) (mkfmap p) →
    (∀ x, ValidCode L I (f x)) →
    A = A' →
    B = B' →
    ValidPackage L I (mkfmap ((i, (A', B')) :: E))
      (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros L I i A B A' B' f E p hp hf eA eB. subst.
  eapply valid_package_cons. all: eauto.
Qed.

#[export] Hint Extern 100 =>
  shelve : ssprove_valid_db.

#[export] Hint Extern 2 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons ; [
  | intro
  ]
  : typeclass_instances ssprove_valid_db.

Lemma valid_scheme :
  ∀ A L I c,
    @ValidCode emptym [interface] A c →
    ValidCode L I c.
Proof.
  intros A L I c h.
  eapply valid_injectMap. 2: eapply valid_injectLocations.
  1-2: eapply fsub0map.
  apply h.
Qed.

Ltac choice_type_eq_prove :=
  lazymatch goal with
  | |- chProd _ _ = chProd _ _ => f_equal ; choice_type_eq_prove
  | |- chMap _ _ = chMap _ _ => f_equal ; choice_type_eq_prove
  | |- chOption _ = chOption _ => f_equal ; choice_type_eq_prove
  | |- chFin _ = chFin _ => f_equal ; apply positive_ext ; reflexivity
  | |- _ = _ => reflexivity
  end.

#[export] Hint Extern 4 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons_upto ; [
  | intro
  | choice_type_eq_prove
  | choice_type_eq_prove
  ]
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 10 (ValidCode ?L ?I (let u := _ in _)) =>
  cbv zeta
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 2 (ValidCode ?L ?I (match ?t with _ => _ end)) =>
  destruct t
  : typeclass_instances ssprove_valid_db.

Ltac ssprove_valid :=
  (unshelve typeclasses eauto with ssprove_valid_db) ; shelve_unifiable.
