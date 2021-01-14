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

  - program fold
    This tactic can be used to fold raw programs together with their validity
    proof to program syntax.

  - program setoid fold
    Variant of [program fold] which can go under binders (λ and the monadic
    operations).
    It is not well-optimised and it might be preferable to use the folding
    lemmata by hand, using setoid_rewrite.
    Here are a few examples

    setoid_rewrite fold_getr.
    unshelve setoid_rewrite fold_bind.

    In the case of bind, an extra proof has to be provided, hence the
    unshelve.

**)

From mathcomp Require Import ssreflect ssrbool eqtype seq eqtype choice.
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

  Include (PackageNotation π).
  Include (DerivedRules π).

  (* Ltac program_fold_one :=
    lazymatch goal with
    | context [ exist _ (_ret x) h ] =>
      rewrite fold_ret
    | context [ exist _ (_opr o x k) h ] =>
      rewrite fold_opr *)

  Ltac program_fold_pass :=
    change (exist (valid_program ?L ?I) (@_ret ?A ?x) ?h) with (@ret L I A x) ;
    change (exist (valid_program ?L ?I) (@_opr ?A ?o ?x ?k) ?h)
    with (@opr L I A o (valid_opr_in h) x (λ v, exist _ (k v) (valid_opr_k h v))) ;
    change (exist (valid_program ?L ?I) (@_getr ?A ?l ?k) ?h)
    with (@getr L I A l (valid_getr_in h) (λ x, exist _ (k x) (valid_getr_k h x))) ;
    change (exist (valid_program ?L ?I) (@_putr ?A ?l ?v ?k) ?h)
    with (@putr L I A l (valid_putr_in h) v (exist _ k (valid_putr_k h))) ;
    change (exist (valid_program ?L ?I) (@_sampler ?A ?op ?k) ?h)
    with (@sampler L I A op (λ x, exist _ (k x) (h x))).

  Ltac program_fold :=
    repeat program_fold_pass ;
    rewrite ?fold_ret ?fold_opr ?fold_getr ?fold_putr ?fold_sampler.

  Tactic Notation "program" "fold" :=
    program_fold.

  (* With the following, one can rewrite under λ with setoid_rewrite *)

  Instance pointwise_eq_ext {A B : Type} {RB : relation B} (sb : subrelation RB eq) :
    subrelation (pointwise_relation A RB) eq.
  Proof.
    intros f g Hfg.
    apply functional_extensionality.
    intro x. apply sb. apply Hfg.
  Qed.

  (** Folding under binders with setoid_rewrite *)

  (* TODO: Can we also remove o? Hard because of the dependencies. *)
  (* TODO: Can we use the trivial relation instead of the second eq? *)
  Instance opr_morphism L I (A : choiceType) o :
    Proper (eq ==> eq ==> pointwise_relation (tgt o) eq ==> eq) (@opr L I A o).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  (* TODO: Can we also remove l? Hard because of the dependencies. *)
  (* TODO: Can we use the trivial relation instead of the first eq? *)
  Instance getr_morphism L I (A : choiceType) l :
    Proper
      (eq ==> pointwise_relation (option (Value l.π1)) eq ==> eq)
      (@getr L I A l).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  (* TODO: Can we also remove o? Hard because of the dependencies. *)
  Instance sampler_morphism L I (A : choiceType) o :
    Proper (pointwise_relation (Arit o) eq ==> eq) (@sampler L I A o).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Instance bind_morphism L I (A B : choiceType) :
    Proper (eq ==> pointwise_relation A eq ==> eq) (@bind L I A B).
  Proof.
    simpl_relation.
    f_equal. apply functional_extensionality. auto.
  Qed.

  Opaque bind ret opr getr putr sampler.

  Tactic Notation "program" "setoid" "fold" :=
    try setoid_rewrite fold_putr ;
    try setoid_rewrite fold_getr ;
    try setoid_rewrite fold_opr ;
    try setoid_rewrite fold_sampler ;
    try setoid_rewrite fold_ret.

End PackageTactics.