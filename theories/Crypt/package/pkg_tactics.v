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
From SSProve.Crypt Require Import Prelude pkg_core_definition
  pkg_composition pkg_notation choice_type fmap_extra
  RulesStateProb.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

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
  try fmap_solve. (*;
  try in_fset_auto ;
                     try inset_try.*)

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

(** Some validity lemmata and hints *)
(* TODO MOVE? *)

(*
Definition fromEmpty {B} {v : opsig} (H : v \in fset0) : B.
Proof.
  rewrite in_fset0 in H.
  move: H. move /eqP. move /eqP => H.
  discriminate.
Defined.
 *)

Lemma valid_empty_package :
  ∀ L I,
    ValidPackage L I [interface] emptym.
Proof.
  intros L I.
  apply prove_valid_package.
  intros [id [S T]] ho. rewrite /fhas emptymE // in ho.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [::])) =>
  try (replace E with [interface] by eapply fset0E) ;
  eapply valid_empty_package
  : typeclass_instances ssprove_valid_db.

Lemma valid_package1 :
  ∀ L I i A B f,
    (∀ x, ValidCode L I (f x)) →
    ValidPackage L I (mkfmap [:: (i, (A, B))]) (mkfmap [:: (i, mkdef A B f)]).
Proof.
  intros L I i A B f hf.
  apply prove_valid_package.
  intros [i' [S T]] ho. rewrite /fhas setmE emptymE //= in ho.
  destruct (i' == i) eqn:e => //.
  injection ho => ? ?; subst.
  exists f.
  move: e => /eqP -> //.
  rewrite setmE eq_refl //.
Qed.

(* Would be a shortcut, but when backtracking, this has an unnecessary cost *)
(* #[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [:: (?i, mkdef ?A ?B ?f)])) =>
  eapply valid_package1 ;
  intro ; eapply valid_code_from_class
  : typeclass_instances. *)

Lemma valid_package_cons :
  ∀ L I i A B f E p,
    ValidPackage L I (mkfmap E) (mkfmap p) →
    (∀ x, ValidCode L I (f x)) →
    ValidPackage L I (mkfmap ((i, (A, B)) :: E))
      (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros L I i A B f E p hp hf.
  apply prove_valid_package.
  intros [i' [S T]] ho. rewrite //= setmE in ho.
  destruct (i' == i) eqn:e.
  - move: e => /eqP e.
    injection ho => ? ?; subst.
    simpl. exists f.
    rewrite setmE eq_refl //.
  - eapply from_valid_package in hp.
    specialize (hp (i', (S, T)) ho).
    destruct hp as [g [eg hg]].
    exists g.
    rewrite //= setmE e //.
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

(*
(* TODO MOVE *)
Lemma notin_fset :
  ∀ (T : ordType) (s : seq T) (x : T),
    (x \notin fset s) = (x \notin s).
Proof.
  intros T s x.
  unfold "\notin". rewrite in_fset. reflexivity.
Qed.
 *)

#[export] Hint Extern 100 =>
  shelve : ssprove_valid_db.

(*
#[export] Hint Extern 2 (is_true (?x \in fset ?I)) =>
  rewrite in_fset
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 3 (is_true (?x \in ?I)) =>
  reflexivity
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 3 (is_true (?x \in ?I)) =>
  inseq_try
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 2 (is_true (?x \notin fset ?I)) =>
  rewrite notin_fset
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 3 (is_true (?x \notin ?I)) =>
  reflexivity
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 3 (is_true (fsubset [interface] ?L)) =>
  rewrite <- fset0E ; eapply fsub0set
  : typeclass_instances ssprove_valid_db.
 *)

(*
#[export] Hint Extern 2 (fhas ?m ?k) =>
  fmap_solve
  : typeclass_instances ssprove_valid_db.
*)

#[export] Hint Extern 2 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons ; [
  | intro
  ]
  : typeclass_instances ssprove_valid_db.

Lemma trimmed_empty_package :
  trimmed [interface] (mkfmap nil).
Proof.
  unfold trimmed. simpl. unfold trim.
  apply eq_fmap. intro n.
  rewrite filtermE. rewrite emptymE. reflexivity.
Qed.

Lemma trimmed_package_cons :
  ∀ i A B f p E,
    trimmed (mkfmap E) (mkfmap p) →
    trimmed (mkfmap ((i, (A, B)) :: E)) (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros i A B f p E h.
  unfold trimmed. unfold trim.
  apply eq_fmap. intro n.
  rewrite filtermE //= 2!setmE.
  destruct (n == i) eqn:e => //.
  unfold trimmed, trim in h.
  apply eq_fmap in h. specialize (h n).
  rewrite filtermE // in h.
Qed.

#[export] Hint Extern 1 (trimmed ?E (mkfmap [::])) =>
  eapply trimmed_empty_package
: typeclass_instances ssprove_valid_db.

#[export] Hint Extern 2 (trimmed ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p))) =>
  eapply trimmed_package_cons
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
