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
From Crypt Require Import Prelude pkg_core_definition
  pkg_composition pkg_notation choice_type
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
  try in_fset_auto ;
  try inset_try.

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

#[export] Instance getr_morphism (A : choiceType) l :
  Proper (pointwise_relation (Value l.π1) eq ==> eq) (@getr A l).
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

Definition fromEmpty {B} {v : opsig} (H : v \in fset0) : B.
Proof.
  rewrite in_fset0 in H.
  move: H. move /eqP. move /eqP => H.
  discriminate.
Defined.

Lemma valid_empty_package :
  ∀ L I,
    ValidPackage L I [interface] emptym.
Proof.
  intros L I.
  rewrite -fset0E.
  apply prove_valid_package.
  intros [id [S T]] ho. eapply fromEmpty. eauto.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [::])) =>
  try (replace E with [interface] by eapply fset0E) ;
  eapply valid_empty_package
  : typeclass_instances ssprove_valid_db.

Lemma valid_package1 :
  ∀ L I i A B f,
    (∀ x, ValidCode L I (f x)) →
    ValidPackage L I (fset [:: (i, (A, B))]) (mkfmap [:: (i, mkdef A B f)]).
Proof.
  intros L I i A B f hf.
  apply prove_valid_package.
  intros o ho. rewrite in_fset in ho.
  rewrite mem_seq1 in ho. move: ho => /eqP ho. subst o.
  cbn. exists f.
  destruct (eqn i i) eqn:e.
  2:{ move: e => /eqP. contradiction. }
  intuition auto.
Qed.

(* Would be a shortcut, but when backtracking, this has an unnecessary cost *)
(* #[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [:: (?i, mkdef ?A ?B ?f)])) =>
  eapply valid_package1 ;
  intro ; eapply valid_code_from_class
  : typeclass_instances. *)

Lemma flat_valid_package :
  ∀ L I E p,
    ValidPackage L I E p →
    flat E.
Proof.
  intros L I E p hp.
  intros i [u1 u2] [v1 v2] h1 h2.
  eapply from_valid_package in hp.
  specialize (hp _ h1) as h1'.
  specialize (hp _ h2) as h2'.
  simpl in *.
  destruct h1' as [f [ef _]].
  destruct h2' as [g [eg _]].
  rewrite ef in eg. noconf eg.
  reflexivity.
Qed.

Lemma valid_package_cons :
  ∀ L I i A B f E p,
    ValidPackage L I (fset E) (mkfmap p) →
    (∀ x, ValidCode L I (f x)) →
    i \notin (λ '(i,_), i) @: fset E →
    ValidPackage L I (fset ((i, (A, B)) :: E))
      (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros L I i A B f E p hp hf hi.
  apply prove_valid_package.
  intros o ho. rewrite in_fset in ho. rewrite in_cons in ho.
  move: ho => /orP [ho | ho].
  - move: ho => /eqP ho. subst o.
    rewrite mkfmapE. cbn. exists f.
    destruct (eqn i i) eqn:e.
    2:{ move: e => /eqP. contradiction. }
    intuition auto.
  - rewrite -in_fset in ho.
    eapply from_valid_package in hp.
    specialize (hp _ ho).
    destruct o as [id [S T]].
    destruct hp as [g [eg hg]].
    rewrite mkfmapE. cbn.
    destruct (eqn id i) eqn:e.
    1:{
      move: e => /eqP e. subst id.
      eapply mem_imfset with (f := λ '(i,_), i) in ho.
      unfold "\notin" in hi. rewrite ho in hi.
      discriminate.
    }
    rewrite mkfmapE in eg.
    exists g. intuition auto.
Qed.

Lemma valid_package_cons_upto :
  ∀ L I i A B A' B' f E p,
    ValidPackage L I (fset E) (mkfmap p) →
    (∀ x, ValidCode L I (f x)) →
    i \notin (λ '(i,_), i) @: fset E →
    A = A' →
    B = B' →
    ValidPackage L I (fset ((i, (A', B')) :: E))
      (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros L I i A B A' B' f E p hp hf hi eA eB. subst.
  eapply valid_package_cons. all: eauto.
Qed.

(* TODO MOVE *)
Lemma notin_fset :
  ∀ (T : ordType) (s : seq T) (x : T),
    (x \notin fset s) = (x \notin s).
Proof.
  intros T s x.
  unfold "\notin". rewrite in_fset. reflexivity.
Qed.

#[export] Hint Extern 100 =>
  shelve : ssprove_valid_db.

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

#[export] Hint Extern 2 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons ; [
    idtac
  | intro
  | rewrite imfset_fset ; rewrite notin_fset
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
    trimmed (fset E) (mkfmap p) →
    trimmed (fset ((i, (A, B)) :: E)) (mkfmap ((i, mkdef A B f) :: p)).
Proof.
  intros i A B f p E h.
  unfold trimmed. unfold trim.
  apply eq_fmap. intro n.
  rewrite filtermE.
  rewrite mkfmapE. simpl.
  destruct (n == i) eqn:e.
  - simpl. move: e => /eqP e. subst.
    rewrite in_fset. rewrite in_cons. rewrite eqxx. simpl.
    reflexivity.
  - unfold trimmed, trim in h.
    apply eq_fmap in h. specialize (h n).
    rewrite filtermE in h. rewrite mkfmapE in h.
    rewrite -[X in _ = X]h.
    destruct (getm_def p n) as [[S [T g]]|] eqn:e'.
    2:{ rewrite e'. reflexivity. }
    rewrite e'. simpl.
    rewrite !in_fset. rewrite in_cons.
    destruct ((n, (S, T)) == (i, (A, B))) eqn:e2.
    1:{
      exfalso. move: e2 => /eqP e2. noconf e2.
      rewrite eqxx in e. discriminate.
    }
    rewrite e2. simpl. reflexivity.
Qed.

#[export] Hint Extern 1 (trimmed ?E (mkfmap [::])) =>
  eapply trimmed_empty_package
: typeclass_instances ssprove_valid_db.

#[export] Hint Extern 2 (trimmed ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p))) =>
  eapply trimmed_package_cons
: typeclass_instances ssprove_valid_db.

Lemma valid_scheme :
  ∀ A L I c,
    @ValidCode fset0 [interface] A c →
    ValidCode L I c.
Proof.
  intros A L I c h.
  eapply valid_injectMap. 2: eapply valid_injectLocations.
  1-2: eapply fsub0set.
  rewrite -fset0E in h. auto.
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
    idtac
  | intro
  | rewrite imfset_fset ; rewrite notin_fset
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
