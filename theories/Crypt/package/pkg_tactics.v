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
  pkg_composition pkg_notation chUniverse
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
    | valid_package ?L ?I ?E ?q =>
      change (valid_package L I E q)
      with (tac_intro_mark (valid_package L I E p)) in h'
    end
  end.

Ltac mark_abstract_codes :=
  repeat match goal with
  | |- context [ mkprog ?p ?h ] =>
    let h' := fresh "h" in
    set (h' := h) ;
    let p' := fresh "p" in
    set (p' := mkprog p h') ;
    clearbody h' ;
    change (mkprog p h') with (tac_mark (mkprog p h')) in p' ;
    lazymatch type of h' with
    | valid_code ?L ?I ?q =>
      change (valid_code L I q)
      with (tac_intro_mark (valid_code L I p)) in h'
    end
  end.

Ltac unmark_tac_mark :=
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

Ltac intro_tac_intro :=
  repeat match goal with
  | |- ∀ h : tac_intro_mark ?A, _ =>
    intro h ;
    change (tac_intro_mark A) with A in h
  end.

Ltac package_before_rewrite :=
  mark_abstract_packages ;
  unmark_tac_mark ;
  revert_tac_intro.

Ltac package_after_rewrite :=
  intro_tac_intro.

Ltac code_before_rewrite :=
  mark_abstract_codes ;
  unmark_tac_mark ;
  revert_tac_intro.

Ltac code_after_rewrite :=
  intro_tac_intro.

(** Tactic to unify Positive proofs in a goal *)

(* Ltac mark_abstract_positive :=
  repeat match goal with
  | |- context [ @mkpos ?p ?h ] =>
    let h' := fresh "h" in
    set (h' := h) ;
    let p' := fresh "p" in
    set (p' := @mkpos p h') ;
    clearbody h' ;
    change (@mkpos p h') with (tac_mark (@mkpos p h')) in p' ;
    lazymatch type of h' with
    | ?T =>
      change T with (tac_intro_mark (Positive p)) in h'
    end
  end. *)

(* Ltac unify_marked_positive_proofs :=
  repeat match goal with
  | h : tac_intro_mark (Positive ?n),
    h' : tac_intro_mark (Positive ?n) |- _ =>
    assert (h = h') by eapply uip ;
    subst h'
  end. *)

Ltac subst_marked :=
  repeat match goal with
  | p := tac_mark ?t |- _ =>
    subst p
  end.

Ltac unmark_tac_intro_mark :=
  repeat match goal with
  | h : tac_intro_mark ?t |- _ =>
    change (tac_intro_mark t) with t in h
  end.

(* Ltac unify_positive_proofs :=
  mark_abstract_positive ;
  unify_marked_positive_proofs ;
  unmark_tac_intro_mark ;
  subst_marked. *)

(** Tactic to unify ValidCode proofs in a goal *)

Ltac unify_marked_code_proofs :=
  repeat match goal with
  | h : tac_intro_mark (ValidCode ?L ?I ?p),
    h' : tac_intro_mark (ValidCode ?L ?I ?p) |- _ =>
    assert (h = h') by eapply uip ;
    subst h'
  end.

Ltac unify_code_proofs :=
  mark_abstract_codes ;
  unify_marked_code_proofs ;
  unmark_tac_intro_mark ;
  subst_marked.

(** Tactic to unify ValidPackage proofs in a goal *)

Ltac unify_marked_package_proofs :=
  repeat match goal with
  | h : tac_intro_mark (ValidPackage ?L ?I ?E ?p),
    h' : tac_intro_mark (ValidPackage ?L ?I ?E ?p) |- _ =>
    assert (h = h') by eapply uip ;
    subst h'
  end.

Ltac unify_package_proofs :=
  mark_abstract_packages ;
  unify_marked_package_proofs ;
  unmark_tac_intro_mark ;
  unmark_tac_mark.

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
    valid_package L I [interface] emptym.
Proof.
  intros L I.
  rewrite -fset0E.
  apply prove_valid_package.
  intros [id [S T]] ho. eapply fromEmpty. eauto.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [::])) =>
  try (replace E with [interface] by eapply fset0E) ;
  eapply valid_empty_package
  : typeclass_instances packages.

Lemma valid_package1 :
  ∀ L I i A B f,
    (∀ x, valid_code L I (f x)) →
    valid_package L I (fset [:: (i, (A, B))]) (mkfmap [:: (i, mkdef A B f)]).
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
    valid_package L I E p →
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
    valid_package L I (fset E) (mkfmap p) →
    (∀ x, valid_code L I (f x)) →
    i \notin (λ '(i,_), i) @: fset E →
    valid_package L I (fset ((i, (A, B)) :: E))
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
    valid_package L I (fset E) (mkfmap p) →
    (∀ x, valid_code L I (f x)) →
    i \notin (λ '(i,_), i) @: fset E →
    A = A' →
    B = B' →
    valid_package L I (fset ((i, (A', B')) :: E))
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
  shelve : packages.

#[export] Hint Extern 2 (is_true (?x \in fset ?I)) =>
  rewrite in_fset
  : typeclass_instances packages.

#[export] Hint Extern 3 (is_true (?x \in ?I)) =>
  reflexivity
  : typeclass_instances packages.

#[export] Hint Extern 3 (is_true (?x \in ?I)) =>
  inseq_try
  : typeclass_instances packages.

#[export] Hint Extern 2 (is_true (?x \notin fset ?I)) =>
  rewrite notin_fset
  : typeclass_instances packages.

#[export] Hint Extern 3 (is_true (?x \notin ?I)) =>
  reflexivity
  : typeclass_instances packages.

#[export] Hint Extern 2 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons ; [
    eapply valid_package_from_class
  | intro ; eapply valid_code_from_class
  | rewrite imfset_fset ; rewrite notin_fset
  ]
  : typeclass_instances packages.

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
: typeclass_instances packages.

#[export] Hint Extern 2 (trimmed ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p))) =>
  eapply trimmed_package_cons
: typeclass_instances packages.

Ltac chUniverse_eq_prove :=
  lazymatch goal with
  | |- chProd _ _ = chProd _ _ => f_equal ; chUniverse_eq_prove
  | |- chMap _ _ = chMap _ _ => f_equal ; chUniverse_eq_prove
  | |- chOption _ = chOption _ => f_equal ; chUniverse_eq_prove
  | |- chFin _ = chFin _ => f_equal ; apply positive_ext ; reflexivity
  | |- _ = _ => reflexivity
  end.

#[export] Hint Extern 4 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  eapply valid_package_cons_upto ; [
    eapply valid_package_from_class
  | intro ; eapply valid_code_from_class
  | rewrite imfset_fset ; rewrite notin_fset
  | chUniverse_eq_prove
  | chUniverse_eq_prove
  ]
  : typeclass_instances packages.

#[export] Hint Extern 10 (ValidCode ?L ?I (let u := _ in _)) =>
  cbv zeta
  : typeclass_instances packages.

#[export] Hint Extern 2 (ValidCode ?L ?I (match ?t with _ => _ end)) =>
  destruct t
  : typeclass_instances packages.

(** Variant of the cons case where we unify Positive proofs beforehand
  This is—I hope—the only thing that might cause a discrepancy between
  the interface and the signature of the term.
*)
(* #[export] Hint Extern 3 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
  =>
  unify_positive_proofs
  : typeclass_instances. *)

Ltac ssprove_valid :=
  (unshelve typeclasses eauto with packages) ; shelve_unifiable.