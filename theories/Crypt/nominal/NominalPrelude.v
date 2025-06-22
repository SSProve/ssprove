Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  reals distr realsum fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

From SSProve.Crypt Require Export pkg_composition Prelude Package.

From SSProve.Crypt.nominal Require Export
  Nominal Fresh Pr Share Sep Adv.

Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.


Lemma valid_share_link_weak :
  ∀ I M1 M2 E P1 P2,
    ValidPackage (loc P1) M1 E P1 →
    ValidPackage (loc P2) I M2 P2 →
    fcompat (loc P1) (loc P2) →
    fsubmap M1 M2 →
    ValidPackage (loc (P1 ∘ P2)%share) I E (P1 ∘ P2)%share.
Proof. intros; eapply valid_link_weak; eassumption. Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (share_link ?p1 ?p2))) =>
  package_evar ; [ eapply valid_share_link_weak | .. ]
  : typeclass_instances ssprove_valid_db.

Lemma fresh_supp_l : ∀ {X Y : nomType} {x : X} {y : Y},
  fresh (supp x) y = fresh x y.
Proof.
  intros X Y x y.
  rewrite /fresh supp_supp //.
Qed.

Lemma valid_sep_link_weak :
  ∀ I M1 M2 E P1 P2,
    ValidPackage (loc P1) M1 E P1 →
    ValidPackage (loc P2) I M2 P2 →
    fcompat (loc P1) (loc P2) →
    fsubmap M1 M2 →
    ValidPackage (loc (P1 ∘ P2)%sep) I E (P1 ∘ P2)%sep.
Proof. intros.
  eapply valid_link_weak.
  1,4: eassumption.
  1: unfold move; by apply rename_valid.
  apply fseparate_compat.
  rewrite fseparate_disj //=.
  rewrite -fresh_supp_l -fresh_supp_r /supp.
  rewrite //= fresh_supp_l fresh_supp_r.
  auto with nominal_db.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (share_par ?p1 ?p2))) =>
  package_evar ; [ eapply valid_sep_link_weak | .. ]
  : typeclass_instances ssprove_valid_db.

Lemma valid_share_par {I1 I2 E1 E2} {p1 p2 : nom_package} :
  ValidPackage (loc p1) I1 E1 p1 →
  ValidPackage (loc p2) I2 E2 p2 →
  fseparate E1 E2 →
  fcompat (loc p1) (loc p2) →
  fcompat I1 I2 →
  ValidPackage (loc (p1 || p2)%share) (unionm I1 I2) (unionm E1 E2) (p1 || p2)%share.
Proof. apply valid_par. Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (share_par ?p1 ?p2))) =>
  package_evar ; [ eapply valid_share_par | .. ]
  : typeclass_instances ssprove_valid_db.

Lemma valid_sep_par {I1 I2 E1 E2} {p1 p2 : nom_package} :
  ValidPackage (loc p1) I1 E1 p1 →
  ValidPackage (loc p2) I2 E2 p2 →
  fseparate E1 E2 →
  fcompat I1 I2 →
  ValidPackage (loc (p1 || p2)%sep)
    (unionm I1 I2) (unionm E1 E2) (p1 || p2)%sep.
Proof.
  intros. unfold sep_par. apply valid_par; try done.
  1: unfold move; by apply rename_valid.
  apply fseparate_compat.
  rewrite fseparate_disj //=.
  rewrite -fresh_supp_l -fresh_supp_r /supp.
  rewrite //= fresh_supp_l fresh_supp_r.
  auto with nominal_db.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (sep_par ?p1 ?p2))) =>
  package_evar ; [ eapply valid_share_par | .. ]
  : typeclass_instances ssprove_valid_db.


Create HintDb disj_db.
#[export] Hint Resolve disj_equi2 disj_equi2' : disj_db.
#[export] Hint Resolve equi_share_link equi_share_par : disj_db.
#[export] Hint Resolve disj_ID_r disj_ID_l : disj_db.

#[export] Hint Extern 5 (is_true (disj _ _)) =>
  solve [ rewrite -fseparate_disj; fmap_solve ] : disj_db.

Ltac ssprove_separate_solve :=
  auto with disj_db nocore.

Ltac ssprove_separate_once :=
  (rewrite -> share_link_sep_link by ssprove_separate_solve)
  || (rewrite -> share_par_sep_par by ssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac ssprove_separate :=
  repeat ssprove_separate_once.


Create HintDb ssprove_into_share.
Hint Rewrite <- @share_link_sep_link : ssprove_into_share.
Hint Rewrite <- @share_par_sep_par : ssprove_into_share.

Ltac ssprove_share_once :=
  ((rewrite_strat innermost hints ssprove_into_share)
    ; try ssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac ssprove_share :=
  repeat ssprove_share_once.


(* Extra code notation *)

Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_injectLocations;
    [| eapply valid_injectMap;
      [| eapply prog_valid ]]; fmap_solve
  : typeclass_instances ssprove_valid_db.

Notation call n S T a
  := (#import (mkopsig n S T) as F ;; b ← F a ;; ret b).

Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c
  )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.


(* Light and uniform notation for interface, packages and imports *)

Notation "[ f ] : { A ~> B }" :=
    (f, (A, B))
    (in custom interface at level 0,
    f constr, A constr, B constr,
    format "[ f ]  :  { A  ~>  B }").

Notation "[ f ] : { A ~> B } ( x ) { e }" :=
    ((f, mkdef A B (λ x, e)))
    (in custom package at level 0,
    f constr, e constr, x name, A constr, B constr,
    format "[ f ]  :  { A  ~>  B }  ( x )  { '[' '/'  e  '/' ']' }")
    : package_scope.

Notation "[ f ] : { A ~> B } ' p { e }" :=
    ((f, mkdef A B (λ p, e)))
    (in custom package at level 0,
    f constr, e constr, p pattern, A constr, B constr,
    format "[ f ]  :  { A  ~>  B }  ' p  { '[' '/'  e  '/' ']' }")
    : package_scope.

Notation "'#import' s " :=
    (λ x, opr s x (λ y, ret y))
    (at level 100, s custom interface at level 2,
    format "#import  s  ")
    : package_scope.
