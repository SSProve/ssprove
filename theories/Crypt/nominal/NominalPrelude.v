Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  reals distr realsum fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap ffun fperm.

From SSProve.Crypt Require Export Axioms SubDistr pkg_composition
  Prelude Package Nominal Fresh Pr Share Sep Adv.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(******************************************************************************)
(* This serves as the main import when using Nominal-SSProve. Importantly,    *)
(* it re-exports Prelude and most of the nominal development.                 *)
(******************************************************************************)

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.
Import Order.POrderTheory.

Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

Ltac ssprove_ehop :=
  eapply le_trans; [ eapply Adv_triangle |].

Ltac ssprove_hop M :=
  eapply le_trans; [ eapply (@Adv_triangle _ M%sep) |].


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

Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.


(* Light and uniform notation for interface, packages and calls. *)
(* The basic shape of a signature is `[ f ] : { A ~> B }`, where
   f is an identifier, A is the argument type and B is the return
   type of the function. *)

Notation "[ f ] : { A ~> B }" :=
  (mkopsig f A B)
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

Notation "y ← 'call' [ f ] : { A ~> B } x ;; c" :=
  (opr (mkopsig f A B) x (λ y, c))
  (at level 100, x at next level, right associativity,
  format "y  ←  call  [ f ]  :  { A  ~>  B }  x  ;;  '//' c")
  : package_scope.

Notation "' p ← 'call' [ f ] : { A ~> B } x ;; c" :=
  (opr (mkopsig f A B) x (λ p, c))
  (at level 100, p pattern, x at next level, right associativity,
  format "' p  ←  call  [ f ]  :  { A  ~>  B }  x  ;;  '//' c")
  : package_scope.
