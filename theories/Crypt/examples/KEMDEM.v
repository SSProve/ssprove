(** KEM-DEM example *)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude.

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Import PackageNotation.

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

(** Procedure names

  All in one place so it's easier.

*)

(* KEY *)
Definition GEN := 0%N.
Definition SET := 1%N.
Definition GET := 2%N.

(* MOD-CCA *)
Definition PKGEN := 3%N.
Definition PKENC := 4%N.
Definition PKDEC := 5%N.

(** KEY Package *)

(* TODO Section for length?  *)
Definition i_key (l : nat) := l.

Definition key n `{Positive n} : Location := ('option ('fin n) ; 0%N).

(* TODO MOVE *)
(* TODO Same as finmap.oextract but with a better name? *)
Definition getSome {A} (o : option A) :
  isSome o → A.
Proof.
  intro h.
  destruct o. 2: discriminate.
  assumption.
Defined.

Definition KEY n `{Positive n} :
  package
    (fset [:: key n ])
    [interface]
    [interface
      val #[ GEN ] : 'unit → 'unit ;
      val #[ SET ] : ('fin n) → 'unit ;
      val #[ GET ] : 'unit → 'fin n
    ] :=
  [package
    def #[ GEN ] (_ : 'unit) : 'unit {
      k ← get (key n) ;;
      assert (k == None) ;;
      k ← sample uniform (i_key n) ;;
      put (key n) := Some k ;;
      ret Datatypes.tt
    } ;
    def #[ SET ] (k : ('fin n)) : 'unit {
      k' ← get (key n) ;;
      assert (k' == None) ;;
      put (key n) := Some k ;;
      ret Datatypes.tt
    } ;
    def #[ GET ] (_ : 'unit) : ('fin n) {
      k ← get (key n) ;;
      #assert (isSome k) as kSome ;;
      @ret ('fin n) (getSome k kSome)
    }
  ].

(** MOD-CCA *)

Definition MODCCA l `{Positive l} :
  package
    (fset [:: (* TODO *) ])
    [interface] (* TODO Import KEM and DEM *)
    [interface
      val #[ PKGEN ] : 'unit → ('fin l) × ('fin l)
    ].
Abort.