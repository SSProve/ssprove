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

(* TODO MOVE *)
(* TODO Same as finmap.oextract but with a better name? *)
Definition getSome {A} (o : option A) :
  isSome o → A.
Proof.
  intro h.
  destruct o. 2: discriminate.
  assumption.
Defined.

Section KEMDEM.

  (** In the SSP paper, we have λ.
      key_length would 2^λ because we do not use bitstrings.
  *)
  Context (key_length : nat) `{Positive key_length}.

  Context (plain_length : nat) `{Positive plain_length}.

  (** In the paper, the following are functions of |m|, here we assume |m|
      is constant: plain_length.
  *)
  Context (clen : nat) `{Positive clen}.
  Context (elen : nat) `{Positive elen}.

  (** Types *)
  Notation "'key" := ('fin key_length) (in custom pack_type at level 2).
  Notation "'key" := ('fin key_length) (at level 2) : package_scope.

  Notation "'plain" := ('fin plain_length) (in custom pack_type at level 2).
  Notation "'plain" := ('fin plain_length) (at level 2) : package_scope.

  Notation "'clen" := ('fin clen) (in custom pack_type at level 2).
  Notation "'clen" := ('fin clen) (at level 2) : package_scope.

  Notation "'elen" := ('fin elen) (in custom pack_type at level 2).
  Notation "'elen" := ('fin elen) (at level 2) : package_scope.

  (** Procedure names *)

  (* KEY *)
  Definition GEN := 0%N.
  Definition SET := 1%N.
  Definition GET := 2%N.

  (* KEM-CCA *)
  Definition KEMGEN := 6%N.
  Definition ENCAP := 7%N.
  Definition DECAP := 8%N.

  (* DEM-CCA *)
  Definition ENC := 9%N.
  Definition DEC := 10%N.

  (* PKE-CCA / MOD-CCA *)
  Definition PKGEN := 3%N.
  Definition PKENC := 4%N.
  Definition PKDEC := 5%N.

  (** Memory locations *)
  Definition key : Location := ('option ('fin key_length) ; 0%N).

  (** Uniform distributions *)
  Definition i_key := key_length.

  (** KEY Package *)

  Definition KEY :
    package
      (fset [:: key ])
      [interface]
      [interface
        val #[ GEN ] : 'unit → 'unit ;
        val #[ SET ] : 'key → 'unit ;
        val #[ GET ] : 'unit → 'key
      ] :=
    [package
      def #[ GEN ] (_ : 'unit) : 'unit {
        k ← get key ;;
        assert (k == None) ;;
        k ← sample uniform i_key ;;
        put key := Some k ;;
        ret Datatypes.tt
      } ;
      def #[ SET ] (k : 'key) : 'unit {
        k' ← get key ;;
        assert (k' == None) ;;
        put key := Some k ;;
        ret Datatypes.tt
      } ;
      def #[ GET ] (_ : 'unit) : 'key {
        k ← get key ;;
        #assert (isSome k) as kSome ;;
        @ret 'key (getSome k kSome)
      }
    ].

  (** Assumed KEM game *)
  (* TODO Not sure if I should do this, or simply assusme some code. *)
  Definition KEM_export :=
    [interface
      val #[ KEMGEN ] : 'unit → 'key ;
      val #[ ENCAP ] : 'unit → 'elen ;
      val #[ DECAP ] : 'elen → 'key
    ].

  Context (KEM₀ : loc_package [interface val #[ SET ] : 'key → 'unit ] KEM_export).
  Context (KEM₁ : loc_package [interface val #[ GEN ] : 'unit → 'unit ] KEM_export).

  (** Assumed DEM game *)
  Definition DEM_export :=
    [interface
      val #[ ENC ] : 'plain → 'clen ;
      val #[ DEC ] : 'clen → 'plain
    ].

  Context (DEM₀ : loc_package [interface val #[ GET ] : 'unit → 'key ] DEM_export).
  Context (DEM₁ : loc_package [interface val #[ GET ] : 'unit → 'key ] DEM_export).

  (** PKE-CCA *)

  Definition PKE_CCA :
    package
      (fset [:: (* TODO *) ])
      [interface (* TODO *) ]
      [interface
        val #[ PKGEN ] : 'unit → 'key ;
        val #[ PKENC ] : 'plain → 'clen ;
        val #[ PKDEC ] : 'elen × 'clen → 'plain
      ].
  Abort.

  (** MOD-CCA *)

  Definition MOD_CCA :
    package
      (fset [:: (* TODO *) ])
      [interface (* TODO *) ]
      [interface
        val #[ PKGEN ] : 'unit → 'key ;
        val #[ PKENC ] : 'plain → 'clen ;
        val #[ PKDEC ] : 'elen × 'clen → 'plain
      ].
  Abort.

End KEMDEM.