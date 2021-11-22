From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl
  Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.

Import PackageNotation.

Module Type ROParams.

  Parameter Query : finType.
  Parameter Random : finType.

  Parameter Query_pos : Positive #|Query|.
  Parameter Random_pos : Positive #|Random|.

End ROParams.

Module RO (π : ROParams).

  Import π.

  #[local] Existing Instance Query_pos.
  #[local] Existing Instance Random_pos.

  Definition chQuery := 'fin #|Query|.
  Definition chRandom := 'fin #|Random|.
  Notation " 'query " := chQuery (in custom pack_type at level 2).
  Notation " 'random " := chRandom (in custom pack_type at level 2).

  Definition i_random := #|Random|.
  Definition INIT : nat := 0.
  Definition QUERY : nat := 1.

  Definition queries_loc : Location := (chMap chQuery chRandom ; 2).
  Definition RO_locs : {fset Location} := fset [:: queries_loc].

  Definition RO_exports :=
    [interface
      val #[ INIT ] : 'unit → 'unit ;
      val #[ QUERY ] : 'query → 'random
    ].

  Definition RO : package RO_locs [interface] RO_exports :=
    [package
      def #[ INIT ] (_ : 'unit) : 'unit
      {
        put queries_loc := emptym ;;
        ret Datatypes.tt
      } ;
      def #[ QUERY ] (q : 'query) : 'random
      {
        queries ← get queries_loc ;;
        match queries q with
        | Some r =>
          ret r
        | None =>
          r ← sample uniform i_random ;;
          put queries_loc := setm queries q r ;;
          ret r
        end
      }
    ].

End RO.
