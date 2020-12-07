From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings Rules
  StateTransfThetaDens StateTransformingLaxMorph FreeProbProg.
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.


From Crypt Require Import pkg_preamble.
From Crypt Require Import pkg_chUniverse.

Definition ident := nat.

(* Signature of an operation, including the identifier *)
Definition opsig := ident * (chUniverse * chUniverse).
(* Record opsig := mkop {
  ident : nat ;
  src : chUniverse ;
  tgt : chUniverse
}. *)

Definition Location := nat.
Definition Value := nat_choiceType.

Module CorePackageTheory (π : ProbRulesParam).

  Export π.

  Definition Interface := {fset opsig}.

  Definition ide (v : opsig) : ident :=
    let '(n, _) := v in n.

  Definition chsrc (v : opsig) : chUniverse :=
      let '(n, (s, t)) := v in s.

  Definition src (v : opsig) : choiceType :=
    chsrc v.

  Definition chtgt (v : opsig) : chUniverse :=
    let '(n, (s, t)) := v in t.

  Definition tgt (v : opsig) : choiceType :=
    chtgt v.

  Section Translation.

    Context (probE : Type → Type).
    Context (rel_choiceTypes : Type) (*the "small" type of relevant choiceTypes*)
            (chEmb : rel_choiceTypes → choiceType).

    Definition Prob_ops_collection :=
      ∑ rchT : rel_choiceTypes, probE (chEmb rchT).

    Definition Prob_arities : Prob_ops_collection → choiceType :=
      fun '(envType ; opp) => chEmb envType.

  End Translation.

End CorePackageTheory.
