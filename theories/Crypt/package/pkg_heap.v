(** Heaps for code/packages

  This module introduces the notion of heap for storing memory in packages.
*)


From Coq Require Import Utf8.
Require Import ZArith.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From mathcomp Require Import word.

(* Must come after importing Equations.Equations, who knows why. *)
From SSProve.Crypt Require Import FreeProbProg.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Definition heap_init (A : choice_type) := chCanonical A.

Definition heap := {fmap nat → nat}.

Definition heap_choiceType := Choice.clone _ heap.

Definition get_heap (map : heap) (l : Location) : l :=
  odflt (heap_init l.2) (obind uncucumber (map l.1)).

Definition set_heap (map : heap) (l : Location) (v : l) : heap
  := setm map l.1 (cucumber v).

Definition empty_heap : heap := emptym.

Lemma get_empty_heap :
  ∀ ℓ, get_heap empty_heap ℓ = heap_init ℓ.
Proof.
  intros ℓ. reflexivity.
Qed.

Lemma get_set_heap_eq :
  ∀ h ℓ v,
    get_heap (set_heap h ℓ v) ℓ = v.
Proof.
  intros h ℓ v.
  rewrite /get_heap /set_heap setmE eq_refl //= cucumberK //.
Qed.

Lemma get_set_heap_neq :
  ∀ h ℓ v ℓ',
    ℓ'.1 != ℓ.1 →
    get_heap (set_heap h ℓ v) ℓ' = get_heap h ℓ'.
Proof.
  move=> h ℓ v ℓ' /negPf ne.
  rewrite /get_heap /set_heap setmE ne //.
Qed.

Lemma set_heap_contract :
  ∀ s ℓ v v',
    set_heap (set_heap s ℓ v) ℓ v' = set_heap s ℓ v'.
Proof.
  intros s ℓ v v'.
  rewrite /set_heap setmxx //.
Qed.

Lemma set_heap_commut :
  ∀ s ℓ v ℓ' v',
    ℓ.1 != ℓ'.1 →
    set_heap (set_heap s ℓ v) ℓ' v' =
    set_heap (set_heap s ℓ' v') ℓ v.
Proof.
  intros s ℓ v ℓ' v' ne.
  rewrite /set_heap setmC //.
Qed.
