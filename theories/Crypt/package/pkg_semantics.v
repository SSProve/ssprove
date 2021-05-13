(** Semantics of code

  This module gives an interpretation of code into the semantics.
*)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph chUniverse pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, who knows why. *)
From Crypt Require Import FreeProbProg.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.

Arguments retrFree {_ _ _} _.
Arguments bindrFree {_ _ _ _} _ _.
Arguments ropr {_ _ _} _ _.

(** Interpretation of raw codes into the semantic model

  Note that we don't require any validity proof to do so,
  instead we rely on the fact that types in the chUniverse are all
  inhabited.

*)
Fixpoint repr {A : choiceType} (p : raw_code A) :
  rFreeF (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) A :=
  match p with
  | ret x => retrFree x
  | opr o x k =>
      repr (k (chCanonical (chtgt o)))
  | getr l k =>
      bindrFree
        (ropr gett (λ s, retrFree (get_heap s l)))
        (λ v, repr (k v))
  | putr l v k =>
      bindrFree
        (ropr gett (λ s, ropr (putt (set_heap s l v)) (λ s, retrFree tt)))
        (λ _, repr k)
  | sampler op k =>
      bindrFree
        (ropr (op_iota op) (λ v, retrFree v))
        (λ s, repr (k s))
  end.

Lemma repr_bind :
  ∀ {A B : choiceType} (p : raw_code A) (f : A → raw_code B),
    repr (bind p f) = bindrFree (repr p) (λ a, repr (f a)).
Proof.
  intros A B p f.
  induction p in f |- *.
  - cbn. reflexivity.
  - simpl. auto.
  - simpl. f_equal. extensionality x. auto.
  - simpl. f_equal. extensionality x. f_equal. extensionality y. auto.
  - simpl. f_equal. extensionality x. auto.
Qed.

Definition repr_cmd {A} (c : command A) :
  rFreeF (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) A :=
  match c with
  | cmd_op o x => retrFree (chCanonical (chtgt o))
  | cmd_get ℓ =>
      bindrFree
        (ropr gett (λ s, retrFree (get_heap s ℓ)))
        (λ v, retrFree v)
  | cmd_put ℓ v =>
      bindrFree
        (ropr gett (λ s, ropr (putt (set_heap s ℓ v)) (λ s, retrFree tt)))
        (λ s', retrFree s')
  | cmd_sample op =>
      bindrFree
        (ropr (op_iota op) (λ v, retrFree v))
        (λ s, retrFree s)
  end.

Lemma repr_cmd_bind :
  ∀ {A B} (c : command A) (k : A → raw_code B),
    repr (cmd_bind c k) = bindrFree (repr_cmd c) (λ a, repr (k a)).
Proof.
  intros A B c k.
  destruct c. all: reflexivity.
Qed.