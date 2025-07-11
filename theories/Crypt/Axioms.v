Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals boolp.
Set Warnings "notation-overridden,ambiguous-paths".

Local Open Scope ring_scope.

(*
In this file we assume several axioms.
*)

Parameter (R:realType).
Parameter  (absord : R -> R -> bool).  (*sealed order on real numbers*)
Parameter (unlock_absord : absord = (fun x y : R => x <= y)). (*unseal with this*)


(* We can obtain proof_irrelevance from boolp in mathcomp: *)
Definition proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2 := Prop_irrelevance.
From Coq Require Export FunctionalExtensionality.


(* The following are not axioms per se, but come from boolp using axioms *)
Local Definition func (A B : Type) (R : A -> B -> Prop) :
  (forall a : A, exists b : B, R a b) -> forall a : A, { b : B | R a b }.
  intros H a.
  specialize (H a).
  apply constructive_indefinite_description in H.
  destruct H as [b H].
  exists b. assumption.
Qed.

Local Definition ext_func (A B : Type) (R : A -> B -> Prop) (H : forall a : A, { b : B | R a b }) :
  A -> B.
  intros a.
  specialize (H a).
  destruct H as [b H].
  exact b.
Defined.

Local Theorem fchoice (A B : Type) (R : A -> B -> Prop) :
  (forall a : A, exists b : B , R a b) -> exists (f : A -> B), forall a : A, R a (f a).
  intros H.
  remember (func A B R H) as F.
  exists (ext_func A B R F).
  unfold ext_func.
  cbv; intuition.
  remember (F a) as W.
  destruct W.
  assumption.
Qed.

Theorem schoice (A B : Type) (R : A -> B -> Prop) :
  (forall a : A, exists b : B , R a b) -> { f : A -> B | forall a : A, R a (f a) }.
  intros H.
  remember (func A B R H) as F.
  exists (ext_func A B R F).
  unfold ext_func.
  cbv; intuition.
  remember (F a) as W.
  destruct W.
  assumption.
Qed.
