From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality List.

From Mon Require Export Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From mathcomp Require Import all_ssreflect all_algebra reals distr.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Bla.

  Context (R:realType).

  Import SPropNotations.
  Definition is_true_sprop (b:bool) : Prop := if b then True else False.
  Notation "⟦ b ⟧" := (is_true_sprop b).

  Definition unit_interval := { r : R | ⟦0 <= r <= 1⟧}.
  Let I := unit_interval.

  Lemma since_its_true (b:bool) : ⟦b⟧ -> b.
  Proof. by case: b. Qed.

  Lemma its_true_anyway (b:bool) : b -> ⟦b⟧.
  Proof. by case: b. Qed.

End Bla.

Notation "⟦ b ⟧" := (is_true_sprop b).
(* Infix "-s>" := (s_impl) (right associativity, at level 86, only parsing). *)
