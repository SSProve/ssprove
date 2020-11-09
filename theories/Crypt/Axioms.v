From mathcomp Require Import all_ssreflect all_algebra reals boolp.


Import ssrnum.Num.Theory.
Local Open Scope ring_scope.

Parameter (R:realType).
Parameter  (absord : R -> R -> bool). 
Parameter (unlock_absord : absord = (fun x y : R => x <= y)).

From Coq Require Export Logic.ProofIrrelevance.
From Coq Require Export FunctionalExtensionality.

(*now an equivalence between SProp and Prop. An equivalence of
truth collections.*)

(*
Parameter (Prop2SProp : Prop -> SProp).
Parameter (SProp2Prop : SProp -> Prop).

Axiom (PSP_retr :  forall Q : Prop , SProp2Prop (Prop2SProp Q) = Q ).
Axiom (PSP_sect : forall Q' : SProp, Prop2SProp( SProp2Prop Q' ) = Q').

Axiom (Prop2SProp_truthMorphism_leftRight :
forall Q : Prop, Q -> (Prop2SProp Q)).
Axiom (Prop2SProp_truthMorphism_rightLeft :
forall Q : Prop, (Prop2SProp Q) -> Q).

Axiom (SProp2Prop_truthMorphism_leftRight :
forall Q' : SProp, Q' -> SProp2Prop Q').
Axiom (SProp2Prop_truthMorphism_rightLeft :
forall Q' : SProp, SProp2Prop Q' -> Q').
*)

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
