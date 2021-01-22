From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Mon Require Import SPropBase.
From Crypt Require Import ChoiceAsOrd Couplings.
From mathcomp Require Import all_ssreflect.

Import SPropNotations.
Import SPropAxioms.

(*
In this file I try to define a state transformer for relative monads.
just for choiceType relative monads for now.

This file is not useful anymore. Can transform relative monads via left
relative adjunctions (see Crypt/OrderEnrichedAdjunctions.v)
*)

Lemma applying_functions : forall {A B} (f g : A -> B) (a:A), f = g -> f a = g a.
  Proof.
  move=> A B f g a Heq. rewrite Heq. reflexivity.
Qed.


Section OnRelMons.
  Context (S : ord_choiceType).

  Definition rstt0 : (ord_relativeMonad choice_incl) -> ord_choiceType -> TypeCat :=
    fun M A => (choice_incl S) -> M (F_choice_prod  ⟨ A ,  S ⟩).

  Program Definition rstt : ord_relativeMonad choice_incl -> ord_relativeMonad choice_incl :=
    fun M => @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl
    (rstt0 M) _ _ _ _ _ _.
  Next Obligation. (*the unit*)
    move=> M A a. rewrite /rstt0. move=> s0.
    apply (@ord_relmon_unit ord_choiceType TypeCat choice_incl M (F_choice_prod ⟨ A , S ⟩)).
    econstructor. trivial. exact s0.
  Defined.
  Next Obligation. (*the bind*)
    move=> M A B k m s0.
    eapply (@ord_relmon_bind _ _ _ M (F_choice_prod ⟨ A, S⟩) (F_choice_prod⟨B,S⟩)).
    move=> ppair. rewrite /rstt0 in k. eapply k.
    move: ppair=> [a s]. exact a. move: ppair=> [a s]. exact s.
    apply m. exact s0.
  Defined.
  Next Obligation.
    intros. move=> k1 k2 pointwise_eq. move=> m. rewrite /rstt_obligation_2.
    apply funext_sprop. move=> s. f_sEqual. apply funext_sprop.
    move=> [a s']. destruct (pointwise_eq a). reflexivity. reflexivity.
  Qed.
  Next Obligation.
    move=> M A. apply boolp.funext. move=> m. rewrite /rstt_obligation_2.
    apply boolp.funext. move=> s. rewrite /rstt_obligation_1.
    have: (fun ppair : choice_incl (F_choice_prod ⟨ A, S ⟩) =>
     ord_relmon_unit M (F_choice_prod ⟨ A, S ⟩)
       (let (a, _) := ppair in a, let (_, s0) := ppair in s0)) = ord_relmon_unit M (F_choice_prod ⟨ A ,S⟩).
    apply boolp.funext. move=> [a s']. reflexivity.
    move=> Heq. rewrite Heq. rewrite ord_relmon_law1. cbv. reflexivity.
  Qed.
  Next Obligation.
    move=> M A B k. apply boolp.funext. move=> a. rewrite /rstt_obligation_2.
    rewrite /rstt_obligation_1. apply boolp.funext. move=> s0.
    pose (ord_relmon_law2 M (F_choice_prod⟨A,S⟩) (F_choice_prod⟨B,S⟩)
     (fun ppair : choice_incl (F_choice_prod ⟨ A, S ⟩) =>
     k (let (a0, _) := ppair in a0) (let (_, s) := ppair in s))).
    unshelve eapply applying_functions in e. econstructor. exact a. exact s0.
    simpl in e. simpl. assumption.
  Qed.
  Next Obligation.
    move=> M A B C k2 k1. rewrite /rstt_obligation_2.
    apply boolp.funext. move=> m.
    apply boolp.funext. move=> s0.
    pose (ord_relmon_law3 M A B C).

