From Mon Require Import SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import Casts.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From mathcomp Require boolp.

Import SPropNotations.

(*
In this file we register the collection of mathcomp choicetypes "choiceType" as an ord_category instance. Morphisms between choiceTypes are endowed with a discrete order structure.

We also define a product of choiceTypes here.
*)

Section ChoiceAsOrd.


  Program Definition ord_choiceType : ord_category :=
    mkOrdCategory choiceType
               (fun A B => A -> B)
               (fun _ _ f g => forall x, f x =  g x) _
               (fun A a => a)
               (fun _ _ _ f g x => f (g x))
               _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; etransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. induction (H0 x1). apply H. Qed.

End ChoiceAsOrd.

Program Definition choice_incl := @mkOrdFunctor ord_choiceType TypeCat
    (fun (A:ord_choiceType) => A)
    (fun (A B : ord_choiceType) f => f)
    _ _ _.


Section Prod_of_choiceTypes.

  Definition F_choice_prod_obj : Obj (prod_cat ord_choiceType ord_choiceType) ->
                               Obj ord_choiceType.
  Proof.
    rewrite /prod_cat /=. move => [C1 C2].
    exact (prod_choiceType C1 C2).
  Defined.

  Definition F_choice_prod_morph : forall T1  T2 : (prod_cat ord_choiceType ord_choiceType),
      (prod_cat ord_choiceType ord_choiceType) ⦅ T1; T2 ⦆ ->
      ord_choiceType ⦅F_choice_prod_obj T1; F_choice_prod_obj T2 ⦆.
  Proof.
    move => [C11 C12] [C21 C22] [f1 f2] [c1 c2]. simpl in *.
    exact (f1 c1, f2 c2).
  Defined.

  Definition F_choice_prod: ord_functor (prod_cat ord_choiceType ord_choiceType) ord_choiceType.
  Proof.
    exists F_choice_prod_obj F_choice_prod_morph.
    - move => [C11 C12] [C21 C22] [s11 s12] [s21 s22] [H1 H2] [x1 x2].
      simpl in *. move: (H1 x1) (H2 x2) => eq1 eq2.
      destruct eq1, eq2. reflexivity.
    - move => [C1 C2]. rewrite /F_choice_prod_morph /=.
      apply: boolp.funext => c. by destruct c.
    - move =>  [C11 C12] [C21 C22] [C31 C32] [f1 f2] [g1 g2].
      simpl in *. apply: boolp.funext => x. by destruct x.
  Defined.

  Definition choice_fst_proj : forall {A1 A2 : ord_choiceType},
  ord_choiceType ⦅ F_choice_prod (npair A1 A2) ; A1 ⦆.
    intros. intro pairr. destruct pairr as [a1 a2]. simpl in a1. assumption.
  Defined.

  Definition choice_snd_proj : forall {A1 A2 : ord_choiceType},
  ord_choiceType ⦅ F_choice_prod (npair A1 A2) ; A2 ⦆.
    intros. intro pairr. destruct pairr as [a1 a2]. simpl in a2. assumption.
  Defined.


End Prod_of_choiceTypes.

