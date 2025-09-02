From SSProve.Mon Require Import SPropBase.
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import Casts.
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
    (fun (A : ord_choiceType) => A)
    (fun (A B : ord_choiceType) f => f)
    _ _ _.


Section Prod_of_choiceTypes.

  Definition F_choice_prod_obj :
    Obj (prod_cat ord_choiceType ord_choiceType) -> Obj ord_choiceType
    := fun '(npair C1 C2) => (C1 * C2)%type.

  Definition F_choice_prod_morph
    (T1 T2 : prod_cat ord_choiceType ord_choiceType) :
    (prod_cat ord_choiceType ord_choiceType) ⦅ T1; T2 ⦆ ->
    ord_choiceType ⦅F_choice_prod_obj T1; F_choice_prod_obj T2 ⦆
    := fun '(npair f1 f2) '(c1, c2) => (f1 c1, f2 c2).

  Program Definition F_choice_prod :
    ord_functor (prod_cat ord_choiceType ord_choiceType) ord_choiceType
    := mkOrdFunctor F_choice_prod_obj F_choice_prod_morph _ _ _.
  Next Obligation.
    move: x y H x0 => [s11 s12] [s21 s22] [H1 H2] [x1 x2].
    move: (H1 x1) (H2 x2) => /= -> -> //.
  Qed.
  Next Obligation.
    apply: boolp.funext => [[? ?]] //.
  Qed.
  Next Obligation.
    apply: boolp.funext => [[? ?]] //.
  Qed.

  Definition choice_fst_proj {A1 A2 : ord_choiceType} :
    ord_choiceType ⦅ F_choice_prod (npair A1 A2) ; A1 ⦆
    := fst.

  Definition choice_snd_proj {A1 A2 : ord_choiceType} :
    ord_choiceType ⦅ F_choice_prod (npair A1 A2) ; A2 ⦆
    := snd.

End Prod_of_choiceTypes.
