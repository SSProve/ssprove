From Coq Require Import Morphisms.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_algebra all_ssreflect classical.boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Mon Require Import SPropBase Base.
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import OrderEnrichedRelativeAdjunctions FreeProbProg ChoiceAsOrd Couplings Theta_exCP SubDistr.

Import SPropNotations.


(*
Let M: I → C be a J-relative monad.
Consider J♭ : I → I and R: C → C functors such that JL♭ ⊣ R
(the "transforming (left relative) adjunction")
M can be factored through its Kleisli: M = R^M ∘ L^M, with L^M ⊣ R^M
And there is a "transformed" left relative adjunction  L^M ∘ L♭ ⊣ R ∘ R^M .
as well as the associated monad of this new adjunction (see AdjTransform in OrderEnrichedRelativeAdjunctions.)
*)


Section ConstantFunctor.
  Context (C D : ord_category) (d : D).

  Program Definition mkConstFunc : ord_functor C D := mkOrdFunctor (fun c => d) _ _ _ _.
  Next Obligation.
    auto with solve_subterm.
  Defined.
  Next Obligation.
    cbv. auto with solve_subterm.
  Qed.
  Next Obligation.
    cbv. intuition. rewrite ord_cat_law1. reflexivity.
  Qed.

End ConstantFunctor.

(*
Lflat = _ x (S1,S2) : chTy² → chTy²
computational relational monad : chty² → Type²
R = S → _ : Type² → Type²
*)
Section DomainStateAdj.
  Context (S1 : ord_choiceType) (S2 : ord_choiceType).

  (*First we define Lflat : chTy² -> chTy² which is just _ x S*)

  Let IdAndS1 := functor_to_prod_cat (ord_functor_id ord_choiceType)
(mkConstFunc ord_choiceType ord_choiceType S1).

  Let IdAndS2 := functor_to_prod_cat (ord_functor_id ord_choiceType)
(mkConstFunc ord_choiceType ord_choiceType S2).

  Definition unaryTimesS1 := ord_functor_comp IdAndS1 F_choice_prod.

  Definition unaryTimesS2 := ord_functor_comp IdAndS2 F_choice_prod.

  Definition binaryTimesS := prod_functor (unaryTimesS1) (unaryTimesS2).

  Let Lflat := binaryTimesS.

  (*Next we define R = S -> _ : TypeCat² -> TypeCat² *)

  Program Definition ToTheS (T : ord_choiceType) : ord_functor TypeCat TypeCat :=
    mkOrdFunctor (fun A => (T -> A)) _ _ _ _.
  Next Obligation.
    move=> T A B. cbv. move=> f1 f2. move=> H12. move=> g. apply boolp.funext.
    move=> t. destruct (H12 (g t)). reflexivity.
  Qed.

  Let TypeCat_squ := prod_cat TypeCat TypeCat.

  Definition binaryToTheS : ord_functor TypeCat_squ TypeCat_squ :=
    prod_functor (ToTheS S1) (ToTheS S2).

  Let R := binaryToTheS.

  Let J := prod_functor (choice_incl) (choice_incl).

  (*Now we exhibit the transforming adjunction J ∘ Lflat ⊣ R*)

  Let Chi_DomainStateAdj0 :   forall A : prod_cat (oppo (prod_cat ord_choiceType ord_choiceType)) (prod_cat TypeCat TypeCat),
  OrdCat ⦅ leftHom (ord_functor_comp Lflat J) A; rightHom J R A ⦆.
    move=> [[C1 C2][X1 X2]]. simpl. unshelve econstructor.
    move=> [p q]. split. move=> c1 s1. apply p. exact (c1 , s1).
    move=> c2 s2. apply q. exact (c2,s2).
    simpl. cbv. intuition. apply boolp.funext. move=> s1.
    eapply H0.
    apply boolp.funext. move=> s2. eapply H1.
  Defined.


  Program Definition Chi_DomainStateAdj : leftAdjunctionSituation J (ord_functor_comp Lflat J) R :=
    mkNatIso _ _ (Chi_DomainStateAdj0) _ _ _ _.
  Next Obligation.
    move=> [C1 C2]. unshelve econstructor. simpl.
    move=> [p q]. split. move=> [c1 s1]. eapply p. exact c1. exact s1.
    move=> [c1 s2]. eapply q. exact c1. exact (s2).
    cbv. intuition. move: H0. move=> /(_ a) H0. destruct H0. reflexivity.
    move: H1. move=> /(_ a) H1. destruct H1. reflexivity.
  Defined.
  Next Obligation.
    move=> [[C1 C2] [A1 A2]].
    move=> [[C1' C2'] [A1' A2']].
    move=> [f f'].
    apply sig_eq. simpl. apply funext. move=> [p q].
    simpl. f_equal.
  Qed.
  Next Obligation.
    move=> [[C1 C2] [A1 A2]].
    apply sig_eq. simpl.
    apply funext. move=> [bla1 bla2].
    simpl. reflexivity.
  Qed.
  Next Obligation.
    move=> [[C1 C2] [A1 A2]].
    apply sig_eq. simpl.
    apply funext. move=> [bla1 bla2].
    simpl. f_equal. apply funext. move=> [c1 s1]. reflexivity.
      apply funext. move=> [c2 s2]. reflexivity.
  Qed.

  Definition StT_rFreeProb_squ :=
    AdjTransform (rFreeProb_squ) Lflat R Chi_DomainStateAdj.

End DomainStateAdj.


(*
Lflat = _ × (S1,S2) : chty² → chty²
monad to transform = relational spec monad : chty² → Preorder ("OrdCat")
R = S1×S2 → _ :  Preorder → Preorder
*)
Section CodomainStateAdj.
  Context (S1 S2 : ord_choiceType).

  Let S := chDiscr (F_choice_prod ⟨S1 , S2⟩).

  Let J := ord_functor_comp F_choice_prod chDiscr.
  Let Lflat := binaryTimesS S1 S2.

  Let SConst := mkConstFunc OrdCat (oppo OrdCat) S.
  Let Ordid := ord_functor_id OrdCat.
  Let preHom := functor_to_prod_cat SConst Ordid.
  Definition ToTheS_OrdCat : ord_functor OrdCat OrdCat :=
    ord_functor_comp preHom (HomF OrdCat).

  Let R := ToTheS_OrdCat.

  Definition Chi_CodomainStateAdj0 :
  forall A : prod_cat (oppo (prod_cat ord_choiceType ord_choiceType)) OrdCat,
  OrdCat ⦅ leftHom (ord_functor_comp Lflat J) A; rightHom J R A ⦆.
    move=> [[C1 C2] O]. unshelve econstructor.
    simpl. move=> [p pp]. unshelve econstructor.
    move=> [c1 c2]. unshelve econstructor.
    move=> [s1 s2]. apply p. easy.
    (*Proper*)
    move=> [s1 s2] [s1' s2'] Hs.
    epose (Hs1 := (f_equal fst Hs)). simpl in Hs1. rewrite Hs1.
    epose (Hs2 := (f_equal snd Hs)). simpl in Hs2. rewrite Hs2.
    reflexivity.
    (*Proper*)
    cbv ; intuition. destruct H. reflexivity.
    move=> [bla Hb] [bla' Hb']. move=> Hbla. simpl.
    move=> [c1 c2] [s1 s2]. simpl.
    cbv in Hbla. apply Hbla.
  Defined.

  Definition invChi_CodomainStateAdj0 :
  forall A : prod_cat (oppo (prod_cat ord_choiceType ord_choiceType)) OrdCat,
                  OrdCat ⦅ rightHom J R A; leftHom (ord_functor_comp Lflat J) A ⦆.
    move=> [[C1 C2] O]. unshelve econstructor. simpl.
    move=> [gg gproof]. unshelve econstructor. move=> [[c1 s1] [c2 s2]].
    unshelve eapply ((gg _)∙1). exact (c1,c2). exact (s1,s2).
    move=> [[c1 s1] [c2 s2]]. move=> [[c1' s1'] [c2' s2']].
    move=> [Hc1 Hs1 Hc2 Hs2]. rewrite Hc1 Hs1 Hc2 Hs2. reflexivity.
    move=> [bla Hb] [bla' Hb']. move=> Hbla. simpl.
    move=> [[c1 s1] [c2 s2]]. cbv in Hbla. apply Hbla.
  Defined.


  Program Definition Chi_CodomainStateAdj : leftAdjunctionSituation J (ord_functor_comp Lflat J) R :=
    mkNatIso _ _ (Chi_CodomainStateAdj0) invChi_CodomainStateAdj0  _ _ _.
  (* Next Obligation. *)
  (*   move=> [[C1 C2] O]. unshelve econstructor. simpl. *)
  (*   move=> [gg gproof]. unshelve econstructor. move=> [[c1 s1] [c2 s2]]. *)
  (*   unshelve eapply ((gg _)∙1). exact (c1,c2). exact (s1,s2). *)
  (*   cbv. intuition. destruct H. reflexivity. *)
  (*   cbv. intuition. *)
  (* Defined. *)
  Next Obligation.
    move=> [[A1 A2] OA] [[B1 B2] OB]. simpl. move=>[[u v] [w wp] ].
    apply sig_eq ; simpl. apply funext ; move=> [topp toppAux]. simpl.
    apply sig_eq ; simpl. apply funext ; move=> [b1 b2]. simpl.
    apply sig_eq ; simpl. apply funext ; move=> [s1 s2]. simpl.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [[C1 C2] O].
    apply sig_eq ; simpl. apply funext ; move=> [gg ggAux]. simpl.
    apply sig_eq ; simpl. apply funext ; move=> [c1 c2]. simpl.
    apply sig_eq ; simpl. apply funext ; move=> [s1 s2]. simpl.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [[C1 C2] O].
    apply sig_eq ; simpl. apply funext ; move=> [gg ggAux]. simpl.
    apply sig_eq ; simpl. apply funext ; move=> [[c1 s1] [c2 s2]]. simpl.
    easy.
  Qed.

  Definition StT_WRelprop :=
    AdjTransform (WRelProp) Lflat R Chi_CodomainStateAdj.

End CodomainStateAdj.
