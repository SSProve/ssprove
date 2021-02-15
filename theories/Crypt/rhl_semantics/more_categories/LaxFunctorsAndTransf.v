From Coq Require Import Morphisms.
From Relational Require Import OrderEnrichedCategory.
From Mon Require Import SPropBase.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect boolp.
Set Warnings "notation-overridden".
From Crypt Require Import Axioms.

Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
This file defines lax functors and lax natural transformations which are
in turn used to define lax morphisms between left relative adjunctions
in the file LaxMorphismOfRelAdjunctions.v
Such lax morphisms (L_1 ⊣ R_1) → (L_2 ⊣ R_2) contain lax functors linking the
categories involved, as well as lax natural transformations (our "lax" is commonly known
as "oplax" in the literature) between those lax functors. Recall that we are always
working in an order-enriched setting, see OrderEnrichedCategory.v
*)

Section LaxFunctors.
  Context (C D : ord_category).

  Record lord_functor : Type :=
    mkLordFunctor
      { lofmapObj :> C -> D
      ; lofmap : forall {A B}, C⦅A;B⦆ -> D⦅lofmapObj A;lofmapObj B⦆
      ; lofmap_proper : forall A B, Proper (@ord_cat_le C A B ==> @ord_cat_le D _ _) lofmap
      ; lord_functor_law1 : forall A, lofmap (Id A) ⪷ Id _
      ; lord_functor_law2 : forall (X Y Z: C) (g : C⦅X;Y⦆) (f:C⦅Y;Z⦆),
          lofmap (f ∙ g) ⪷ (lofmap f) ∙ (lofmap g)
      }.

End LaxFunctors.

Arguments mkLordFunctor {_ _} _ _ _ _ _.
Arguments lofmap {_ _} _ {_ _} _.


Section LaxFunctorComposition.
  Context {C D E : ord_category} (F : lord_functor C D) (G : lord_functor D E).
  Program Definition lord_functor_comp : lord_functor C E :=
    mkLordFunctor (fun A => G (F A)) (fun A B f=> lofmap G (lofmap F f)) _ _ _.
  Next Obligation. cbv ; intuition; do 2 apply: lofmap_proper=> //. Qed.
  Next Obligation.
    move=> A. transitivity (lofmap G (Id (F A))). eapply lofmap_proper.
    eapply lord_functor_law1. eapply lord_functor_law1.
  Qed.
  Next Obligation.
    move=> X Y Z f g. transitivity ( lofmap G ( (lofmap F g) ∙ (lofmap F f) ) ).
    eapply lofmap_proper. eapply lord_functor_law2. eapply lord_functor_law2.
  Qed.

End LaxFunctorComposition.


Section TTest.

Record Sample := {
  SA : nat;
  SB : nat;
  SCond : SA <> SB }.

Goal forall (a b : Sample), SA a = SA b -> SB a = SB b -> a = b.
  Proof.
  move=> [x1 y1 p1] [x2 y2 p2]. simpl. move=> Hx Hy.
  revert p1 p2.
  rewrite Hx Hy. move=> p1 p2.
  rewrite (proof_irrelevance _ p1 p2).
  f_equal.
  Qed.

End TTest.


Section FromStrictToLaxFunctors.
  Context {C D : ord_category}.

  Program Definition strict2laxFunc (F : ord_functor C D) : lord_functor C D :=
    @mkLordFunctor C D F _ _ _ _.
  Next Obligation.
    move=> F A. rewrite ord_functor_law1. reflexivity.
  Qed.
  Next Obligation.
    move=> F X Y Z f g. rewrite ord_functor_law2. reflexivity.
  Qed.

End FromStrictToLaxFunctors.



(*
The next ingredient to define lax morphisms between relative adjunctions is the notion of lax natural transformation between lax functors.
*)
Section LaxNaturalTransformations.
  Context {C D : ord_category} (F G : lord_functor C D).

  Record lnatTrans :=
    mkLnatTrans
      { lnt_map :> forall {A}, D⦅F A;G A⦆
      ; lnt_lnatural : forall {A B} (f : C⦅A ; B⦆),
           lnt_map ∙ lofmap F f ⪷ lofmap G f ∙ lnt_map
      }.

End LaxNaturalTransformations.

Arguments mkLnatTrans {_ _ _ _}.


Section LaxNaturalTransformationComp.
  Context {C D : ord_category} {F G H : lord_functor C D}
          (phi : lnatTrans F G) (psi : lnatTrans G H).

  Program Definition lnatTrans_comp : lnatTrans F H :=
    mkLnatTrans (fun A => psi A ∙ phi A) _.
  Next Obligation.
    move=> A B f.
    rewrite -ord_cat_law3. transitivity ( psi B ∙ ((lofmap G f) ∙ phi A) ).
    eapply Comp_proper. reflexivity.
    eapply lnt_lnatural.
    rewrite ord_cat_law3. transitivity ((lofmap H f ∙ psi A) ∙ phi A).
    eapply Comp_proper. eapply lnt_lnatural. reflexivity.
    rewrite -ord_cat_law3. reflexivity.
  Qed.

End LaxNaturalTransformationComp.


(*
Because lord_functor's are record types, its difficult to prove equality
between them. For example the associativity property for composition of
lord_functors uses such an equality. Instead of equality we use a
notion of isomophism between lax functors. It is defined as an
invertible lax transformation between the two functors, and it
turns out that the naturality square holds strictly (not only laxly)
/!\ in our case "strictly" means up to antisymmetry classes of ⪷ , the order on morphisms...
*)
Section LaxFunctorIso.
  Context {C D : ord_category} (F G : lord_functor C D).

  Record lnatIso :=
    mkLnatIso
      { lni_trans :> lnatTrans F G
      ; lni_invTrans : lnatTrans G F
      ; lni_rightinv : forall {A}, (lnt_map _ _ lni_trans) ∙ (lnt_map _ _ lni_invTrans) = Id (G A)
      ; lni_leftinv : forall {A}, (lnt_map _ _ lni_invTrans) ∙ (lnt_map _ _ lni_trans) = Id (F A)
      }.

End LaxFunctorIso.

Arguments mkLnatIso {_ _ _ _}.
Arguments lni_trans {_ _ _ _}.
Arguments lni_invTrans {_ _ _ _}.

Section InvLnatIso.
  Context {C D : ord_category} {F G : lord_functor C D}.
  Context (phi : lnatIso F G).

  Program Definition invLnatIso : lnatIso G F :=
    mkLnatIso (lni_invTrans phi) (lni_trans phi) _ _.
  Next Obligation.
    move=> A. eapply (lni_leftinv _ _ phi).
  Qed.
  Next Obligation.
    move=> A. eapply (lni_rightinv _ _ phi).
  Qed.

End InvLnatIso.


Section LaxFunctorAssoc.
  Context {C D E M : ord_category}
          (F : lord_functor C D) (G : lord_functor D E) (H : lord_functor E M).

  Program Definition lord_functor_assoc : lnatIso
     (lord_functor_comp (lord_functor_comp F G) H)
     (lord_functor_comp F (lord_functor_comp G H))
    := mkLnatIso _ _ _ _.
  Next Obligation.
    unshelve econstructor. simpl. move=> A. eapply Id.
    move=> A B f. simpl.
    rewrite ord_cat_law1. rewrite ord_cat_law2. reflexivity.
  Defined.
  Next Obligation.
    unshelve econstructor. move=> A. simpl. eapply Id.
    move=> A B f. simpl.
    rewrite ord_cat_law2. rewrite ord_cat_law1.
    reflexivity.
  Defined.
  Next Obligation.
    move=> A. rewrite ord_cat_law2. reflexivity.
  Qed.
  Next Obligation.
    move=> A. rewrite ord_cat_law2. reflexivity.
  Qed.

End LaxFunctorAssoc.

(*
If phi is a lax natural transformation, and H a (strict) functor, the whiskered H (phi) lax natural transformation exists. But if H is lax it does not!
*)
Section LaxNaturalTransformationRightWhiskering.
  Context {C D E: ord_category} {F G : lord_functor C D} (H : ord_functor D E)
          (phi : lnatTrans F G).

  Program Definition lnatTrans_whisker_right :
  lnatTrans (lord_functor_comp F (strict2laxFunc H)) (lord_functor_comp G (strict2laxFunc H)) :=
    mkLnatTrans (fun A => ofmap H (phi A)) _.
  Next Obligation.
    move=> A B f. rewrite -ord_functor_law2. rewrite -ord_functor_law2.
    eapply ofmap_proper. eapply lnt_lnatural.
  Qed.
End LaxNaturalTransformationRightWhiskering.


(*
No such limitations apply to the other case: left whiskering phi_H
*)
Section LaxNaturalTransformationLeftWhiskering.
  Context {C D E: ord_category} {F G : lord_functor D E}
          (phi : lnatTrans F G) (H : lord_functor C D).

  Program Definition lnatTrans_whisker_left :
  lnatTrans (lord_functor_comp H F) (lord_functor_comp H G) :=
    mkLnatTrans (fun A => phi (H A)) _.
  Next Obligation.
    move=> A B f. eapply lnt_lnatural.
  Qed.
End LaxNaturalTransformationLeftWhiskering.


Section PastingTwoLaxSquares.
  Context {I1 D1 C1 I2 D2 C2 : ord_category}
          {L1 : ord_functor I1 D1} {R1 : ord_functor D1 C1}
          {L2 : ord_functor I2 D2} {R2 : ord_functor D2 C2}
          {KI : ord_functor I1 I2}
          {KC : ord_functor C1 C2}
          {KD : lord_functor D1 D2}.
  Let lKC := strict2laxFunc KC.
  Let lKI := strict2laxFunc KI.
  Let lL1 := strict2laxFunc L1. Let lR1 := strict2laxFunc R1.
  Let lL2 := strict2laxFunc L2. Let lR2 := strict2laxFunc R2.

  Let KDoL1 := lord_functor_comp lL1 KD.
  Let L2oKI := lord_functor_comp lKI lL2.
  Context (alpha : lnatTrans KDoL1 L2oKI).

  Let KCoR1 := lord_functor_comp lR1 lKC.
  Let R2oKD := lord_functor_comp KD lR2.
  Context (beta : lnatTrans KCoR1 R2oKD).

  Let KCoR1oL1 := lord_functor_comp lL1 KCoR1.
  Let R2oL2oKI := lord_functor_comp L2oKI lR2.
  Let R2oKDoL1 := lord_functor_comp lL1 R2oKD.
  Program Definition paste : lnatTrans KCoR1oL1 R2oL2oKI :=
    @lnatTrans_comp _ _ _ R2oKDoL1 _ _ _.
  Next Obligation.
    eapply lnatTrans_whisker_left. eapply beta.
  Defined.
  Next Obligation.
    eapply lnatTrans_comp. exact (invLnatIso (lord_functor_assoc lL1 KD lR2)).
    unfold R2oL2oKI.
    eapply lnatTrans_whisker_right. eapply alpha.
  Defined.

End PastingTwoLaxSquares.

Section lPastingTwoLaxSquares.
  Context {I1 D1 C1 I2 D2 C2 : ord_category}
          {L1 : ord_functor I1 D1} {R1 : ord_functor D1 C1}
          {L2 : ord_functor I2 D2} {R2 : ord_functor D2 C2}
          {KI : lord_functor I1 I2}
          {KC : lord_functor C1 C2}
          {KD : lord_functor D1 D2}.
  Let lL1 := strict2laxFunc L1. Let lR1 := strict2laxFunc R1.
  Let lL2 := strict2laxFunc L2. Let lR2 := strict2laxFunc R2.

  Let KDoL1 := lord_functor_comp lL1 KD.
  Let L2oKI := lord_functor_comp KI lL2.
  Context (alpha : lnatTrans KDoL1 L2oKI).

  Let KCoR1 := lord_functor_comp lR1 KC.
  Let R2oKD := lord_functor_comp KD lR2.
  Context (beta : lnatTrans KCoR1 R2oKD).

  Let KCoR1oL1 := lord_functor_comp lL1 KCoR1.
  Let R2oL2oKI := lord_functor_comp L2oKI lR2.
  Let R2oKDoL1 := lord_functor_comp lL1 R2oKD.
  Program Definition lpaste : lnatTrans KCoR1oL1 R2oL2oKI :=
    @lnatTrans_comp _ _ _ R2oKDoL1 _ _ _.
  Next Obligation.
    eapply lnatTrans_whisker_left. eapply beta.
  Defined.
  Next Obligation.
    eapply lnatTrans_comp. exact (invLnatIso (lord_functor_assoc lL1 KD lR2)).
    unfold R2oL2oKI.
    eapply lnatTrans_whisker_right. eapply alpha.
  Defined.

End lPastingTwoLaxSquares.


Section FromStrict2LaxTransf.
  Context {C D : ord_category}.
  Context {F G : ord_functor C D}.
  Context (phi : natIso F G).

  Let lF := strict2laxFunc F. Let lG := strict2laxFunc G.
  Program Definition strict2laxTransf : lnatTrans lF lG := mkLnatTrans _ _.
  Next Obligation.
    exact phi.
  Defined.
  Next Obligation.
    intuition. cbv. rewrite (ni_natural). reflexivity.
  Qed.

End FromStrict2LaxTransf.




