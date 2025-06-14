From Stdlib Require Import Relation_Definitions.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Mon Require Import SPropBase.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms OrderEnrichedRelativeAdjunctions LaxFunctorsAndTransf LaxMorphismOfRelAdjunctions.

Import SPropNotations.


(*
In this file we implement the following transformations:
- Start with a lax relative monad morphism θ : M1 → M2
- You can obtain a lax morphism of left relative adjunctions between the Kleisli adjunctions:
  Kθ : (L^M1 ⊣ R^M1) → (L^M2 ⊣ R^M2)
- Then transform this morphism to get a new morphism between the transformed left relative adjunctions:
  (L^M1 ∘ L♭ ⊣ R1 ∘ R^M1) → (L^M2 ∘ L♭ ⊣ R2 ∘ R^M2)
- From this we deduce a lax morpihsm between the associated relative monads:
  R1 ∘ M1 ∘ L♭ → R2 ∘ M2 ∘ L♭
*)


Section OrdCatLe.
  Context {C : ord_category}.
  Context {X Y Z : C}.
  Context (f f' : C⦅X ; Y⦆) (g g' : C⦅Y ; Z⦆).
  Lemma ord_cat_le_comp : f ⪷ f' -> g ⪷ g' -> g ∙ f ⪷ g' ∙ f'.
  Proof.
    move=> Hf Hg. eapply Comp_proper. assumption. assumption.
  Qed.


End OrdCatLe.


(*
Take two relative monads and a lax morphism between them. For instance
θ : Prob × Prob → SomeSpecRmonad. Based on θ, we begin by building a lax morphism
between the associated Kleisli relative ajdunctions.
*)
Section LaxMorphBetwKleislis.
  Context {I : ord_category}. (* both rmonads share the same index cat *)
  Context {C1 :ord_category} {J1 : ord_functor I C1} {M1 : ord_relativeMonad J1}.
  Context {C2 :ord_category} {J2 : ord_functor I C2} {M2 : ord_relativeMonad J2}.

  (*  We pack the first Kleisli adjunction  *)
  Let kadj1 := mkLeftAdjunction
  I (relKleisli M1) C1 J1 (KleisliLeftAdjoint M1) (KleisliRightAdjoint M1) (ChiKleisli M1).
  (* and the second *)
  Let kadj2 := mkLeftAdjunction
  I (relKleisli M2) C2 J2 (KleisliLeftAdjoint M2) (KleisliRightAdjoint M2) (ChiKleisli M2).


  Context {KC : ord_functor C1 C2}.
  Context  {bIso : natIso J2 (ord_functor_comp J1 KC)}.

  Context (smTheta :  relativeLaxMonadMorphism KC bIso M1 M2).


  Program Definition Kl_Lfunc : lord_functor (lad_D kadj1) (lad_D kadj2) :=
    mkLordFunctor (fun A => A)  _ _ _ _.
  Next Obligation.
    move=> A B f.
    exact ( smTheta B ∙ (ofmap KC f) ∙ bIso A ).
  Defined.
  Next Obligation.
    move=> A B. move=> f f'. cbv. move=> Hf.
    eapply Comp_proper. eapply Comp_proper.
    reflexivity. eapply ofmap_proper. assumption.
    reflexivity.
  Qed.
  Next Obligation.
    move=> A. cbv. pose (smTheta_laxRet := (rlmm_law1 _ _ _ _ smTheta) A).
    unshelve eapply Comp_proper in smTheta_laxRet. exact (J2 A).
    cbv in smTheta_laxRet.
    move: smTheta_laxRet => /(_ (bIso A) (bIso A)) smTheta_laxRet.
    specialize (smTheta_laxRet ltac: (reflexivity)).
    transitivity ((ord_relmon_unit M2 A ∙ ni_inv bIso A) ∙ bIso A).
    eapply smTheta_laxRet.
    rewrite -ord_cat_law3. rewrite ni_leftinv. rewrite ord_cat_law2.
    reflexivity.
  Qed.
  Next Obligation.
    move=> X Y Z f f'. cbv. rewrite ord_cat_law3. eapply Comp_proper.
    rewrite (ord_functor_law2 _ _ KC). do 2 rewrite ord_cat_law3.
    eapply Comp_proper. eapply rlmm_law2.
    reflexivity. reflexivity.
  Qed.


  Program Definition bbIso :
  natIso (ord_functor_comp (ord_functor_id I) (lad_J kadj2)) (ord_functor_comp (lad_J kadj1) KC).
    eapply natIso_comp. all: swap 1 2. exact (bIso).
    simpl.
    eapply ord_functor_unit_left.
  Defined.

  Notation η := ord_relmon_unit.


  Program Definition Kl_alpha :
  lnatTrans (lord_functor_comp (strict2laxFunc (lad_L kadj1)) Kl_Lfunc)
            (lord_functor_comp (strict2laxFunc (ord_functor_id I))
                             (strict2laxFunc (lad_L kadj2))) :=
    mkLnatTrans _ _.
  Next Obligation.
    exact (η M2).
  Defined.
  Next Obligation.
    intuition. cbv.
    rewrite ord_relmon_law1. rewrite ord_cat_law1.
    rewrite ord_relmon_law2.
    rewrite (ord_functor_law2 _ _ KC).
    rewrite ord_cat_law3.
    assert ( compassoc :
((smTheta B ∙ ofmap KC (η M1 B)) ∙ ofmap KC (ofmap J1 f)) ∙ bIso A
=
smTheta B ∙ ofmap KC (η M1 B) ∙ (ofmap KC (ofmap J1 f) ∙ bIso A)
).
    rewrite !ord_cat_law3. reflexivity.
    rewrite compassoc.
    transitivity (
(η M2 B ∙ (natIso_sym bIso B))  ∙ ( (ofmap KC (ofmap J1 f)) ∙ bIso A)).
    eapply Comp_proper. eapply rlmm_law1. reflexivity.
    rewrite -ord_cat_law3. cbv.
    move: bIso => [bIso_map bIso_inv bIso_nat bIso_law2 bIso_law3].
    cbv in bIso_nat. rewrite -bIso_nat.
    do 2 rewrite ord_cat_law3.
    eapply Comp_proper.
    rewrite -ord_cat_law3. rewrite bIso_law3. rewrite ord_cat_law2.
    reflexivity. reflexivity.
  Qed.

  Program Definition Kl_beta : lnatTrans
                        (lord_functor_comp (strict2laxFunc (lad_R kadj1)) (strict2laxFunc KC))
                        (lord_functor_comp Kl_Lfunc (strict2laxFunc (lad_R kadj2))) :=
    mkLnatTrans _ _.
  Next Obligation.
    exact smTheta.
  Defined.
  Next Obligation.
    cbv. intuition. eapply rlmm_law2.
  Qed.


  Program Definition kleisliLaxMorph : LaxMorphLeftAdj kadj1 kadj2 :=
    mkLaxMorphLeftAdj kadj1 kadj2 Kl_Lfunc KC bIso Kl_alpha Kl_beta _ _.
  Next Obligation.
    cbv ; intuition.
    rewrite !ord_cat_law2. rewrite ord_relmon_law1. rewrite ord_cat_law1.
    transitivity ((η M2 A ∙ (natIso_sym bIso A)) ∙ bIso A).
    eapply Comp_proper. eapply rlmm_law1.
    reflexivity.
    rewrite -ord_cat_law3. cbv. move: bIso => [bIso_map bIso_inv bIso_nat bIso_law1 bIso_law2].
    rewrite bIso_law2. rewrite ord_cat_law2.
    reflexivity.
  Qed.
  Next Obligation.
    cbv ; intuition. rewrite ord_relmon_law2.
    reflexivity.
  Qed.


End LaxMorphBetwKleislis.

(*
From a left relative adjunction we can deduce a relative monad
Similarly from a lax morphism of left relative adjunctions we can
deduce a lax morphism of relative monads.
We implement the latter fact in the following section.
*)
Section FromLaxMorphAdj_TO_LaxMorphRmon.
  Context {I : ord_category}.
  Context {adj1 adj2 : leftAdjunction I}.
  Context (smK : LaxMorphLeftAdj adj1 adj2).

  (*We want to build a lax morphism of relative monads between those two:*)
  Let smM1 := relMon_fromLeftAdj (lad_J adj1) (lad_L adj1) (lad_R adj1) (lad_strucIso adj1).
  Let smM2 := relMon_fromLeftAdj (lad_J adj2) (lad_L adj2) (lad_R adj2) (lad_strucIso adj2).



  Notation α X := (lmlad_alpha _ _ _ X).
  Notation β X := (lmlad_beta _ _ _ X).
  Notation myKC := (ofmap (lmlad_KC _ _ _)).



  (*"relative lax monad morphism from lax morphism of left adjunctions"*)
  Program Definition rlmm_from_lmla :
  relativeLaxMonadMorphism (lmlad_KC _ _ smK) (lmlad_baseIso _ _ smK) smM1 smM2 :=
    mkRelLaxMonMorph (lmlad_KC _ _ smK) (lmlad_baseIso _ _ smK) smM1 smM2 _ _ _.
  Next Obligation.
    exact (paste (lmlad_alpha _ _ smK) (lmlad_beta _ _ smK)).
  Defined.
  Next Obligation.
    unfold rlmm_from_lmla_obligation_1. simpl.
    move=> A.
    pose Hlrp := (lmlad_laxRetPres _ _ smK). move: Hlrp => /(_ A) Hlrp.
    simpl in Hlrp. rewrite ord_cat_law2 in Hlrp.
    rewrite ord_cat_law2.
    transitivity (
((ofmap (lad_R adj2) (lmlad_alpha adj1 adj2 smK A) ∙ lmlad_beta adj1 adj2 smK (lad_L adj1 A))
          ∙ ofmap (lmlad_KC adj1 adj2 smK)
              (OrderEnrichedRelativeAdjunctions.relMon_fromLeftAdj_obligation_1
                 (lad_J adj1) (lad_L adj1) (lad_R adj1) (lad_strucIso adj1) A))
         ∙ (lmlad_baseIso adj1 adj2 smK A ∙  ni_inv (lmlad_baseIso adj1 adj2 smK) A)
).
    rewrite ni_rightinv ord_cat_law2. reflexivity.
    rewrite ord_cat_law3. eapply Comp_proper.
    eapply Hlrp.
    reflexivity.
  Qed.
  Next Obligation.
    (*cleaning*)
    simpl ; move=> A B f.
    unfold rlmm_from_lmla_obligation_1. simpl.
    rewrite !ord_cat_law2.
    unfold OrderEnrichedRelativeAdjunctions.relMon_fromLeftAdj_obligation_2.
    unfold bind_fromLeftAdj.
    (*use beta lax naturality*)
    unshelve epose (betaNat := lnt_lnatural _ _ (lmlad_beta _ _ smK)   ).
      exact (lad_L adj1 A). exact (lad_L adj1 B).
    rewrite -ord_cat_law3. simpl in betaNat.
    specialize (betaNat ((ni_inv (lad_strucIso adj1) ⟨ A, lad_L adj1 B ⟩) ∙1 f)).
    transitivity (
  ofmap (lad_R adj2) (lmlad_alpha adj1 adj2 smK B)
  ∙ ( ofmap (lad_R adj2)
                (lofmap (lmlad_KD adj1 adj2 smK)
                   ((ni_inv (lad_strucIso adj1) ⟨ A, lad_L adj1 B ⟩) ∙1 f))
              ∙ lmlad_beta adj1 adj2 smK (lad_L adj1 A) )
).
    eapply Comp_proper. reflexivity.
    eapply betaNat. clear betaNat.
    (*R2 functoriality*)
    rewrite [ofmap (lad_R adj2) (lmlad_alpha adj1 adj2 smK B) ∙ _] ord_cat_law3.
    rewrite -ord_functor_law2.
    (*KD = ... ; structural iso preservation of smK*)
    pose (myIsoPres := (lmlad_StrucIsoPres _ _ smK)).
    specialize (myIsoPres _ _ ((ni_inv (lad_strucIso adj1) ⟨ A, lad_L adj1 B ⟩) ∙1 f)).
    simpl in myIsoPres. rewrite myIsoPres. clear myIsoPres.
    rewrite [α B ∙ _] ord_cat_law3.
    rewrite [ofmap (lad_R adj2) (_ ∙ α A)] ord_functor_law2.
    rewrite -[(_ ∙ (ofmap (lad_R adj2) (α A))) ∙ β (lad_L adj1 A)] ord_cat_law3.
    (*phi ( phi-1 f ) = f*)
    unshelve epose (rmv_natIso := (ni_rightinv _ _ (lad_strucIso adj1)) ).
      exact ( ⟨ A, lad_L adj1 B ⟩ ).
    simpl in rmv_natIso.
    eapply (f_equal sval) in rmv_natIso. simpl in rmv_natIso.
    unshelve eapply (equal_f) in rmv_natIso.
      exact f.
    simpl in rmv_natIso.
    rewrite rmv_natIso. clear rmv_natIso.
    (*focus on the left part of the members. the right parts are the same*)
    eapply Comp_proper. all: swap 1 2. reflexivity.
    (* f <= f' -> R2 f <= R2 f' *)
    eapply ofmap_proper.
    (*use phi2-1 naturality...*)
    unshelve epose ( Hnat := (ni_natural _ _ (natIso_sym (lad_strucIso adj2)))).
      exact ( ⟨ A, lmlad_KD adj1 adj2 smK (lad_L adj1 B) ⟩ ).
      exact ( ⟨ A, (lad_L adj2) B ⟩ ).
    unshelve epose ( Hnat' := Hnat _).
      unshelve econstructor.
        simpl. eapply Id.
        exact ((lmlad_alpha _ _ smK) B).
    eapply (f_equal sval) in Hnat'. simpl in Hnat'. clear Hnat.
    unfold OrderEnrichedRelativeAdjunctions.oppoF_obligation_1 in Hnat'.
    move: Hnat'. rewrite !ord_functor_law1. move=> Hnat'.
    unshelve eapply equal_f in Hnat'.
      exact (
  (lmlad_beta _ _ smK) (lad_L adj1 B) ∙ ( ofmap (lmlad_KC _ _ smK) f ∙ (lmlad_baseIso _ _ smK) A)
).
    simpl in Hnat'. rewrite !ord_cat_law2 in Hnat'. rewrite -ord_cat_law3.
    rewrite -Hnat'. clear Hnat'.
    rewrite -!ord_cat_law3. reflexivity.
  Qed.


End FromLaxMorphAdj_TO_LaxMorphRmon.


(*
Start with two rmonads and a lax relative monad morphism between them.

*)

Section TransformedLaxMorphAdj.


  Context {I : ord_category} {Lflat : ord_functor I I}.

  (*The first monad*)
  Context {C1 : ord_category} {J1 : ord_functor I C1}.
  Context {M1 : ord_relativeMonad J1}.
  Context {R1 : ord_functor C1 C1}.

  (*The second monad and the second transforming adjunction*)
  Context {C2 : ord_category} {J2 : ord_functor I C2}.
  Context {M2 : ord_relativeMonad J2}.
  Context {R2 : ord_functor C2 C2}.

  (*We have a lax relative monad morphism theta that we wish to transform*)
  Context {KC : ord_functor C1 C2}.
  Context {chi :  natIso J2 (ord_functor_comp J1 KC)}.
  Context (theta :  relativeLaxMonadMorphism KC chi M1 M2).

  (*The first transforming adjunction, and the first transformed adjunction *)
  Context (Chi_RJLflat_1 : leftAdjunctionSituation J1 (ord_functor_comp Lflat J1) R1).
    (*we pack the first transforming adjunction into a record *)
  Let TingAdj1 :=  mkLeftAdjunction I C1 C1 J1 (ord_functor_comp Lflat J1) R1 Chi_RJLflat_1.
  (*The first transformed adjunction *)
  Let tradj1_0 := TransformedAdjunction M1 Lflat R1 Chi_RJLflat_1.
    (*we pack it into a record type (see leftAdjunction)*)
  Let tradj1 :=
  mkLeftAdjunction I (relKleisli M1) C1 J1
  (ord_functor_comp Lflat (KleisliLeftAdjoint M1))
  (ord_functor_comp (KleisliRightAdjoint M1) R1) tradj1_0.

  (*The second transforming adjunction and the second transformed adjunction*)
  Context (Chi_RJLflat_2 : leftAdjunctionSituation J2 (ord_functor_comp Lflat J2) R2).
    (*we pack the second transforming adjunction into a record *)
  Let TingAdj2 :=  mkLeftAdjunction I C2 C2 J2 (ord_functor_comp Lflat J2) R2 Chi_RJLflat_2.
  (*The second transformed adjunction *)
  Let tradj2_0 := TransformedAdjunction M2 Lflat R2 Chi_RJLflat_2.
    (*we pack it into a record type (see leftAdjunction)*)
  Let tradj2 :=
  mkLeftAdjunction I (relKleisli M2) C2 J2
  (ord_functor_comp Lflat (KleisliLeftAdjoint M2))
  (ord_functor_comp (KleisliRightAdjoint M2) R2) tradj2_0.

  (*we begin by extending it into a lax morphism between the Kleisli adjunctions*)
  Let myKtheta :=  kleisliLaxMorph theta.


  (*We also have a "transforming" lax morphism between the 2 transforming adjunctions
   (state relative adjunctions in concrete cases). This lax morphism is compliant with
  the base natural iso of theta, in the sense that its left lax cell is a whiskered inverse
  of chi (= the base nat iso of theta) *)
  Let invChi := strict2laxTransf (natIso_sym chi).
  Let invChiLflat := lnatTrans_whisker_left invChi (strict2laxFunc Lflat).
  Program Definition smAlpha' :
  lnatTrans (lord_functor_comp (strict2laxFunc (lad_L TingAdj1)) (strict2laxFunc KC))
      (lord_functor_comp (strict2laxFunc (ord_functor_id I))
                             (strict2laxFunc (lad_L TingAdj2))) :=
    mkLnatTrans invChiLflat _.
  Next Obligation.
    move=> A B f. pose chiInvNat := (ni_natural _ _ (natIso_sym chi) (ofmap Lflat f)).
    simpl in chiInvNat. rewrite chiInvNat. reflexivity.
  Qed.

  Context (smBeta' : lnatTrans (lord_functor_comp (strict2laxFunc R1) (strict2laxFunc KC))
         (lord_functor_comp (strict2laxFunc KC) (strict2laxFunc R2)) ).

  Hypothesis (laxUnitPres' :
forall A : I,
        (paste smAlpha' smBeta' A
         ∙ lofmap (strict2laxFunc KC)
             (ord_relmon_unit
                (relMon_fromLeftAdj J1 (ord_functor_comp Lflat J1) R1
                   (Chi_RJLflat_1)) A)) ∙ chi A
        ⪷ ord_relmon_unit
            (relMon_fromLeftAdj J2 (ord_functor_comp Lflat J2) R2
               Chi_RJLflat_2) A).


  Hypothesis (StrucIsoPres' :
forall (A : I) (Y : C1) (f : C1 ⦅ J1 (Lflat A) ; Y ⦆),
        lofmap (strict2laxFunc KC) f =
        (natIso_sym (Chi_RJLflat_2) ⟨ A, strict2laxFunc KC Y ⟩) ∙1
          ((smBeta' Y ∙ ofmap KC ((Chi_RJLflat_1 ⟨ A, Y ⟩) ∙1 f)) ∙ chi A) ∙
        smAlpha' A).

(*
  Based on the previous hypotheses there is a lax morphism between twe two transforming
  adjunctions TingAdj1 and TingAdj2. We call it smK'.
*)
  Let smK' :=  mkLaxMorphLeftAdj TingAdj1 TingAdj2 (strict2laxFunc KC) KC
  chi smAlpha' smBeta' laxUnitPres' StrucIsoPres'.


(*
some useful notations in this section
*)

  Notation dnib := (ord_relmon_bind _).
  Notation η := (ord_relmon_unit _).
  Notation Φ1':= ( (Chi_RJLflat_1 _) ).
  Notation Φ2':= ( (Chi_RJLflat_2 _) ).


(*
  And now we have to build the transformed lax morphism.
  We want to build a lax morphism, of this type:
*)
  (*  LaxMorphLeftAdj tradj1 tradj2. *)

  (*Here is its top lax functor*)
  Let Kl_Lfunc_filled :=
  @Kl_Lfunc _ _ _ M1 _ _ M2 KC chi theta.

  (*Here is its left lax cell alpha''*)
  (* Check lmlad_alpha _ _ myKtheta. *)
  (* Check mkLaxMorphLeftAdj tradj1 tradj2 Kl_Lfunc_filled KC chi. *)

  Program Definition pre_smAlpha'' :
  lnatTrans (lord_functor_comp (strict2laxFunc (lad_L tradj1)) Kl_Lfunc_filled)
            (lord_functor_comp
               (strict2laxFunc Lflat)
               (lord_functor_comp (strict2laxFunc (KleisliLeftAdjoint M1)) (Kl_Lfunc theta))) :=
    mkLnatTrans _ _.
  Next Obligation.
    move=> A. exact ( η (Lflat A) ).
  Defined.
  Next Obligation.
    rewrite /OrderEnrichedRelativeAdjunctions.relKleisli_obligation_2.
    rewrite /Kl_Lfunc_obligation_1.
    rewrite /pre_smAlpha''_obligation_1.
    move=> A B f. rewrite ord_relmon_law1. rewrite ord_cat_law1.
    rewrite ord_relmon_law2. reflexivity.
  Qed.

  Program Definition post_smAlpha'' :
  lnatTrans (lord_functor_comp (strict2laxFunc Lflat)
                               (lord_functor_comp (strict2laxFunc (ord_functor_id I))
                                                  (strict2laxFunc (KleisliLeftAdjoint M2))))
            (lord_functor_comp (strict2laxFunc (ord_functor_id I))
                             (strict2laxFunc (lad_L tradj2))) :=
    mkLnatTrans _ _.
  Next Obligation.
    move=> A. exact ( η (Lflat A) ).
  Defined.
  Next Obligation.
    rewrite /OrderEnrichedRelativeAdjunctions.relKleisli_obligation_2.
    rewrite /post_smAlpha''_obligation_1.
    move=> A B f. rewrite ord_relmon_law1. rewrite ord_cat_law1.
    rewrite ord_relmon_law2. reflexivity.
  Qed.

  Let PPre_smAlpha'' :=  lnatTrans_comp
          pre_smAlpha''
          ( lnatTrans_whisker_left (lmlad_alpha _ _ myKtheta) (strict2laxFunc Lflat) ).
  Definition smAlpha'' :
  lnatTrans (lord_functor_comp (strict2laxFunc (lad_L tradj1)) Kl_Lfunc_filled)
                          (lord_functor_comp (strict2laxFunc (ord_functor_id I))
                             (strict2laxFunc (lad_L tradj2))) :=
    lnatTrans_comp PPre_smAlpha'' post_smAlpha''.

  (*The right cell beta'' of the transformed morphism consists of pasting the two lax cells
    beta (coming from the input Kleisli adjunction ) and beta' (coming from the transforming
    adjunction ) *)
  Let myBeta := lmlad_beta _ _ myKtheta.
  Let myBeta' := lmlad_beta _ _ smK'.
  Goal True.
    pose bla := (@lpaste (relKleisli M1) C1 C1 (relKleisli M2) C2 C2
        (KleisliRightAdjoint M1) R1 (KleisliRightAdjoint M2) R2 _ (strict2laxFunc KC) (strict2laxFunc KC) myBeta myBeta').
    simpl in bla. easy. Qed.

  Program Definition pre_smBeta'' :
  lnatTrans
    (lord_functor_comp (strict2laxFunc (lad_R tradj1)) (strict2laxFunc KC))
    (lord_functor_comp (strict2laxFunc (KleisliRightAdjoint M1))
          (lord_functor_comp (strict2laxFunc R1) (strict2laxFunc KC))) :=
    mkLnatTrans _ _.
  Next Obligation.
    move=> A. eapply Id.
  Defined.
  Next Obligation.
    move=> A B f.
    rewrite /pre_smBeta''_obligation_1. rewrite ord_cat_law2.
    rewrite ord_cat_law1.
    reflexivity.
  Qed.

  Program Definition post_smBeta'' :
  lnatTrans
    (lord_functor_comp
          (lord_functor_comp (Kl_Lfunc theta) (strict2laxFunc (KleisliRightAdjoint M2)))
          (strict2laxFunc R2))
    (lord_functor_comp Kl_Lfunc_filled (strict2laxFunc (lad_R tradj2))) :=
    mkLnatTrans _ _.
  Next Obligation.
    move=> A. eapply Id.
  Defined.
  Next Obligation.
    move=> A B f.
    rewrite /post_smBeta''_obligation_1. rewrite !ord_cat_law2.
    rewrite ord_cat_law1. reflexivity.
  Qed.

  Let PPre_smBeta'' := lnatTrans_comp
    pre_smBeta''
    (@lpaste (relKleisli M1) C1 C1 (relKleisli M2) C2 C2
        (KleisliRightAdjoint M1) R1 (KleisliRightAdjoint M2) R2 _ (strict2laxFunc KC) (strict2laxFunc KC) myBeta myBeta').

  Definition smBeta'' :
  lnatTrans
     (lord_functor_comp (strict2laxFunc (lad_R tradj1)) (strict2laxFunc KC))
     (lord_functor_comp Kl_Lfunc_filled (strict2laxFunc (lad_R tradj2)))
   := lnatTrans_comp PPre_smBeta'' post_smBeta''.



  (*Here is the transformed lax morphism of left relative adjunctions...*)
  Program Definition Transformed_lmla : LaxMorphLeftAdj tradj1 tradj2 :=
    mkLaxMorphLeftAdj tradj1 tradj2 Kl_Lfunc_filled KC chi smAlpha'' smBeta'' _ _.
  Next Obligation.
    move=> A. cbv. rewrite !ord_cat_law2.
    rewrite !ord_relmon_law1. rewrite !ord_cat_law1. rewrite !ord_relmon_law1.
    rewrite !ord_functor_law1.
    rewrite !ord_cat_law1.
    (*struc iso Φ1' in terms of right adjoint and η1'*)
    pose (sIso_eq := strucIso_rightAdj Chi_RJLflat_1 (ord_relmon_unit M1 (Lflat A))).
    cbv in sIso_eq.
    rewrite sIso_eq. clear sIso_eq.
    (*struc iso Φ2' in terms of right adjoint and η2'*)
    pose (sIso_eq := strucIso_rightAdj Chi_RJLflat_2 (ord_relmon_unit M2 (Lflat A))).
    cbv in sIso_eq. rewrite sIso_eq. clear sIso_eq.
    (*cleaning*)
    rewrite ord_functor_law2. rewrite ord_cat_law3.
    rewrite -[(_ ∙ _) ∙  ofmap KC (ofmap R1 _)]ord_cat_law3.
    (*beta' laxness*)
    pose (laxnessBeta' := lnt_lnatural _ _ smBeta' (ord_relmon_unit M1 (Lflat A))).
    simpl in laxnessBeta'. (* Check relMon_fromLeftAdj _ _ _ Chi_RJLflat_1. *)
    pose eta1' := ord_relmon_unit (relMon_fromLeftAdj _ _ _ Chi_RJLflat_1).
    pose eta1 := ord_relmon_unit M1.
    transitivity (
ofmap R2 (theta (Lflat A)) ∙
ofmap R2 ( ofmap KC (eta1 (Lflat A)) ) ∙
smBeta' (J1 (Lflat A)) ∙
ofmap KC (eta1' A) ∙
chi A
).
    rewrite -!ord_cat_law3. eapply Comp_proper. reflexivity.
    rewrite !ord_cat_law3. eapply Comp_proper. all: swap 1 2. reflexivity.
    eapply Comp_proper. all: swap 1 2. reflexivity.
    eapply laxnessBeta'.
    clear laxnessBeta'.
    (*R2 func*)
    rewrite -ord_functor_law2.
    (*theta lax unit preservation*)
    pose (thetaUnitLaxness  := rlmm_law1 _ _ _ _ theta (Lflat A)).
    etransitivity.
    eapply Comp_proper. all: swap 1 2. reflexivity.
    eapply Comp_proper. all: swap 1 2. reflexivity.
    eapply Comp_proper. all: swap 1 2. reflexivity.
    eapply ofmap_proper. eapply thetaUnitLaxness.
    clear thetaUnitLaxness.
    (*R2 func*)
    rewrite ord_functor_law2. rewrite -[( ofmap R2 _ ∙ ofmap R2 _ ) ∙ _]ord_cat_law3.
    (*alpha' * beta' lax unit preservation*)
    move: (laxUnitPres' A). cbv. rewrite !ord_cat_law2. move=> BislaxUnitPres'.
    etransitivity.
    eapply Comp_proper. all: swap 1 2. reflexivity.
    rewrite -ord_cat_law3.
    eapply Comp_proper. reflexivity.
    unshelve eapply ord_cat_le_comp in BislaxUnitPres'.
      shelve. exact (invChi A). exact (invChi A). shelve.
    rewrite -ord_cat_law3 in BislaxUnitPres'.
    rewrite ni_rightinv in BislaxUnitPres'. rewrite ord_cat_law2 in BislaxUnitPres'.
    apply BislaxUnitPres'. clear BislaxUnitPres'.
    reflexivity.
    (*chi and invchi are inverses*)
    rewrite -!ord_cat_law3. cbv. rewrite (ni_leftinv _ _ chi). rewrite ord_cat_law2.
    reflexivity.
  Qed.
  Next Obligation.
     cbv. intuition.
    pose (top_isoPres := lmlad_StrucIsoPres _ _ myKtheta). cbv in top_isoPres.
    specialize (top_isoPres (Lflat A) Y f).
    rewrite top_isoPres. clear top_isoPres.
    cbv in StrucIsoPres'. move: StrucIsoPres'. move=> /(_ A (M1 Y) f) BisStrucIsoPres'.
    rewrite {1}BisStrucIsoPres'. clear BisStrucIsoPres'.
    f_equal. f_equal.
    (*cleaning*)
    do 8 rewrite -ord_cat_law3. clear PPre_smBeta'' PPre_smAlpha''.
    simpl in *.
    rewrite (ni_leftinv _ _ chi). rewrite ord_cat_law2.
    rewrite ord_cat_law1.
    (*Phi2' naturality*)
    unshelve epose (naturality_Phi2' := ni_natural _ _ (natIso_sym Chi_RJLflat_2)).
      exact ⟨A, KC ( M1 Y ) ⟩. exact ⟨ A , M2 Y⟩.
    cbv in naturality_Phi2'.
    specialize (naturality_Phi2' ⟨(Id A) , (theta Y)⟩).
    apply (f_equal sval) in naturality_Phi2'. cbv in naturality_Phi2'.
    unshelve eapply equal_f in naturality_Phi2'.
    unshelve eapply Comp. shelve. exact (smBeta' (M1 Y)).
    simpl. unshelve eapply Comp. shelve.
    eapply (ofmap KC). exact (  (Chi_RJLflat_1 ⟨A, M1 Y⟩)∙1 f ).
    simpl. exact (chi A).
    cbv in naturality_Phi2'.
    (*cleaning in naturality_Phi2'*)
    rewrite !ord_functor_law1 in naturality_Phi2'.
    rewrite !ord_cat_law2 in naturality_Phi2'.
    (*rewriting with naturality_Phi2'*)
    rewrite -naturality_Phi2'.
    f_equal. f_equal. rewrite !ord_cat_law1. reflexivity.
    rewrite ord_relmon_law1. rewrite !ord_cat_law1. reflexivity.
  Qed.


  Definition Transformed_rlmm := rlmm_from_lmla Transformed_lmla.


End TransformedLaxMorphAdj.
