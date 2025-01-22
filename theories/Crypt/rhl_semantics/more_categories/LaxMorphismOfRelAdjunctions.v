From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Mon Require Import SPropBase.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect classical.boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms OrderEnrichedRelativeAdjunctions LaxFunctorsAndTransf.

Import SPropNotations.
(*
In this file we define the notion of lax morphism between left relative adjunctions.
We use it to transform relative monad morphisms based on "transforming adjunctions"
in the file TransformingLaxMorph.v.

We first pack left adjunctions into a single record type
*)
Section leftAdjunctions.
  (*J:I → C, L:I → D, R:D → C, L ⊣ R above J*)
  Record leftAdjunction (lad_I : ord_category) := mkLeftAdjunction {
    lad_D : ord_category ; lad_C : ord_category ;
    lad_J : ord_functor lad_I lad_C ;
    lad_L : ord_functor lad_I lad_D ;
    lad_R : ord_functor lad_D lad_C ;
    lad_strucIso : leftAdjunctionSituation lad_J lad_L lad_R
    }.
End leftAdjunctions.

Arguments lad_D {_}. Arguments lad_C {_}.
Arguments lad_J {_}.
Arguments lad_L {_}.
Arguments lad_R {_}.
Arguments lad_strucIso {_}.


Section LaxMorphismLeftRelativeAdjunctions.
  Context {I : ord_category}.
  Context (adj1 : leftAdjunction I)
          (adj2 : leftAdjunction I).

  Let D1 := lad_D adj1. Let C1 := lad_C adj1.
  Let J1 := lad_J adj1. Let L1 := lad_L adj1. Let R1 := lad_R adj1.
  Let phi1 := lad_strucIso adj1.
  Let M1 := relMon_fromLeftAdj J1 L1 R1 phi1.

  Let D2 := lad_D adj2. Let C2 := lad_C adj2.
  Let J2 := lad_J adj2. Let L2 := lad_L adj2. Let R2 := lad_R adj2.
  Let phi2 := lad_strucIso adj2.
  Let M2 := relMon_fromLeftAdj J2 L2 R2 phi2.


  Notation η := ord_relmon_unit.

  Record LaxMorphLeftAdj := mkLaxMorphLeftAdj {
    lmlad_KD : lord_functor D1 D2 ;
    lmlad_KC : ord_functor C1 C2 ;
    lmlad_baseIso : natIso J2 (ord_functor_comp J1 lmlad_KC) ;
    lmlad_alpha : lnatTrans
                    (lord_functor_comp (strict2laxFunc L1) lmlad_KD)
                    (lord_functor_comp (strict2laxFunc (ord_functor_id _)) (strict2laxFunc L2)) ;
    lmlad_beta : lnatTrans
                   (lord_functor_comp (strict2laxFunc R1) (strict2laxFunc lmlad_KC))
                   (lord_functor_comp lmlad_KD (strict2laxFunc R2)) ;
    lmlad_laxRetPres :
      forall {A},   (paste lmlad_alpha lmlad_beta) A ∙
               (lofmap (strict2laxFunc lmlad_KC) (η M1 A)) ∙
               lmlad_baseIso A
         ⪷ (η M2  A) ;
    lmlad_StrucIsoPres : forall A Y (f : D1⦅L1 A ; Y⦆),
      lofmap lmlad_KD f =
      ((natIso_sym phi2)⟨A,lmlad_KD Y⟩)∙1 (lmlad_beta Y ∙ ofmap lmlad_KC ( (phi1 ⟨A,Y⟩) ∙1 f  ) ∙ lmlad_baseIso A) ∙ lmlad_alpha A }.

End LaxMorphismLeftRelativeAdjunctions.


