From mathcomp Require Import all_ssreflect.
From Crypt Require Import OrderEnrichedRelativeAdjunctions OrderEnrichedRelativeAdjunctionsExamples
OrderEnrichedNatTrans ChoiceAsOrd.
From Relational Require Import OrderEnrichedCategory.
From Mon Require Import SPropBase.

Import SPropNotations.

Section Bla.
  (*The source relative monad, from which leaves the transformed lax morphism*)
  Context (I C1 : ord_category).
  Context (Lflat : ord_functor I I) (R1 : ord_functor C1 C1).
  Context (J1 : ord_functor I C1) (M1 : ord_relativeMonad J1).
  Context (Chi_DomainAdj :  leftAdjunctionSituation J1 (ord_functor_comp Lflat J1) R1).

  Let source_relativeMonad :=  AdjTransform M1 Lflat R1 Chi_DomainAdj.

  (*The target relative monad, in which lands the transformed lax morphism*)
  Context (C2 : ord_category).
  Context (R2 : ord_functor C2 C2).
  Context (J2 : ord_functor I C2) (M2 : ord_relativeMonad J2).
  Context (Chi_CodomainAdj :  leftAdjunctionSituation J2 (ord_functor_comp Lflat J2) R2).

  Let target_relativeMonad :=  AdjTransform M2 Lflat R2 Chi_CodomainAdj.

  (*auxilliary cells for the untransformed lax morphism*)

  Context (FC : ord_functor C1 C2).
  Context (theta_baseSqu : natIso J2 (ord_functor_comp J1 FC)).

  (* untransformed lax morphism *)

  Context (theta_lax :  relativeLaxMonadMorphism FC theta_baseSqu M1 M2).

  (*auxilliary 2 cell for the transformed morphism*)

  Context (FCell : natTrans (ord_functor_comp R1 FC) (ord_functor_comp FC R2) ).


  (*Definition of the first part of the transformed morphism*)

  Let domain_functor := (ord_functor_comp Lflat (ord_functor_comp
    (rmon_to_ord_functor M1) (ord_functor_comp R1 FC))).

  Let intermediate_functor := (ord_functor_comp Lflat (ord_functor_comp
    (rmon_to_ord_functor M1) (ord_functor_comp FC R2))).

  Definition Ttheta_part1 : natTrans domain_functor intermediate_functor.
    unshelve eapply natTrans_whisker_left.
    unshelve eapply natTrans_whisker_left.
    exact FCell.
  Defined.

  (*Definition of the whole transformed morphism*)

  Definition Ttheta0 :  forall A : I, C2 ⦅ FC (source_relativeMonad A); target_relativeMonad A ⦆.
    move=> i. simpl. unshelve eapply Comp. exact (R2 (FC (M1 (Lflat i)))).
    eapply (ofmap R2). eapply theta_lax.
    eapply Ttheta_part1.
  Defined.

  Program Definition Ttheta : relativeLaxMonadMorphism
                FC theta_baseSqu source_relativeMonad target_relativeMonad :=
    mkRelLaxMonMorph FC theta_baseSqu source_relativeMonad target_relativeMonad Ttheta0 _ _.
  Next Obligation.
    move=> i.
    move: theta_lax => [theta_lax_map theta_lax_law1 theta_lax_law2].
    move: theta_lax_law1 => /(_ (Lflat i)) theta_law_law1_i.
    cbv.





