From SSProve.Relational Require Import OrderEnrichedCategory.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".

Global Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.


(*
In this file we build products of relative monad morphisms.

First we build products of natural isomorphisms: let F1,G1 : C1 → D1 and Ψ1 a
natural iso between F1 and G1. Similarly let F2,G2 : C2 → D2 and Ψ2 a natural
iso between F2 and G2.
Then we can build F1×F2, G1×G2 : C1×C2→D1×D2 and a natural iso Ψ1×Ψ2 between
the product functors F1×F2 and G1×G2.

Second, two relative monad morphisms θ1 : M1 → W1 and θ2 : M2 → W2 can
be multiplied together to get θ1 × θ2 : M1×M2 → W1×W2 (section Rel_mon_morph_prod).
*)


Section NatIso_prod.
  (*globes*)

  Context {C1 D1 : ord_category} {F1 G1 : ord_functor C1 D1}
          (psi1  : natIso F1 G1).
  Context {C2 D2 : ord_category} {F2 G2 : ord_functor C2 D2}
          (psi2  : natIso F2 G2).


  Local Definition Cprod := prod_cat C1 C2.
  Local Definition Dprod := prod_cat D1 D2.
  Local Definition Fprod := prod_functor F1 F2.
  Local Definition Gprod := prod_functor G1 G2.

  Program Definition prod_natIso : natIso Fprod Gprod := mkNatIso _ _ _ _ _ _ _.
  Next Obligation. (*the map*)
    move=> [A1 A2]. unshelve econstructor. all:simpl.
    apply psi1. apply psi2.
  Defined.
  Next Obligation. (*the inverse map*)
    move=> [A1 A2]. split. all:simpl.
    apply (ni_inv psi1). apply (ni_inv psi2).
  Defined.
  Next Obligation. (*naturality*)
    move=> [A1 A2 [B1 B2]]. all:simpl. move=> [f1 f2]. all:simpl.
    f_equal. eapply (ni_natural _ _ psi1). eapply (ni_natural _ _ psi2).
  Qed.
  Next Obligation. (*proof that it is inverse*)
    move=> [A1 A2]. simpl. f_equal.
    eapply (ni_rightinv _ _ psi1). eapply (ni_rightinv _ _ psi2).
  Qed.
  Next Obligation. (*proof that it is inverse*)
    move=> [A1 A2]. simpl. f_equal.
    eapply (ni_leftinv _ _ psi1). eapply (ni_leftinv _ _ psi2).
  Qed.


End NatIso_prod.

Section Rel_mon_morph_prod.
  (*The first square. it is indexed with _1*)

  Context {I1 CM1 CW1: ord_category}
          {JM1 : ord_functor I1 CM1} {JW1 : ord_functor I1 CW1}
          {JMW1 : ord_functor CM1 CW1}
          {M1 : ord_relativeMonad JM1} {W1 : ord_relativeMonad JW1}
          {cmtSqu1 : natIso JW1 (ord_functor_comp JM1 JMW1)}.
  (*the second square.*)
  Context {I2 CM2 CW2: ord_category}
          {JM2 : ord_functor I2 CM2} {JW2 : ord_functor I2 CW2}
          {JMW2 : ord_functor CM2 CW2}
          {M2 : ord_relativeMonad JM2} {W2 : ord_relativeMonad JW2}
          {cmtSqu2 : natIso JW2 (ord_functor_comp JM2 JMW2)}.

  Local Definition Iprod := prod_cat I1 I2.
  Local Definition CMprod := prod_cat CM1 CM2.
  Local Definition CWprod := prod_cat CW1 CW2.

  Local Definition JMprod := prod_functor JM1 JM2.
  Local Definition JWprod := prod_functor JW1 JW2.
  Local Definition JMWprod := prod_functor JMW1 JMW2.

  Local Definition Mprod := product_rmon M1 M2.
  Local Definition Wprod := product_rmon W1 W2.

  Local Definition cmtSqu_prod := prod_natIso cmtSqu1 cmtSqu2.

  Context (theta1 : relativeMonadMorphism JMW1 cmtSqu1 M1 W1)
          (theta2 : relativeMonadMorphism JMW2 cmtSqu2 M2 W2).

  Local Program Definition cmtSqu
  :natIso (prod_functor JW1 JW2) (ord_functor_comp (prod_functor JM1 JM2) JMWprod)
  := mkNatIso _ _ (prod_natIso cmtSqu1 cmtSqu2) _ _ _ _.
  Next Obligation.
    apply (ni_inv (prod_natIso cmtSqu1 cmtSqu2)).
  Defined.
  Next Obligation.
    eapply (@ni_natural Iprod CWprod JWprod _ (prod_natIso cmtSqu1 cmtSqu2)).
  Qed.
  Next Obligation.
    eapply (@ni_rightinv Iprod CWprod JWprod _ (prod_natIso cmtSqu1 cmtSqu2)).
  Qed.
  Next Obligation.
    eapply (@ni_leftinv Iprod CWprod JWprod _ (prod_natIso cmtSqu1 cmtSqu2)).
  Qed.

  Program Definition prod_relativeMonadMorphism
  : relativeMonadMorphism JMWprod cmtSqu Mprod Wprod :=
    mkRelMonMorph JMWprod cmtSqu Mprod Wprod _ _ _.
  Next Obligation.
    split. apply theta1. apply theta2.
  Defined.
  Next Obligation. (*law 1*)
  move=> [A1 A2]. simpl. f_equal.
  eapply (rmm_law1 _ _ _ _ theta1). eapply (rmm_law1 _ _ _ _ theta2).
  Qed.
  Next Obligation.
  move=> [A1 A2 [B1 B2]]. move=> [f1 f2]. simpl. f_equal.
  eapply (rmm_law2 _ _ _ _ theta1). eapply (rmm_law2 _ _ _ _ theta2).
  Qed.

End Rel_mon_morph_prod.
