From Mon Require Import SpecificationMonads SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd SubDistr Theta_exCP Axioms Couplings.
From mathcomp Require Import all_ssreflect distr all_algebra reals.

Import SPropNotations.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(*
In this file we define a relational effect observation
SD² → BP  (where BP is the relational specification monad
of backward predicate transformer, ie
  BP( A0 , A1 ) := (A0 × A1 → Prop) → Prop

The defined semantics should be more permissive than
the one defined in ThetaDex.v in the sense that
null subdistributions will always be related to anything else
*)

Section Monotonic_spec.

  Context {A0 A1 : ord_choiceType}.
  Context ( w : Base.dfst (WRelProp ⟨ A0 , A1 ⟩) ).

  Goal True.
    cbn in w.
    unfold SPropMonadicStructures.SProp_op_order in w.
    unfold Basics.flip in w.
    unfold SPropMonadicStructures.SProp_order in w.
  Abort.

  Lemma monotonic_spec : forall (post post' : A0 * A1 -> Prop),
  (forall a01 : A0 * A1, post' a01 -> post a01) ->
  w∙1 post' -> w∙1 post.
  Proof.
    move=> post post'. move=> Hpost.
    destruct w as [wmap wprop]. cbn.
    move: wprop.
    rewrite /Morphisms.Proper /Morphisms.respectful.
    rewrite /Morphisms.pointwise_relation.
    rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip.
    rewrite /SPropMonadicStructures.SProp_order.
    move=> wprop.
    apply wprop. assumption.
  Qed.

End Monotonic_spec.

Section Clean_base_morphism.

(*
About ϕ θ_morph
ϕ uses the v functions of Theta_exCP.v which destruct choiceTypes.
we redefine phi here so that it has a better behaviour
*)

Program Definition cleanϕ : natIso
    (ord_functor_comp F_choice_prod chDiscr)
    (ord_functor_comp (prod_functor choice_incl choice_incl) Jprod) :=
  mkNatIso _ _ _ _ _ _ _.
  Next Obligation.
    move=> [A0 A1] ; cbn. unshelve econstructor.
    move=> [a0 a1]. exact ⟨a0 , a1⟩.
    cbn. rewrite /Morphisms.Proper /Morphisms.respectful.
    move=> [a0 a1] [a0' a1']. move=> [H0 H1].
    rewrite H0 H1. reflexivity.
  Defined.
  Next Obligation.
    move=> [A0 A1]. cbn. unshelve econstructor.
    move=> [a0 a1]. exact (a0 , a1). cbn.
    move=> [a0 a1] [a0' a1']. move=> [H0 H1].
    rewrite H0 H1. reflexivity.
  Defined.
  Next Obligation.
    move=> [A0 A1] [B0 B1] /= [f0 f1].
    apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A0 A1]. apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A0 A1]. apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.


End Clean_base_morphism.


Section NonNullDistr.

  Context {A : choiceType}.


  Definition nonZer (d : SDistr A) : Prop :=
    exists (a:A), d a != 0.

  Lemma nonZer_dnull : forall d, nonZer d -> d <> dnull.
  Proof.
    move=> d Hd. move=> Heq. move: Hd. rewrite /nonZer.
    move=> [a0 prf]. move: prf => /eqP. move=> prf. apply prf.
    rewrite Heq. rewrite dnullE. reflexivity.
  Qed.

  Lemma dnull_nonZer : forall d, d <> dnull -> nonZer d.
  Proof.
    move=> d. move=> Hneq.
  Abort.

End NonNullDistr.


Section Permissive_theta.

  Ltac my_unfolding :=
    rewrite /Morphisms.Proper /Morphisms.respectful ;
    rewrite /MonoCont_order /Morphisms.pointwise_relation ;
    rewrite /SPropMonadicStructures.SProp_op_order ;
    rewrite /Basics.flip ;
    rewrite /SPropMonadicStructures.SProp_order.

  Lemma some_mathcomp_lemma (b : bool) :
    0 < @GRing.natmul (GRing.Ring.zmodType R) (GRing.one R) (nat_of_bool b) -> b.
  Proof.
    move: b => [bt | bf].
      by easy.
    cbn in bf.
    rewrite Order.POrderTheory.ltxx in bf. assumption.
  Qed.

  Program Definition θ_perm_carrier :
  forall (A0 A1 : choiceType),
  {f
  : SDistr_carrier A0 × SDistr_carrier A1 ->
    MonoContCarrier SPropMonadicStructures.SProp_op_order (A0 * A1)
  | Morphisms.Proper
      (Morphisms.respectful eq
         (MonoCont_order (Rrel:=SPropMonadicStructures.SProp_op_order) (A:=A0 * A1))) f} :=
    fun A0 A1 => exist _ _ _.
  Next Obligation.
    move=> A0 A1. move=> [c0 c1].
    rewrite /MonoContCarrier. unshelve econstructor.
    move=> post.
    exact (
      nonZer c0 /\ nonZer c1 ->
      exists d, (coupling d c0 c1)  /\
      (forall (a0 : A0) (a1 : A1), (d (a0, a1)) > 0 -> post (a0, a1)) ).
    {
      my_unfolding.
      move=> post post'. move=> Hpost.
      move=> Hcoupl.
      move=> Hnzer. apply Hcoupl in Hnzer.
      destruct Hnzer as [d [dcoupl dprop]].
      unshelve econstructor. exact d. split.
      - exact dcoupl.
      - move=> a0 a1 Hd. apply Hpost. apply dprop. assumption. }
  Defined.
  Next Obligation.
    move=> A0 A1.
    my_unfolding.
    move=> [c0 c1] [c0' c1']. move=> [H0 H1]. move=> post.
    rewrite H0 H1. move=> H ; assumption.
  Qed.



  Program Definition θ_perm: relativeLaxMonadMorphism Jprod cleanϕ SDistr_squ WRelProp :=
    mkRelLaxMonMorph _ _ _ _ _ _ _.
  Next Obligation.
    move=> [A0 A1]. cbn.
    exact (θ_perm_carrier A0 A1).
  Defined.
  Next Obligation.
    move=> [A0 A1] ; cbn. move=> [a0 a1].
    my_unfolding.
    move=> post. cbn. move=> Hpost.
    rewrite /SubDistr.SDistr_obligation_1. move=> _.
    unshelve econstructor.
      exact ( SDistr_unit (F_choice_prod (npair A0 A1)) (a0,a1) ).
    split.
    apply SDistr_unit_F_choice_prod_coupling. reflexivity.
    move=> a0' a1'. rewrite /SDistr_unit. rewrite dunit1E.
    move=> Bnonzer. apply some_mathcomp_lemma in Bnonzer.
    move: Bnonzer  => /eqP [H0 H1]. rewrite -H0 -H1.
    move: Hpost. by easy.
  Qed.
  Next Obligation.
    move=> [A0 A1] [B0 B1] ; cbn. move=> [f0 f1] [c0 c1].
    rewrite /MonoCont_order. my_unfolding.
    move=> post. rewrite /MonoCont_bind ; cbn.
    move=> H.
    rewrite /SubDistr.SDistr_obligation_2.
    move=> [HnonzerBind0 HnonzerBind1].
    assert (HnonzerC01 : nonZer c0 /\ nonZer c1).
    { admit. }
    apply H in HnonzerC01.
    rename HnonzerC01 into Hecoupl.
    move: Hecoupl => [dc [dc_coupl dc_rest]].
  Abort.

