From Coq Require Import RelationClasses Morphisms.

From Mon Require Import
     FiniteProbabilities
     SPropMonadicStructures
     SpecificationMonads
     MonadExamples
     SPropBase.

From Relational Require Import
     OrderEnrichedCategory
     OrderEnrichedRelativeMonadExamples
     Commutativity
     GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     Theta_dens
     Theta_exCP
     LaxComp
     FreeProbProg
     RulesProb
     UniformDistrLemmas
     choice_code
     Prelude.

Import SPropNotations.
Import Num.Theory.


Local Open Scope ring_scope.


(* "standard" Rules + Rules for uniform distributions over a finite
    family of non-empty finite types *)
Module DerivedRulesUniform.

  Definition inhab (i : positive) : chFin i.
  destruct i as [i ipos]. destruct i.
  - cbv in ipos. discriminate.
  - cbn. unshelve econstructor.
    exact i. auto.
  Defined.

  #[local] Definition Index := positive.
  #[local] Definition i0 := mkpos 1.
  #[local] Definition fin_family : Index -> finType := fun i =>
     [finType of ordinal i.(pos) ].
  #[local] Definition F_w0 : forall i, (fin_family i).
    move=> i. apply inhab. Defined.


  Module MyRulesU := DerivedRules.
  Export MyRulesU.

  (* Uniform distribution over F *)
  Definition Uniform_F { i : Index } : MyRulesU.MFreePr (fin_family i).
    rewrite /MyRulesU.MFreePr /rFreePr.
    unshelve eapply ropr. unshelve econstructor.
      exact (chFin i). cbn. eapply @uniform_F. eapply F_w0.
    cbn. move=> i'. eapply retrFree. eapply F_w0.
  Defined.

  (* Uniform_F is actually the uniform distribution over F *)
  Lemma Uniform_F_is_uniform_F { i : Index } : get_d (@Uniform_F i) = (@uniform_F (fin_family i) (F_w0 i)).
  Proof.
    cbn.
    (* epose (hlp := ord_relmon_law1 SDistr). *)
    (* eapply equal_f in hlp. cbn in hlp. *)
    (* unfold SubDistr.SDistr_obligation_1 in hlp. *)
    (* unfold SubDistr.SDistr_obligation_2 in hlp. *)
    (* erewrite hlp. *)
    apply: distr_ext.
    cbn.
    rewrite /SDistr_bind /Uniform_F /SDistr_unit => w.

    rewrite (@dlet_dunit_id _ _ (mkdistrd (fun=> r)) w) /mkdistrd.
    destruct idP.
    + by [].
    + exfalso. apply n.
      rewrite /boolp.asbool //=.
      case (boolp.pselect (isdistr (fun=> r))); intuition.
      exfalso. apply n0. apply: (@is_uniform (fin_family i) (F_w0 i)).
  Qed.

  Import RulesNotation.

  Theorem Uniform_bij_rule { i : Index }
                           { f : fin_family i -> fin_family i }
                           (f_bij : bijective f)
                           (P : Prop):
    ⊨ ⦃ P ⦄ (@Uniform_F i) ≈ (@Uniform_F i) ⦃ fun w1 w2 => (f w1) == w2 ⦄.
  Proof.
   eapply (MyRulesU.sample_rule_ch).
   rewrite Uniform_F_is_uniform_F.
   apply: (sampleFsq_f_coupling f_bij).
   by move => a1 a2; apply: sampleFsq_support.
  Qed.


End DerivedRulesUniform.

