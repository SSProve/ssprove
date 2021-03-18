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
     UniformDistrLemmas.

Import SPropNotations.
Import Num.Theory.

(* Notation "⟦ b ⟧" := (is_true_sprop b). *)
(* Infix "-s>" := (s_impl) (right associativity, at level 86, only parsing). *)

Local Open Scope ring_scope.

Module Type UniformParameters.

  Parameter Index : Type.
  Parameter i0 : Index.
  Parameter fin_family : Index -> finType.
  Parameter F_w0 : forall i, (fin_family i).

End UniformParameters.

(* "standard" Rules + Rules for uniform distributions over a finite
    family of non-empty finite types *)
Module DerivedRulesUniform (myparam :  ProbRulesParam) (myparamUniform : UniformParameters).

  Import myparam.
  Import myparamUniform.

  (* Rem.: we extend the initial parameters for the rules  *)
  Inductive UprobE : Type -> Type :=
  | Uni_W  : forall i, UprobE (fin_family i).

  Definition UchUniverse : Type := Index.

  Definition UchElement : UchUniverse -> choiceType.
  Proof. move => i. exact (fin_family i). Defined.

  Definition Uprob_handler : forall T : choiceType, UprobE T -> SDistr T.
  Proof.
    move => T TF.
    inversion TF.
    rewrite /SDistr /SDistr_carrier.
    eapply mkdistrd.
    rewrite -H0.
    move => F.
    apply: r.
    exact F.
  Defined.

  Module myparamU <: ProbRulesParam.

    Definition probE : Type -> Type := fun T => (UprobE T + probE T):Type.

    Definition chUniverse : Type := UchUniverse + chUniverse.

    Definition chElement : chUniverse -> choiceType.
    Proof.
      move => [t1 | t2].
      + exact (UchElement t1).
      + exact (chElement t2).
    Defined.

    Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
    Proof.
      move => T [HU | HR].
      + exact (Uprob_handler T HU).
      + exact (prob_handler T HR).
    Defined.

    Definition Hch : forall r : chUniverse, chElement r.
    Proof.
      move => r.
      destruct r; rewrite /=.
      - by apply: F_w0.
      - by apply: myparam.Hch.
    Defined.

  End myparamU.

  (*Rem.:  *)
  Module MyRulesU := DerivedRules myparamU.
  Export myparamU.
  Export MyRulesU.


  (* Uniform distribution over F *)
  Definition Uniform_F { i : Index } : MyRulesU.MFreePr (fin_family i).
    rewrite /MyRulesU.MFreePr.
    rewrite /probE /chUniverse.
    apply: (ropr _ _ (fin_family i) (existT (fun rchT : chUniverse => probE (chElement rchT)) (inl _ i) (inl _ (Uni_W i)))).
    rewrite /= => w.
    constructor.
    exact w.
  Defined.

  (* Uniform_F is actually the uniform distribution over F *)
  Lemma Uniform_F_is_uniform_F { i : Index } : get_d (@Uniform_F i) = (@uniform_F (fin_family i) (F_w0 i)).
  Proof.
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

