From Coq Require Import Relation_Definitions Morphisms.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra distr reals realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import ChoiceAsOrd Axioms.

Import Num.Theory.
Import Order.POrderTheory.

Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we define/prove the (relative) monad of subdistributions.
To this end we use mathcomp choiceType structure and mathcomp support for
distributions (file distr.v in mathcomp analysis). The intended monad
SDistr is relative over choice_incl : chTy -> TypeCat.
It is basically defined like so:
SDistr (A:choiceType) := {distr A/R}
The type {distr A/R} consists of the collection of subdensities over the
discrete space A. Concretly it consists of positive functions A -> R which
are summable (ie integrable over any finite part of A) and whose sum is
less than 1.
*)

Definition chDiscr : ord_functor ord_choiceType OrdCat
  := ord_functor_comp (choice_incl) (discr).

Section Extensionality_for_distr.

  Lemma distr_ext : forall (A : choiceType) (mu nu : {distr A/R}),
  distr.mu mu =1 distr.mu nu -> mu = nu. Proof.
    move=> A [mu muz mu_smbl mu_psum] [nu nuz nu_smbl nu_psum].  simpl. intro H.
    move: muz mu_smbl mu_psum nuz nu_smbl nu_psum. apply boolp.funext in H.
    rewrite H. intuition. f_equal. all: apply proof_irrelevance.
  Qed.

End Extensionality_for_distr.

Section Carrier.

  (*the actual carrier, on poset enriched categories (ord_category
  in the dev) *)

  Program Definition SDistr_carrier (A : ord_choiceType) : TypeCat
    := {distr A / R}.

End Carrier.



Section Unit.

  Definition SDistr_unit (A : ord_choiceType) :
    TypeCat ⦅ choice_incl A ; SDistr_carrier A ⦆
    := fun a => dunit a.

End Unit.

Section Bind.

  Definition SDistr_bind (A B : ord_choiceType) :
    TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆ ->
    TypeCat ⦅ SDistr_carrier A; SDistr_carrier B ⦆
    := fun f m => dlet f m.

End Bind.


Section Relmon_equations.

  Lemma SDistr_rightneutral (A : ord_choiceType) :
    SDistr_bind A A (SDistr_unit A) = Id (SDistr_carrier A).
  Proof. apply boolp.funext => de. apply distr_ext, dlet_dunit_id. Qed.

  Lemma SDistr_leftneutral (A B : ord_choiceType)
    (f : TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆) :
    SDistr_bind A B f ∙ SDistr_unit A = f.
  Proof. apply boolp.funext => de; apply distr_ext, dlet_unit. Qed.

  Lemma SDistr_assoc (A B C : ord_choiceType)
    (f : TypeCat ⦅ choice_incl B; SDistr_carrier C ⦆)
    (g : TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆) :
    SDistr_bind A C (SDistr_bind B C f ∙ g)
      = SDistr_bind B C f ∙ SDistr_bind A B g.
  Proof. apply boolp.funext => de. symmetry. apply distr_ext, dlet_dlet. Qed.

End Relmon_equations.


Section Ordrelmon_instance.
  (*Here we pack all the above constructs in a ord_relativeMonad instance*)

   Program Definition SDistr : ord_relativeMonad choice_incl :=
     mkOrdRelativeMonad SDistr_carrier SDistr_unit SDistr_bind _ _ _ _.
   Next Obligation.
     intros A B f1 f2 H a. apply boolp.funext in H. by subst.
   Qed.
   Next Obligation. exact SDistr_rightneutral. Qed.
   Next Obligation. exact SDistr_leftneutral. Qed.
   Next Obligation. exact SDistr_assoc. Qed.

End Ordrelmon_instance.


(*Finaly we can build the square of this unary relative monad to get a
type former for pairs of probabilistic programs, seen as subdensities.
*)
Definition SDistr_squ := product_rmon
  (SDistr) (SDistr).
