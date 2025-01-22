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

For efficiency reasons we seal the use of fun x y : R => x ≤ y using two axioms.
The first one absord : R -> R -> bool
The second one unlock_absord : absord = (fun x y : R => x ≤ y)
They are in the file Crypt/Axioms.v
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

  Definition SDistr_carrier0 (A:choiceType) := {distr A/R}.

  Definition SDistr_carrier0_preorder A : relation (SDistr_carrier0 A) :=
  fun de1 de2 =>
  pointwise_relation A (fun x y =>  absord x y) de1 de2.

  (* This hangs: Eval cbv in Sdistr_carrier0_preorder. *)
  (* This does not hang: Eval vm_compute in SDistr_carrier0_preorder.*)

  Instance SDistr_carrier0_preorder_preorder A
  : PreOrder (@SDistr_carrier0_preorder A).
  Proof.
    constructor.
      vm_compute. intros de a. rewrite unlock_absord.
      apply lexx.
    vm_compute. intros de1 de2 de3 H12 H23 a.
    (* apply its_true_anyway. *) rewrite unlock_absord.
    unshelve eapply le_trans.
      exact (de2 a).
    - pose (fromH12 := (H12 a)). (* apply since_its_true  in fromH12. *)
      erewrite unlock_absord in fromH12. assumption.
    - pose (fromH23 := (H23 a)).
      erewrite unlock_absord in fromH23. assumption.
  Qed.

  (*the actual carrier, on poset enriched categories (ord_category
  in the dev) *)

  Program Definition SDistr_carrier (A: ord_choiceType) : TypeCat.
    exact ({distr A/R}).
  Defined.

End Carrier.



Section Unit.

  Definition SDistr_unit : forall (A:ord_choiceType),
  TypeCat ⦅ choice_incl A ; SDistr_carrier A ⦆.
    intro A. intro a. exact (@dunit R A a).
  Defined.

End Unit.

Section Bind.

  Definition SDistr_bind : forall A B : ord_choiceType,
  TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆ ->
  TypeCat ⦅ SDistr_carrier A; SDistr_carrier B ⦆.
    intros A B. intro ff. simpl in ff.
    intro mm.
    exact (@dlet R A B ff mm). (*dlet is the bind operator defined in mathcomp*)
  Defined.

End Bind.


Section Relmon_equations.

  Lemma SDistr_rightneutral :
  forall A : ord_choiceType, SDistr_bind A A (SDistr_unit A) = Id (SDistr_carrier A).
  Proof.
    intro A. simpl. eapply boolp.funext. unfold "=1". intro de.
    apply distr_ext. apply dlet_dunit_id.
  Qed.

  Lemma SDistr_leftneutral :
  forall (A B : ord_choiceType) (f : TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆),
  SDistr_bind A B f ∙ SDistr_unit A = f.
    intros A B ff. simpl. simpl in ff.
    apply boolp.funext. intro de. apply distr_ext.
    apply dlet_unit.
  Qed.

  Lemma SDistr_assoc :
  forall (A B C : ord_choiceType) (f : TypeCat ⦅ choice_incl B; SDistr_carrier C ⦆)
    (g : TypeCat ⦅ choice_incl A; SDistr_carrier B ⦆),
  SDistr_bind A C (SDistr_bind B C f ∙ g) = SDistr_bind B C f ∙ SDistr_bind A B g.
    intros A B C f g.
    simpl in f. simpl in g. simpl.
    apply boolp.funext. intro de. symmetry.
    apply distr_ext. intro c. simpl. apply dlet_dlet.
  Qed.

End Relmon_equations.


Section Ordrelmon_instance.
  (*Here we pack all the above constructs in a ord_relativeMonad instance*)

   Program Definition SDistr : ord_relativeMonad choice_incl :=
   mkOrdRelativeMonad SDistr_carrier  _  _ _ _ _ _.
   Next Obligation. exact (SDistr_unit). Defined.
   Next Obligation. exact (SDistr_bind). Defined.
   Next Obligation.
     intros A B. intros f1 f2. intro H. intro a.
     assert (f1 = f2). apply boolp.funext. assumption.
     destruct H0. reflexivity.
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
