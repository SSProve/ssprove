From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase SRelationClasses SMorphisms FiniteProbabilities.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
From Crypt Require Import ChoiceAsOrd Axioms.


Import SPropNotations.
Import Num.Theory.

Notation "⟦ b ⟧" := (is_true_sprop b).
Infix "-s>" := (s_impl) (right associativity, at level 86, only parsing).

Local Open Scope ring_scope.

(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we define/prove the (relative) monad of subdistributions.
To this end we use mathcomp choiceType structure and mathcomp support for
distributions (file distr.v in mathcomp analysis). The intended monad
SDistr is relative over chDiscr : chTy -> Poset (Poset is OrdCat in the dev).
It is basically defined like so:
SDistr (A:choiceType) := {distr A/R}
The type {distr A/R} consists of the collection of subdensities over the
discrete space A. Concretly it consists of positive functions A -> R which
are summable (ie integrable over any finite part of A) and whose sum is
less than 1.

For efficiency reasons we seal the use of fun x y : R => x ≤ y using two axioms.
The first one absord : R -> R -> bool
The second one unlock_absord : absord = (fun x y : R => x ≤ y)
Theyre in the file Crypt/Axioms.v
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

  Definition SDistr_carrier0_preorder A : srelation (SDistr_carrier0 A) :=
  fun de1 de2 =>
  pointwise_srelation A (fun x y =>  ⟦absord x y⟧) de1 de2.

  (* This hangs: Eval cbv in Sdistr_carrier0_preorder. *)
  Eval vm_compute in SDistr_carrier0_preorder.

  Instance SDistr_carrier0_preorder_preorder A
  : PreOrder (@SDistr_carrier0_preorder A).
  Proof.
    constructor.
      vm_compute. intros de a. apply its_true_anyway. rewrite unlock_absord.
      apply lerr.
    vm_compute. intros de1 de2 de3 H12 H23 a.
    apply its_true_anyway. rewrite unlock_absord. unshelve eapply ler_trans.
      exact (de2 a).
    - pose (fromH12 := (H12 a)). apply since_its_true in fromH12.
      rewrite unlock_absord in fromH12. assumption.
    - pose (fromH23 := (H23 a)). apply since_its_true in fromH23.
      rewrite unlock_absord in fromH23. assumption.
  Qed.

  (*the actual carrier, on poset enriched categories (ord_category
  in the dev) *)

  Program Definition SDistr_carrier (A: ord_choiceType) : OrdCat.
    unshelve econstructor. exact (SDistr_carrier0 A).
    unshelve econstructor. exact (SDistr_carrier0_preorder A).
    exact (SDistr_carrier0_preorder_preorder A).
  Defined.

End Carrier.



Section Unit.

  Definition SDistr_unit : forall (A:ord_choiceType),
  OrdCat ⦅ chDiscr A ; SDistr_carrier A ⦆.
    intro A. unshelve econstructor.
    (*carrier of the unit*)
    cbv. intro a. exact (@dunit R A a).
    (*monotonicity of unit. trivial because A is discrete*)
    intros a1 a2 H12. destruct H12. (*in fact a1 ≡ a2 *)
    unfold SDistr_carrier. destruct SDistr_carrier0_preorder_preorder.
    unshelve eapply PreOrder_Reflexive.
  Defined.

End Unit.

Section Bind.

  Definition SDistr_bind : forall A B : ord_choiceType,
  OrdCat ⦅ chDiscr A; SDistr_carrier B ⦆ ->
  OrdCat ⦅ SDistr_carrier A; SDistr_carrier B ⦆.
    intros A B. intro ff. destruct ff as [ff _]. simpl in ff.
    unshelve econstructor. simpl. intro mm.
    (*bind carrier*)
    exact (@dlet R A B ff mm). (*dlet is the bind operator defined in mathcomp*)
    (*the kleisli lifting must preserve the enrichment (bind ff is monotonic)*)
    intros de1 de2 H b. simpl in de1 ; simpl in de2.  apply its_true_anyway.
    unfold dlet. unlock. simpl. rewrite unlock_absord. eapply le_psum.
    (*first condition for applying le_psum*)
    intro a.
    destruct de1 as [de1 zde1 de1_smbl de1_psum]. simpl.
    destruct (ff a) as [deff zdeff deff_smbl deff_psum]. simpl.
      apply /andP ; split.
      - apply mulr_ge0. apply (zde1 a). apply (zdeff b).
      - unshelve eapply ler_pmul. apply (zde1 a). apply (zdeff b).
      - apply since_its_true. unfold "≤" in H. simpl in H. unfold SDistr_carrier0_preorder in H.
        simpl in H. rewrite unlock_absord in H. apply (H a).
      - apply lerr.
    (*second hypothesis of le_psum.*)
    eapply summable_mlet.
  Defined.

  (*The following can be (1) better written (2) simplified using mathcomp lemmas*)
  Lemma SDistr_bind_compat_orderEnr :
  forall A B : ord_choiceType,
  SProper (ord_cat_le OrdCat s==> ord_cat_le OrdCat) (SDistr_bind A B).
      (*compatibility of bind with the order enrichment *)
    intros A B kl1 kl2 H3 de b. simpl. apply its_true_anyway. unfold dlet. unlock. simpl.
    rewrite unlock_absord. eapply le_psum.
      (*first hyp of le_psum*)
      intro a. apply/andP ; split.
      - apply mulr_ge0. simpl in de. destruct de as [de dez de_smbl de_psum]. simpl.
        apply (dez a).
        destruct kl1 as [kl1 kl1mon]. simpl in kl1. destruct (kl1 a) as [kl1a kl1az kl1a_smbl kl1a_psum].
        simpl. apply (kl1az b).
      (*other part of the split*)
      - apply ler_pmul. destruct de as [de dez de_smbl de_psum]. simpl. apply (dez a).
        destruct kl1 as [kl1 kl1mon]. simpl in kl1. destruct (kl1 a) as [kl1a kl1az kl1a_smbl kl1a_psum].
        simpl. apply (kl1az b).
        apply lerr. simpl in H3. pose (H3a := H3 a). Set Printing All. unfold extract_ord in H3a.
        simpl in H3a. Unset Printing All. unfold SDistr_carrier0_preorder in H3a. pose (H3ab := H3a b).
        simpl in H3ab. apply since_its_true in H3ab. rewrite unlock_absord in H3ab. assumption.
      (*second hyp of le_psum*) eapply summable_mlet.
  Qed.

End Bind.


Section Relmon_equations.

  (*the following exists in mathcomp under the name of dlet_dunit_id*)
  Lemma SDistr_rightneutral :
  forall A : ord_choiceType, SDistr_bind A A (SDistr_unit A) = Id (SDistr_carrier A).
    intro A. simpl. apply Ssig_eq. simpl. eapply boolp.funext. unfold "=1". intro de.
    apply distr_ext. apply dlet_dunit_id.
 Qed.

  Lemma SDistr_leftneutral :
  forall (A B : ord_choiceType) (f : OrdCat ⦅ chDiscr A; SDistr_carrier B ⦆),
  SDistr_bind A B f ∙ SDistr_unit A = f.
    intros A B ff. destruct ff as [ff ffmon]. simpl. simpl in ff.
    apply Ssig_eq. simpl. apply boolp.funext. intro de. apply distr_ext.
    apply dlet_unit.
  Qed.

  Lemma SDistr_assoc :
  forall (A B C : ord_choiceType) (f : OrdCat ⦅ chDiscr B; SDistr_carrier C ⦆)
    (g : OrdCat ⦅ chDiscr A; SDistr_carrier B ⦆),
  SDistr_bind A C (SDistr_bind B C f ∙ g) = SDistr_bind B C f ∙ SDistr_bind A B g.
    intros A B C f g.
    destruct f as [f fmon]. simpl in f.
    destruct g as [g gmon]. simpl in g.
    simpl. apply Ssig_eq. simpl. apply boolp.funext. intro de. symmetry.
    apply distr_ext. intro c. simpl. apply dlet_dlet.
  Qed.

End Relmon_equations.


Section Ordrelmon_instance.
  (*Here we pack all the above constructs in a ord_relativeMonad instance*)
  (*careful with Defined vs Qed*)

   Program Definition SDistr : ord_relativeMonad chDiscr :=
   mkOrdRelativeMonad SDistr_carrier  _  _ _ _ _ _.
   Next Obligation. exact (SDistr_unit). Defined.
   Next Obligation. exact (SDistr_bind). Defined.
   Next Obligation. exact (SDistr_bind_compat_orderEnr). Qed.
   Next Obligation. exact SDistr_rightneutral. Qed.
   Next Obligation. exact SDistr_leftneutral. Qed.
   Next Obligation. exact SDistr_assoc. Qed.

End Ordrelmon_instance.


(*Finaly we can build the square of this unary relative monad to get a
type former for pairs of probabilistic programs, seen as subdensities.
This relational computational monad shall be mapped to a continuation-like
relational specification monad  via a lax relational effect observation.
(the latter is defined with an infimum on the collection of couplings
for a given pair of subdistributions. Morally 1 coupling = 1 joint
density.
*)

Definition SDistr_squ := product_rmon
  (SDistr) (SDistr).
