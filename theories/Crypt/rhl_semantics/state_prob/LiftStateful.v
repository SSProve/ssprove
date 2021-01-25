From Coq Require Import Morphisms.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".
From Mon Require Import SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import OrderEnrichedRelativeAdjunctions OrderEnrichedRelativeAdjunctionsExamples ChoiceAsOrd.


Import SPropNotations.

Section AuxLemmas.
  Context {A : Type} {P : A -> Prop}.

  Lemma myBetaRed : forall x e, (exist P x e)∙1 = x.
  Proof.
    move=> x e. simpl. reflexivity.
  Qed.


  Context {B : Type}.
  Context (f g : A -> B).
  Lemma funRewrite : f = g -> forall a , f a = g a.
  Proof.
    move=> H. rewrite H. move=> a. reflexivity.
  Qed.



End AuxLemmas.


Section MonotonicBind.
  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  Let J :=
  (ord_functor_comp F_choice_prod SubDistr.chDiscr).
  Context {W : ord_relativeMonad J}.

  Context {AA BB : prod_cat ord_choiceType ord_choiceType}.
  Context (w w' : dfst (W AA)).
  Context (Hw : w ≤ w').
  Context (f : OrdCat⦅ J AA ; W BB⦆).

  Lemma monotonic_bind :
  ((dnib W) f )∙1 w ≤ ((dnib W) f )∙1 w'.
  Proof.
    destruct (dnib W f) as [gg ggmon].
    apply ggmon. assumption.
  Qed.


  Lemma noMoreLets :
  forall f1 f2 : OrdCat⦅ J AA ; W BB ⦆,
  f1 = f2 -> (let (a,_) := dnib W f1 in a) = (let (a,_) := dnib W f2 in a).
  Proof.
    move=> f1 f2. move=> Hf. rewrite Hf. reflexivity.
  Qed.

End MonotonicBind.

Section ComputationalAuxiliary.
  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  (*applied relmon laws for monad I → TypeCat*)
  Context {I : ord_category}.
  Context {J : ord_functor I TypeCat}.
  Context {M : ord_relativeMonad J}.

  Lemma applied_ord_relmon_law1 :
  forall (A : I) x, dnib M (η M A) x = x.
  Proof.
    move=> A. move=> x. rewrite ord_relmon_law1. simpl. reflexivity.
  Qed.


  Lemma applied_ord_relmon_law2 :
  forall (A B : I) (f : TypeCat ⦅ J A; M B ⦆) x, dnib M f ( η M A x ) = f x.
  Proof.
    move=> A B f x.
    unshelve epose (aux := (ord_relmon_law2 M) _ _ _).
      shelve. shelve. exact f.
    unshelve eapply equal_f in aux. exact x. simpl in aux.
    assumption.
  Qed.


  Lemma applied_ord_relmon_law3 :
  forall (A B C : I) (f : TypeCat ⦅ J B; M C ⦆) (g : TypeCat ⦅ J A; M B ⦆) x,
       dnib M (dnib M f ∙ g) x = dnib M f ( dnib M g x).
  Proof.
    move=> A B C f g x.
    epose (aux := (ord_relmon_law3 M) A B C f g).
    unshelve eapply equal_f in aux. exact x.
    assumption.
  Qed.

End ComputationalAuxiliary.

Section ComputationalStatefulLiftDef.
  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  (*The semantic relational framework we are using assumes that there is a relational
    computational monad which is a product of two unary computational monads M1 and M2.
    Here we have Mi : choiceType → Type two choiceType relative unary computational
    monads.
  *)
  Context {M1 M2 : ord_relativeMonad choice_incl}.
  Let M := product_rmon M1 M2. (*relational computational monad*)


  (*The transforming state adjunction*)
  Context {S1 S2 : ord_choiceType}.
  Let TingAdj := Chi_DomainStateAdj S1 S2.

  (*The state transformed computational monad*)
  Let StT_M := AdjTransform M _ _ TingAdj.


  (*We wish to build the lift morphism M → StT_M*)
  Definition StatefulCompLift0 :
  forall A : prod_cat ord_choiceType ord_choiceType,
                   prod_cat TypeCat TypeCat ⦅ ord_functor_id (prod_cat TypeCat TypeCat) (M A);
                   StT_M A ⦆.
  move=> [A1 A2]. simpl. rewrite /F_choice_prod_obj. constructor.
  - move=> m s. eapply (dnib M1).
    move=> a. apply (η M1). simpl. exact (a,s). exact m.
  - move=> m s. eapply (dnib M2).
    move=> a. apply (η M2). simpl. exact (a,s). exact m.
  Defined.

  Let J := prod_functor choice_incl choice_incl.
  Let myChi := natIso_sym (ord_functor_unit_right J).
  Program Definition StatefulCompLift :=
    mkRelMonMorph _ myChi M StT_M StatefulCompLift0 _ _.
  Next Obligation.
    move=> [A1 A2]. f_equal.
    - apply boolp.funext. move=> a. apply boolp.funext. move=> s.
      rewrite /F_choice_prod_obj. simpl.
      epose (bla :=
      (ord_relmon_law2 M1) _ _ (fun a0 : choice.Choice.sort A1 => η M1 (choice.prod_choiceType A1 S1) (a0, s)) ). simpl in bla.
      unshelve eapply equal_f in bla.  exact a.
      assumption.
    - apply boolp.funext. move=> a. apply boolp.funext. move=> s.
      rewrite /F_choice_prod_obj. simpl.
      epose (bla :=
      (ord_relmon_law2 M2) _ _ (fun a0 : choice.Choice.sort A2 => η M2 (choice.prod_choiceType A2 S2) (a0, s)) ). simpl in bla.
      unshelve eapply equal_f in bla.  exact a.
      assumption.
  Qed.
  Next Obligation.
    move=> [A1 A2] [B1 B2]. simpl.
    move=> [k1 k2].
    rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
    simpl. f_equal.
    - apply boolp.funext. move=> m. apply boolp.funext. move=> s.
      (*nice proof technique here*)
      pose (bindbindM1 := (ord_relmon_law3 M1)).
      eapply equal_f in bindbindM1. simpl in bindbindM1.
      erewrite <- bindbindM1. clear bindbindM1.
      (*ends here. We do a similar rewriting in the righthandside*)
      pose (bindbindM1 := (ord_relmon_law3 M1)).
      eapply equal_f in bindbindM1. simpl in bindbindM1.
      erewrite <- bindbindM1. clear bindbindM1.
      (*ends here. The two erewritings are equivalent to the following:*)
      (* rewrite -!applied_ord_relmon_law3. simpl. *)
      f_equal.
      apply boolp.funext. move=> a.
      rewrite ! applied_ord_relmon_law2. reflexivity.
    - apply boolp.funext. move=> m. apply boolp.funext. move=> s.
      rewrite -!applied_ord_relmon_law3. simpl.
      f_equal.
      apply boolp.funext. move=> a.
      rewrite ! applied_ord_relmon_law2. reflexivity.
  Qed.

End ComputationalStatefulLiftDef.


Section SpecificationAuxiliary.

  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  (*applied relmon laws for monad I → TypeCat*)
  Context {I : ord_category}.
  Context {J : ord_functor I OrdCat}.
  Context {M : ord_relativeMonad J}.


  Lemma spec_applied_ord_relmon_law1 :
  forall (A : I) x, (dnib M (η M A))∙1 x = x.
  Proof.
    move=> A. move=> x. rewrite ord_relmon_law1. simpl. reflexivity.
  Qed.


  Lemma spec_applied_ord_relmon_law2 :
  forall (A B : I) (f : OrdCat ⦅ J A; M B ⦆) x, (dnib M f)∙1 ( (η M A)∙1 x ) = f∙1 x.
  Proof.
    move=> A B f x.
    unshelve epose (aux := (ord_relmon_law2 M) _ _ _).
      shelve. shelve. exact f.
    apply (f_equal sval) in aux. simpl in aux.
    unshelve eapply equal_f in aux. exact x. simpl in aux.
    assumption.
  Qed.


  Lemma spec_applied_ord_relmon_law3 :
  forall (A B C : I) (f : OrdCat ⦅ J B; M C ⦆) (g : OrdCat ⦅ J A; M B ⦆) x,
       (dnib M (dnib M f ∙ g))∙1 x = (dnib M f)∙1 ( (dnib M g)∙1 x).
  Proof.
    move=> A B C f g x.
    simpl.
    epose (aux := (ord_relmon_law3 M) A B C f g).
    apply (f_equal sval) in aux. simpl in aux.
    unshelve eapply equal_f in aux. exact x.
    assumption.
  Qed.

End SpecificationAuxiliary.

Section SpecficationStatefulLiftDef.
  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  (*
  A relational specification monad W is a monad relative to
  the product;discrete functor J : choiceType² → Preorder
   *)
  Context {S1 S2 : ord_choiceType}.
  Let J :=
  (ord_functor_comp F_choice_prod SubDistr.chDiscr).
  Context {W : ord_relativeMonad J}.

  (*the state , transforming,  adjunction*)
  Let TingAdj := Chi_CodomainStateAdj S1 S2.

  (*The state transformed spec monad*)
  Let StT_W := AdjTransform W _ _ TingAdj.



  (* We wish to build a rmm morphism lift : W -> StT_W *)


  Program  Definition StatefulSpecLift0 (A : prod_cat ord_choiceType ord_choiceType) :
  OrdCat ⦅ ord_functor_id OrdCat (W A); StT_W A ⦆ := exist _ _ _.
  Next Obligation.
  move=> [A1 A2]. move=> w. unshelve econstructor.
  rewrite /F_choice_prod_obj. cbn.
  move=> [s1 s2].
  unshelve eapply (dnib W). exact ⟨A1,A2⟩.
  unshelve econstructor.
    cbn. move=> [a1 a2]. eapply (η W). exact ((a1,s1),(a2,s2)).
    move=> [a1 a2] [a1' a2']. cbn.
    move=> Ha. inversion Ha. reflexivity.
  exact w.
  move=> [s1 s2] [s1' s2'] Hs. inversion Hs ; reflexivity.
  Defined.
  Next Obligation.
    move=> [A1 A2]. move=> w w'. move=> Hw. move=> [s1 s2].
    cbn.
    eapply monotonic_bind. assumption.
  Qed.


  Let myChi := natIso_sym (ord_functor_unit_right J).
  Program Definition StatefulSpecLift :=
    mkRelMonMorph _ myChi W StT_W StatefulSpecLift0 _ _.
  Next Obligation.
    move=> [A1 A2]. apply sig_eq. cbn.
    apply boolp.funext. move=> [a1 a2]. cbn.
    rewrite /OrderEnrichedRelativeAdjunctions.relKleisli_obligation_1.
    rewrite /F_choice_prod_obj.
    rewrite /StatefulSpecLift0_obligation_1.
    cbn.
    apply sig_eq. cbn. apply boolp.funext.
    move=> [s1 s2].
    pose (bindretW := @spec_applied_ord_relmon_law2 _ _ W).
    cbv in bindretW. rewrite bindretW.
    destruct (η W ⟨prod_choiceType A1 S1, prod_choiceType A2 S2⟩).
    cbn. reflexivity.
  Qed.
  Next Obligation.
    move=> [A1 A2] [B1 B2] [ff ffmon].
    apply sig_eq. cbn. apply boolp.funext. move=> w.
    rewrite /StatefulSpecLift0_obligation_1. cbn.
    apply sig_eq. cbn. apply boolp.funext.
    move=> [s1 s2].
    cbn.
    pose (bindbindW := (@spec_applied_ord_relmon_law3 _ _ W)).
    cbv in bindbindW. rewrite -bindbindW.
    unfold "∙1". cbn. rewrite -bindbindW.
    (* destruct ( η W ⟨ prod_choiceType A1 S1, prod_choiceType A2 S2 ⟩ ) *)
    (*     as [eta_as eta_as1_mon]. *)
    (* destruct ( η W ⟨ prod_choiceType B1 S1, prod_choiceType B2 S2 ⟩ ) *)
    (*     as [eta_bs eta_bs_mon]. *)
    cbn.
    move: w. apply funRewrite. apply noMoreLets. apply sig_eq.
    cbn. apply boolp.funext. move=> [a1 a2].
    pose (bindretW := (@spec_applied_ord_relmon_law2 _ _ W)).
    cbv in bindretW. rewrite bindretW. reflexivity.
  Qed.

End SpecficationStatefulLiftDef.
