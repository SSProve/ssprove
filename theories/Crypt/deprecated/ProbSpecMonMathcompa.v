From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase SRelationClasses SMorphisms FiniteProbabilities.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
From Crypt Require Import ChoiceAsOrd.

Import SPropNotations.
Import Num.Theory.

Notation "⟦ b ⟧" := (is_true_sprop b).
Infix "-s>" := (s_impl) (right associativity, at level 86, only parsing).

Local Open Scope ring_scope.

(*
In this file we try to devise a relational specification monad for
probabilities. It ressembles the continuation monad A1 A2 ↦ (A1 × A2 → I) → I
but we take care of measurability conditions.

-The first part of the file is dedicated to the unary version of this monad,
which we call the Daniell monad (or pick a relevant name: Giry (measures),
distribution monad (confusion with densities), probability (fuzzy name),
expectation )
See Daniell integral.
It is still a relative monad though because
of our restriction to choiceTypes. It is a relative monad over
discr : chTy → Poset.
It uses the notion of distribution (aka sub mass function) defined
in the mathcomp analysis library, in the file distr.v.

-The second part of the file defines the relevant relative monad by
precomposing.
chTy × chTy → chTy → Poset.
*)

Section Hanging_computations.
(*In this section we keep track of the various computational blows up
  encountered
  using mathcomp, and of our investigations regarding this issue.*)
  Context (R:realType)
  (absordd : R -> R -> bool).

  (*Blow up 1*)
  Fail Timeout 1 Eval cbv in fun (R:realType) (x y : R) => x <= y.

  (*Blow up 2*)
  Record PDanCarrier0 (A : choiceType) := mkPDanCarrier0 {
    Pdan_point : {distr A/R} -> R ;
    Pdan_monotonic : forall (mu1 mu2 : {distr A/R}) (x:A),
     absordd (mu1 x) (mu2 x) -> absordd (Pdan_point mu1) (Pdan_point mu2)
}.

  Eval vm_compute in fun A => Pdan_point A.

  Fail Timeout 1 Eval cbv in
  fun A => Pdan_point A.

  (*now we remove the second field of the record*)
  Record PPDanCarrier0 (A : choiceType) := mkPPDanCarrier0 {
    PPdan_point : {distr A/R} -> R
}.

  (*it doesnt hang anymore*)
  Eval cbv in fun A => PPdan_point A.

End Hanging_computations.


Section Hiding_techniques.
(*The following Eval cbv in fun x y : R => x <= y hangs, for R:realType.
That is why we try to opaque it. This section lists the various techniques
we tried.*)

  (*hiding technique 0: similar to the one below, and to the module type
  trick. The idea is to work in a section with Context
  (abstract : bool) (unlock : abstract = true). *)
  (*for some reason when using unlock in a rewrite it is good to provide
  the occurence switch {1} (refers to the first occurence). *)

  (*hiding technique 1*)
  Record singleton_true : Type := mk_singletonTrue {
    sealed_true : bool;
    unlock_true : sealed_true = true
  }.

  Program Definition true_true_boolean := mk_singletonTrue true _.

  (*hiding technique 2. I dont know how to unseal*)
  Program Definition bla : bool := _.
  Next Obligation. exact true. Qed.

  (*hiding technique 3: the module type trick. more or less similar to
  technique 1? *)

  (*hiding technique 4: nosimpl, locked, locked_with. this stuff prevents
  simplification*)

  (*hiding technique 5: Opaque, Transparent. Does not always prevent
  computations*)

End Hiding_techniques.


(*order enrinched embedding of chTy into Poset (the latter is called OrdCat)*)
Definition chDiscr : ord_functor ord_choiceType OrdCat
  := ord_functor_comp (choice_incl) (discr).


Section DaniellMonad.
  Context (R:realType).
  (*the following is needed to seal the comparison operator for reals,
  which blows up when cbv'ed.
  Apparently it is sometimes necessary to use rewrite {1}unlock_asbord
  instead of just rewrite unlock_absord, for some reason.*)
  Context (absord : R -> R -> bool)
  (unlock_absord : absord = (fun x y : R => x <= y)).

  (*we need more conditions on the external arrow (additivity, scott cont ?)
  I don't know if we need the restriction to be SProp like.*)
  (*By definition, distribution are positive functions A -> R, which are
  -  summable: integrable for discrete sigma algebra, ie sums over finite
     parts of A are overall minored by a global upper bound M
  -  such that their discrete integral is less than 1*)
  Record DanCarrier0 (A : choiceType) := mkDanCarrier0 {
    dan_point :> {distr A/R} -> R ;
    (*could be good to use proper here ?*)
    dan_monotonic : forall (mu1 mu2 : {distr A/R}),
      (forall x:A, absord (mu1 x) (mu2 x)) -> absord (dan_point mu1) (dan_point mu2);
    (*wkst preconditions actually land into the interval [01].
    can not infer this from the other conditions*)
    dan_sub : forall mu,
      (absord 0 (dan_point mu)) /\ (absord (dan_point mu) 1)
}.

  (* This hangs: Eval cbv in fun A:choiceType => dan_point A. *)

  (*we need to endow DanCarrier A  with a poset structure, taken
    pointwise. see OrdCat definition .*)
  Program Definition DanCarrier0_order A : srelation (DanCarrier0 A) :=
    fun ff1 ff2 =>
    pointwise_srelation {distr A/R} (fun x y =>  ⟦absord x y⟧) ff1 ff2.

  (*Eval cbv in DanCarrier0_order hangs. see section hanging computations*)
  Eval vm_compute in DanCarrier0_order.

  Instance DanCarrier0_order_preorder A : PreOrder (@DanCarrier0_order A).
  Proof.
    constructor.
      vm_compute. intros ff mu. apply its_true_anyway.
      rewrite {1}unlock_absord. apply lerr.
    vm_compute. intros ff1 ff2 ff3. intros H12 H23. intro mu.
    pose H12mu := (H12 mu). pose H23mu := (H23 mu).
    apply since_its_true in H12mu. apply since_its_true in H23mu.
    apply its_true_anyway. clear H12 H23.
    rewrite {1}unlock_absord in H12mu. rewrite {1}unlock_absord in H23mu.
    rewrite {1}unlock_absord.
    unshelve eapply ler_trans.
    exact ((let (dan_point, _,_) := ff2 in dan_point) mu).
    assumption. assumption.
  Qed.

  Program Definition DanCarrier (A : choiceType) : OrdCat.
      unshelve econstructor. exact (DanCarrier0 A).
    exact (Sexists _ (DanCarrier0_order A) (DanCarrier0_order_preorder A) ).
  Defined.

  Program Definition DanUnit (A : ord_choiceType)
  : OrdCat ⦅ chDiscr A; DanCarrier A ⦆.
    unshelve econstructor.
    (*carrier of the unit*)
    vm_compute. intro a.
    unshelve econstructor. intro mu. exact (mu a).
    intros mu1 mu2 H. vm_compute. apply (H a).
    intro mu. pose (le1_mu1 mu).
    split. destruct mu as [mu zmu mu_sum mu_sub]. rewrite unlock_absord.
    apply (zmu a).
    rewrite {1}unlock_absord. apply (i a).
    vm_compute. intros a1 a2. intro sH. intro mu. destruct sH.
    apply its_true_anyway. rewrite {1}unlock_absord. apply lerr.
  Defined.

(*The following is needed to define bind in a continuation style*)
  Program Definition  mk_tempDistr (A B : ord_choiceType)
    (fff : OrdCat ⦅ chDiscr A; DanCarrier B ⦆) (mu : {distr B / R})
    : {distr A/R}.
    destruct fff as [fff _]. vm_compute in fff.
    unshelve econstructor.
    (*carrier*)
    exact (fun a => fff a mu).
    (*zero less than carrier*)
    intro x. simpl. destruct (fff x) as [fff_point fff_mon fff_sub].
    simpl. pose (from_fff_sub := fff_sub mu). destruct from_fff_sub as
    [from_fff_sub0 from_fff_sub1]. rewrite unlock_absord in from_fff_sub0.
    assumption.
    (*the carrier needs to be summable *)
    unshelve econstructor. Abort.


  Program Definition DanBind : forall A B : ord_choiceType,
                      OrdCat ⦅ chDiscr A; DanCarrier B ⦆ ->
                      OrdCat ⦅ DanCarrier A; DanCarrier B ⦆.
    intros A B fff. unshelve econstructor. intro mmm. vm_compute.
    unshelve econstructor. intro mu.
    (*carrier*)
    vm_compute in mmm.
    destruct mmm as [mmm mono_mmm sub_mmm]. vm_compute in fff.
    destruct fff as [fff mono_fff]. clear mono_fff.
      (*we need to define an intermediary distr with carrier fun a => fff a mu*)
    assert (temp : {distr A/R}). unshelve econstructor. exact (fun a => fff a mu).
    intro x. simpl. destruct (fff x) as [fff_point fff_mon fff_sub].
    simpl. pose (from_fff_sub := fff_sub mu). destruct from_fff_sub as
    [from_fff_sub0 from_fff_sub1]. rewrite unlock_absord in from_fff_sub0.
    assumption.


unshelve epose (from_monofff := mono_fff x x _).
    reflexivity.



exact (mmm (fun a => fff a mu)).

  Program Definition Dan : ord_relativeMonad chDiscr := {|
    ord_relmonObj := DanCarrier ;
    ord_relmon_unit := DanUnit ;
    ord_relmon_bind := _ |}.
  Next Obligation.
    unshelve econstructor. intro a. cbv. intro mu. exact (mu a).
    unfold SProper. unfold "s==>". intros a b Hab. Set Printing All.
    cbv. Eval simpl in extract_ord

    @mkOrdRelativeMonad ord_choiceType OrdCat chDiscr  _ _ _ _ _ _ _.


End DaniellMonad.
