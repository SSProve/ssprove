From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase SRelationClasses.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
From mathcomp Require Import all_ssreflect all_algebra reals distr.
From Crypt Require Import ChoiceAsOrd.

Import SPropNotations.
(*
In this file we try to devise a lax relational effect observation having
1) as computations, twice the free probability monad ProbM which is defined
in OrderEnrichedcategory.
2) as specifications, A1 A2 ↦ (A1 × A2 → I) → I (called WI)
or maybe something more involved (measurability conditions)
This lax effect observation is defined using an infimum on possible
couplings = joint distributions of the two probabilistic programs.

θ == λ c1 c2 post. inf[d~(c1,c2)] ∑[A1×A2] d(a1,a2)*post(a1,a2)

We need big sums so we need to restrict ourselve to mathcomp choiceType
the current plan is the following

- register choiceType as the right notion of category. One has to be
able to define ord_relativeMonad instances with domain choiceType × choiceType.
-> ord_category instance

- On the computation side, we don't directly need two monads. The goal is
to define the freeproba monad as a relative monad
over ι : choiceType → Type basically.
some remarks
+ this approach is isomorphic but more painful than the following: define the
computational relative monad by precomposing ProbComppair (provided in the
early experinments on probas) by choice_incl.
  chTy × chTy ⟶ Ty × Ty ⟶ Ty × Ty.
+If we wish to work in a more
traditional style with two computational monads
(which involves proving that freeproba (A:choiceType) is still a choicetype)
then we can reuse this approach by precomposing the obtained lax relataional
effect observation with a relative monad morphism corresponding to the inclusion
ι : choiceTYpe → Type.

- the relational specification is basically obtained by precomposing with the
product of choiceType.
/!\ maybe we will need a measurability restriction ? restrict to summable stuff?
maybe we'll use the mathcomp distr.v file.

- finally we will be able to define the expected relational eff obs because
we can sum over choice types
*)

(*
Section ChoiceAsOrd.


  Program Definition ord_choiceType : ord_category :=
    mkOrdCategory choiceType
               (fun A B => A -> B)
               (fun _ _ f g => forall x, f x ≡ g x) _
               (fun A a => a)
               (fun _ _ _ f g x => f (g x))
               _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; estransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. induction (H0 x1). apply H. Qed.

End ChoiceAsOrd.

Program Definition choice_incl := @mkOrdFunctor ord_choiceType TypeCat
    (fun (A:ord_choiceType) => A)
    (fun (A B : ord_choiceType) f => f)
    _ _ _.
  Next Obligation. cbv ; intuition. Qed.
*)

Section Computations.
(*
We devise a computational relative monad chTy × chTy → Ty × Ty by
precomposing with the above inclusion functor.
Note that there is a way to reuse this if we want to explicitly deal with
nonrelative monads.
*)
  Context (R : realType).

  Definition ProbCompPair := compPair (ProbM R) (ProbM R).

  Let incl := prod_functor choice_incl choice_incl.
  Definition chProbCompPair :=
    relativeMonad_precomposition incl ProbCompPair.

End Computations.

Section JointDistributions.
(*
We have to define what is a joint distribution of two probabilistic programs.
It is a monadic program with answer type A1 × A2 such that its marginals
are the original programs.
Maybe well use the mathcomp type distr instead, in order to be able to do
barycentric sums afterward.
*)
  Context (R : realType).

  Definition couplings_of {A1 A2 : Type} (c1 : ProbM R A1) (c2 : ProbM R A2)
  : Type :=
    @sig (ProbM R (A1 * A2)%type)
         (fun d => SPropMonadicStructures.map fst d = c1  /\
                 SPropMonadicStructures.map snd d = c2).

End JointDistributions.

Section Specifications.
(*
We are probably going to use the mathcomp distr.v file.
But for now we stick to WI ?
See Daniell integral
*)
  Context (R : realType ).

  Definition ProbWrel := Wrel (WI R). (*   (_ × _ → I) → I  *)

End Specifications.


Section EffectObservation.
  Context (R : realType ).
(*
We want to inhabit this type
RelationalLaxEffectObservation0 (ProbM R) (ProbM R) (ProbWrel R).
*)
  Program Definition bla :
  RelationalLaxEffectObservation0 (ProbM R) (ProbM R) (ProbWrel R) :=
  mkRelLaxMonMorph _ _ _ _ _ _ _.
  Next Obligation.
    unshelve econstructor. destruct A as (A1,A2). simpl.
    intros (c1 , c2). unfold MonoContCarrier.
    unshelve econstructor.
  Abort All.

