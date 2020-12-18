From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase FiniteProbabilities.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
From Crypt Require Import ChoiceAsOrd Axioms RelativeMonadMorph_prod only_prob.FreeProbProg
only_prob.SubDistr.


Import SPropNotations.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.

(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*In this file we define a relative monad morphism between
- Pairs of probabilistic computations written in a free way
  (see file FreeProbProg.v).
- Pairs of probabilistic computations written as subdistributions
  (see file SubDistr.v)

It is possible to define this relative monad morphism as a product of
two unary relative monad morphisms, each of them going from rFreePr to
SDistr.
*)

Section test.
  (*In this section we implement a probability handler, ie something of type
  forall T : rel_choiceTypes, probE T -> SDistr T*)
  (*This kind of handler is exactly the data needed to define a universal map exiting
  the free probablistic relative monad defined in FreeProbProg.v. Is abstracted over
  in the subsequent sections. *)

  Program Local Definition myzero : unit_interval R := exist _ 0 _.
  Next Obligation.
    apply /andP ; split.
    apply lerr. eapply (@ler01 R).
  Qed.

  Inductive concrete_probE : Type -> Type :=
    |Bern : unit_interval R -> concrete_probE bool
    |Poiss : unit_interval R -> concrete_probE nat.

  Record my_rel_choiceTypes : Type := mk_rel_choiceTypes
    { abs_chTy :> choiceType ;
      unlock_absChTy : ((abs_chTy = bool_choiceType) + ( abs_chTy = nat_choiceType))%type
    }.

  Definition my_chEmb : my_rel_choiceTypes -> choiceType := fun relChTy =>
    match relChTy with
    |mk_rel_choiceTypes T unlock_T =>
    match unlock_T with
    |inl unlock_bool => bool_choiceType
    |inr unlock_nat => nat_choiceType
    end
    end.

  Definition my_concrete_probhandler : forall T : choiceType,
  concrete_probE T -> SDistr T := fun T opp =>
    match opp with
    |Bern p => dnull (*to replace with the relevant mass function*)
    |Poiss λ => dnull
  end.

End test.



Section Unary_effobs.
  (*In this section we define a unary effect observation between
   (1) the free relative probabilistic monad (a relative monad over the
   the choice inclusion)
   (2) The relative monad of subdistributions

   We take the square of this morphism in subsequent sections to obtain
   the desired relational (vs unary) effect observation

   the unary effect observation is the universal map exiting the free
   relative monad. Consequently it is defined inductively, just using a
   probablity handler which transform operations into actual distributions*)

  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).

  Definition commuting_unary_base_square :
  natIso (choice_incl)
         (ord_functor_comp choice_incl (ord_functor_id TypeCat)).
    unshelve econstructor.
    intro A. intro a. cbv.  assumption.
    intro A. intro a. cbv in a. cbv. assumption.
    intros A B f. cbv. reflexivity.
    intros A. cbv. reflexivity.
    intro A. cbv. reflexivity.
  Defined.


  Local Definition S := Prob_ops_collection probE rel_choiceTypes chEmb.
  Local Definition Ar := Prob_arities probE rel_choiceTypes chEmb.

(*  | ropr     : forall s, (P s -> rFreeF A) -> rFreeF A.*)
  Definition unary_ThetaDens0 : forall (A:choiceType) (tree : rFreeF S Ar A),
  SDistr_carrier A.
    intro A. elim=> [a | [relchty op] /= sbtrs IH].
      apply SDistr_unit. simpl. assumption.
    (*IH: each subtree, indexed by x:chEmb relchty has already produced a SDistr A*)
    (*sbtrs: the trees below s = (relchty, op)*)
    refine ((SDistr_bind (chEmb relchty) A _) _). all:revgoals.
    (*we turn s into a subdistr, using the available handler.*)
    apply (prob_handler (chEmb relchty)). exact op.
    (*now the continuation. *)
    simpl. exact IH.
  Defined.

  Program Definition unary_theta_dens :
  relativeMonadMorphism (ord_functor_id TypeCat) (commuting_unary_base_square)
  (rFreePr probE rel_choiceTypes chEmb) (SDistr) :=
    mkRelMonMorph (ord_functor_id TypeCat) (commuting_unary_base_square) _ _ _ _ _.
  Next Obligation.
    intros A tree. exact (unary_ThetaDens0 A tree).
  Defined.
  Next Obligation. (*theta of bind = bind of theta basically*)
    intros A B ff.
    apply boolp.funext. intro tree. elim: tree => [a | [relchty op] /= sbtrs IH].
    (*ret is mapped to ret ?*)
    simpl. pose (toUse := SDistr_leftneutral). apply distr_ext. intro b.
    rewrite dlet_unit. reflexivity.
    (*bind is mapped to bind ?*)
    apply distr_ext. intro b.
    unfold SDistr_bind. rewrite dlet_dlet. f_equal. f_equal.
    apply boolp.funext. intro x.  pose (fromIH := IH x).
    apply fromIH.
  Qed.

End Unary_effobs.

Arguments unary_theta_dens {probE} {rel_choiceTypes} {chEmb} _.

Section Relational_effobs.
  (*We just need to square unary_theta_dens to obtain the desired relational effect
   observation.*)
  Context {probE : Type -> Type}. (*an interface for probabilistic events*)
  Context {rel_choiceTypes : Type}
          {chEmb : rel_choiceTypes -> choiceType}.
  Context (prob_handler : forall (T:choiceType),
    probE T -> SDistr T).
  Definition theta_dens :=
    prod_relativeMonadMorphism (@unary_theta_dens probE rel_choiceTypes chEmb prob_handler)
                               (@unary_theta_dens probE rel_choiceTypes chEmb prob_handler).
End Relational_effobs.


