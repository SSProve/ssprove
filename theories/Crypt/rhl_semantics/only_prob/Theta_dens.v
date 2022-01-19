From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase FiniteProbabilities.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From Crypt Require Import ChoiceAsOrd Axioms RelativeMonadMorph_prod FreeProbProg SubDistr choice_type.


Import SPropNotations.
Import Num.Theory.

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

(* Section test. *)
(*   (*In this section we implement a probability handler, ie something of type *)
(*   forall T : choice_type, probE T -> SDistr T*) *)
(*   (*This kind of handler is exactly the data needed to define a universal map exiting *)
(*   the free probablistic relative monad defined in FreeProbProg.v. Is abstracted over *)
(*   in the subsequent sections. *) *)

(*   Program Local Definition myzero : unit_interval R := exist _ 0 _. *)
(*   Next Obligation. *)
(*     apply /andP ; split. *)
(*     apply lerr. eapply (@ler01 R). *)
(*   Qed. *)

(*   Inductive concrete_probE : Type -> Type := *)
(*     |Bern : unit_interval R -> concrete_probE bool *)
(*     |Poiss : unit_interval R -> concrete_probE nat. *)

(*   Record my_choice_type : Type := mk_choice_type *)
(*     { abs_chTy :> choiceType ; *)
(*       unlock_absChTy : ((abs_chTy = bool_choiceType) + ( abs_chTy = nat_choiceType))%type *)
(*     }. *)

(*   Definition my_chElement : my_choice_type -> choiceType := fun relChTy => *)
(*     match relChTy with *)
(*     |mk_choice_type T unlock_T => *)
(*     match unlock_T with *)
(*     |inl unlock_bool => bool_choiceType *)
(*     |inr unlock_nat => nat_choiceType *)
(*     end *)
(*     end. *)

(*   Definition my_concrete_probhandler : forall T : choiceType, *)
(*   concrete_probE T -> SDistr T := fun T opp => *)
(*     match opp with *)
(*     |Bern p => dnull (*to replace with the relevant mass function*) *)
(*     |Poiss λ => dnull *)
(*   end. *)

(* End test. *)



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


  Definition unary_ThetaDens0 : forall (A:choiceType) (tree : rFreePr A),
  SDistr_carrier A.
    move=> A. elim=> [a | [X op] /= sbtrs IH].
      apply SDistr_unit. simpl. assumption.
    (*IH: each subtree, indexed by x:chElement X has already produced a SDistr A*)
    eapply SDistr_bind. all: revgoals.
      exact op.
    (*now the continuation. *)
    simpl. exact IH.
  Defined.

  Program Definition unary_theta_dens :
  relativeMonadMorphism (ord_functor_id TypeCat) (commuting_unary_base_square)
  (rFreePr) (SDistr) :=
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


Section Relational_effobs.
  (*We just need to square unary_theta_dens to obtain the desired relational effect
   observation.*)

  Definition theta_dens :=
    prod_relativeMonadMorphism unary_theta_dens unary_theta_dens.

End Relational_effobs.


