From Coq Require Import ssreflect ssrfun FunctionalExtensionality List Arith ZArith.
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads DijkstraMonadExamples.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Relational Require Import Imp OrderEnrichedCategory OrderEnrichedRelativeMonadExamples RelationalState RelationalNDD RelationalNDA RelationalExcSimple Commutativity GenericRulesSimple GenericRulesComplex RelationalExcFull.



Import SPropNotations.
Import DijkstraMonadNotations.

(********************************************************************)
(* This file is intended to collect the notions presented in the
   paper and formalised in Coq.                                     *)
(********************************************************************)


(********************************************************************)
(*** SIMPLIFIED FRAMEWORK                                         ***)
(********************************************************************)

(********************************************************************)
(*** From Effects to Monads *)
(********************************************************************)

(* Definition of monads *)
Print Monad.

Check ret.
Check bind.

(* Classical examples of computational monads *)

(* Stateful computations, parametrized by a type S *)
Check (St _).
Eval cbv in (St _ _).
Check get.
Check put.

(* Exceptions, also a free monad parametrized by a type E of exceptions *)
Check (Exn _).
Check (raise _).

(* IO, a free monad parametrized by the types of Input and Ouput *)
Check (IO _ _).
Check read.
Check write.

(* A version of non-determinism based on predicates *)
Check NDSet.
Eval cbv in (NDSet _).
Check pick_set.

(* Non-determinism, implemented with lists *)
(* it does not satisfy commutativity and idempotency
   but it has a more computational feeling *)
Check ListM.
Eval cbv in (ListM _).
Check pick.

(* Imp-like monad *)
Check Imp.
Check do_while.

(********************************************************************)
(*** Specifications as Relative Monads *)
(********************************************************************)

(* Definition simple relational specification monads *)
Print ord_relativeMonad.
Eval cbv in RelationalSpecMonad0.

(* Backward predicate transformer: WPurerel *)
Definition WPurerel : RelationalSpecMonad0 :=  relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon (MonoContSProp)).
Eval cbv in WPurerel.

(* Pre-/postconditions: PPPurerel *)
Definition PPPurerel : RelationalSpecMonad0 := relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon (PrePost.PPSpecMonad)).
Eval cbv in PPPurerel.

(* Pre-/postconditions with state: PPSTrel *)
(* Depends on the Equations Coq libray *)
(* From Mon.SM Require Import SMMonadExamples. *)
(* Definition PPStrel (S1 S2 : Type ): RelationalSpecMonad0 := *)
(*   relativeMonad_precomposition typeCat_prod *)
(*                                (ordmonad_to_relmon (ST_T (S1 × S2) PrePost.PPSpecMonad)). *)
(* Eval cbv in fun A1 A2 => PPStrel _ _ ⟨A1,A2⟩. *)

(* Errorful backward predicate transformer *)
Definition WErrrel : RelationalSpecMonad0 := RelErr.
Eval cbv in WErrrel.

(********************************************************************)
(*** Relational Semantics from Effect Observations *)
(********************************************************************)

(* Definition simple relational effect observation *)
(*  see also 3.4 on simple relational effect
    observations as relative monad morphisms       *)
Print relativeMonadMorphism.
Eval cbv in RelationalEffectObservation0.

(* Simple relational effect observation on WStrel *)
Check θSt.

(* Simple relational effect observation for ND *)
Check θforallrel : RelationalEffectObservation0 NDSet NDSet WPurerel.
Check θexistsrel : RelationalEffectObservation0 NDSet NDSet WPurerel.

(* Theorem 1 *)
Check commute_effObs.

(* Semantic relational judgement *)
Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ c1 c2 w).
Check semantic_judgement.


(********************************************************************)
(*** Pure Relational Rules *)
(********************************************************************)

(* Bool elim *)
Check if_rule.

(* Nat elim *)
Check nat_rect_rule.

(********************************************************************)
(*** Generic Monadic Rules *)
(********************************************************************)

(* Ret rule *)
Check ret_rule2.

(* Weaken rule *)
Check weaken_rule2.

(* Bind rule *)
Check seq_rule.

(* Theorem 2 comes from the fact that these rules are proven lemmas *)

(********************************************************************)
(*** Effect-specific Rules *)
(********************************************************************)

(* Non-deterministic computations *)
Print demonic_left_rule_w.
Check demonic_left_rule.

Print angelic_rule_w.
Check angelic_rule.

(* Exceptions using WErrrel *)
Check θErr.

Print fail_spec.
Check raise_l_rule.
Check raise_r_rule.

Print catch_spec.
Check catch_rule.

(* Unbounded iteration *)
(*   we admit the commutativity condition from Theorem 1 as
     it requires reasoning about omega-cpos that we have not
     yet finished formalising *)
Check θPart.
(*   admitted as well, as it depends on θPart *)
Check do_while_rule.

(********************************************************************)
(*** Example: non-interference *)
(********************************************************************)

Eval cbv in NI_pre_post.
Print NI.

Print prog5.
Check prog5_satisfies_NI.

(* see other concrete examples in Relational/RelationalState.v *)

(********************************************************************)
(*** GENERIC FRAMEWORK                                            ***)
(********************************************************************)

Eval lazy in ExcExc.Wrc _.

(* relational component of bind *)
Eval cbn in rsmc_act ExcExc.Wrc.

(********************************************************************)
(*** PRODUCT PROGRAMS                                             ***)
(********************************************************************)

(* For monads M1 = M2 = St (bool -> nat),
   product programs are defined as
    P(A1, A2) = St (bool + bool -> nat) (A1 × A2) *)

(* First, construction of the relation c1 x c2 ~> c *)
Check st_rel.

(* Second, we define the ζ *)
Check ζSt.

(* Finally, the theorem 4 *)
Check coupling_soundness.
