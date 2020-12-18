From Coq Require Import ssreflect.
From ITree Require Import ITree ITreeFacts.
From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads.

Import ITreeNotations.

Section ProbEvent.
  Context (R : reals.Real.Exports.realType).

  (*The following type describes a (Bernouilli) sampling event.
  We specificy to the env with what probability the bit should
  be drawn from bool. The environment then provides a boolean.
  This external event type could be made more complex to handle
  more randomness (see commented constructor).
   *)
  Inductive probE : Type -> Type :=
  |Bern : unit_interval R -> probE bool
  (*|Poisson : (λ : unit_interval R) → probE nat *).

End ProbEvent.


Section ProbHandler.
  (*We interpret probabilities directly using the specification monad
    depicted in Finiteprobabilities.v. This monad is a continuation
    monad with answer type [0,1].
    *)
  Context {R : reals.Real.Exports.realType}.
  Definition Pro := monad_tyop (omon_monad (WI R)).

  Definition prob_handler : (probE R) ~> Pro.
  intro A. intro pe. unfold Pro. unfold WI.
  unfold MonoCont. Abort.

  Definition iter_for_probas
  {A B: Type} (body : (A -> Pro (A + B)%type)) (a:A) :  Pro B. Abort.

End ProbHandler.
