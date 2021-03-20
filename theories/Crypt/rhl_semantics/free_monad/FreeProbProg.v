Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect boolp.
Set Warnings "notation-overridden".
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd chUniverse.
From Crypt Require Import SubDistr.


(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we pack pairs of free probabilistic computations into a
(order enriched) relative monad instance (see ord_relativeMonad).

Some informations about free monads:

The unary Free monad can be parametrized by a collection of operations S
and arities for those operations (somth of type S -> choiceType).
Concretely S could be the collection {(sample_bollean p) | p in [01]}, ie
one Bernouilli sampling operation for each probability p. In this case
the arity predicate (ar : S -> choiceType) would map each operation to bool
(or rather the choiceType instance for bool).
Indeed we expect the environment to either return true or false after
a Bernouilli sampling operation has been issued to it.

We take S = { X: chUniverse & SDistr X }, that is, each subdistribution
sampling from a choiceType present in chUniverse (a small universe of choiceTypes)
is considered as being part of our probabilistic signature (S,P)
where P : S -> choiceType is the first projection.


NOTE regarding ancient design:

Note that before we were specifying a probabilistic operation with
an ITree like event type 
Inductive probE : Type -> Type :=
  |Bern : unit_interval R -> probE bool
  |Poisson : (λ : unit_interval R) → probE nat.
The parameter of the inductive is supposed to be the type of the valued
returned by the environment after an operation has been issued. The
parameters of the constructors are supposed to represent the information
we would like to pass when we issue an operation. For instance when
sampling uniformly a boolean we need to provide a probability p : [O,1].
We were using this last way of specifying sampling operations generically
and we were translating this signature 
internally into a collection of operations S and an
arity predicate ar : S -> choiceType
*)

Section Extensionality_for_ordfunctors.
  (*work in progress*)

  (*the following relies on proof irrelevance (see file axioms)*)
  (*/!\ also need the arrow map*)
  Lemma functor_ext : forall (C D : ord_category) (F G : ord_functor C D),
  (forall A : C, F A = G A) -> F = G.
  Proof.
    intros C D F G H.  apply boolp.funext in H.
    destruct F as [F F2 F3 F4 F5]. destruct G as [G G2 G3 G4 G5].
    simpl in H.
    move: F2 F3 F4 F5 G2 G3 G4 G5.
    rewrite !H. intuition. assert (FG2 : F2 = G2).
  Abort.

End Extensionality_for_ordfunctors.


Section RelativeFreeMonad.
  (*This section defines a unary free monad relative to choice_incl.
   In this section the free relative monad is parametrized by an arbitrary
   set S of operations. In subsequent sections this set S is an actual set of
   probabilistic operations. *)


  (* A signature where S is the type of operations and P describes the
     arity of each operations *)
  Context (S : Type) (P : S  -> choiceType).


  Inductive rFreeF (A : choiceType) : Type :=
  | retrFree : A -> rFreeF A
  | ropr     : forall s, (P s -> rFreeF A) -> rFreeF A.

  Arguments ropr [A] _ _.

  Fixpoint bindrFree {A B : choiceType} (c : rFreeF A)
  (k : TypeCat ⦅ choice_incl A ; rFreeF B ⦆ )
  : rFreeF B :=
    match c with
    | retrFree a => k a
    | ropr s ar  => ropr s (fun p => bindrFree (ar p) k)
    end.

  Definition callrFree (s : S) : rFreeF (P s) := ropr s (fun k => retrFree _ k).


  Program Definition rFree : ord_relativeMonad choice_incl :=
    @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl rFreeF _ _ _ _ _ _.
  Next Obligation. constructor. assumption. Defined.
  Next Obligation.
    intros A B. intros ff mm. exact (bindrFree mm ff).
  Defined.
  Next Obligation.
    cbv ; intuition. f_equal. apply funext. move=> a. eapply H.
  Qed.
  Next Obligation.
    intro A. apply funext.
    intro c. elim: c.
      simpl. reflexivity.
    intros s ar IH. simpl. f_equal. apply funext.
    assumption.
  Qed.
  Next Obligation.
    intros.
    apply funext. intro c. induction c.
      simpl. reflexivity.
    simpl. f_equal. apply funext. intro p.
    eapply H.
  Qed.

End RelativeFreeMonad.

Section Unary_free_prob_monad.

  (* the type of probabilistic operations*)
  Definition P_OP  := { X : chUniverse & SDistr X }.
  
  (* the arities for operations in OPP*)
  Definition P_AR : P_OP -> choiceType :=
    fun op => chElement ( projT1 op ).

  Definition rFreePr := rFree P_OP P_AR.

  Context (Hch : forall r : chUniverse, chElement r).

  Definition sample_from { A } (D : rFreePr A) : A.
  Proof.
    elim: D => [ a | s Ps IH].
    - exact: a.
    - apply: IH.
      destruct s. simpl in *.
        by apply: Hch.
   Defined.

End Unary_free_prob_monad.


Section Pairs_of_probabilistic_computations.
  (*We want to obtain a product of relative monads, the product of rFreePr
  with itself. We use the support for product of relative
  monads provided by the dm4all devlopment .*)

  Definition rFreeProb_squ_fromProd :=
    product_rmon rFreePr rFreePr.

  (*alias for retro compatibility*)
  Definition rFreeProb_squ := rFreeProb_squ_fromProd.

End Pairs_of_probabilistic_computations.
