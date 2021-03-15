Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect boolp.
Set Warnings "notation-overridden".
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd.


(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we pack pairs of free probabilistic computations into a
(order enriched) relative monad instance (see ord_relativeMonad).

Some informations about free monads:

The unary Free monad can be parametrized by a collection of operations S
and arities for those operations (somth of type S -> Type).
Concretely S could be the collection {(sample_bollean p) | p in [01]}, ie
one Bernouilli sampling operation for each probability p. In this case
the arity predicate (ar : S -> Type) would map each operation to bool.
Indeed we expect the environment to either return true or false after
a Bernouilli sampling operation has been issued to it.

On the other hand it is aslo possible to specify
free monads using event types ("functors")
The follwoing is stolen from the ITree Coq library
Inductive probE : Type -> Type :=
  |Bern : unit_interval R -> probE bool
  |Poisson : (λ : unit_interval R) → probE nat.
The parameter of the inductive is supposed to be the type of the valued
returned by the environment after an operation has been issued. The
parameters of the constructors are supposed to represent the information
we would like to pass when we issue an operation. For instance when
sampling uniformly a boolean we need to provide a probability p : [O,1].

We use this last way of specifying sampling operations generically and
translate it internally into a collection of operations S and an
arity predicate ar : S -> Type (needed for the Free monad implementation
in the dm4all devlopment).
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
    rewrite !H. intuition. assert (FG2 : F2 = G2). Abort.

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

Section Translation.
  (*In this section we translate a probabilistic signature into a set of operations S
  and an arity prediacte ar : S -> Type as expected by rFree (defined in the section
  RelativeFreemonad)*)


  (*We specify a probabilistic signature using ITree like events type: *)
  Context (probE : Type -> Type).
  (*for instance the above could be defined like so
  Inductive concrete_probE : Type -> Type :=
  |Bern : unit_interval R -> concrete_probE bool
  |Poiss : unit_interval R -> concrete_probE nat.

  The parameter of this interface has to be understood as the type of values returned
  by the environment after we issue some operation (as `Poiss 0.5` for example)
  The arguments of the constructors correspond to the information we pass to the
  environement.
*)

  (*Next we abstract on a subtype of choiceType. This "small" type of relevant choiceTypes
  should be understood as the collection of
  choiceTypes where the values will be drawn from. This could be
  the singleton {bool} for example, or the set {bool, nat}. *)
  Context (chUniverse : Type) (*the "small" type of relevant choiceTypes*)
  (chElement : chUniverse -> choiceType).

(*
  possible implementation in the case we want to sample things from bool, and nat:

    Record chUniverse : Type := mk_chUniverse
      { abs_chTy :> choiceType ;
        unlock_absChTy : ((abs_chTy = bool_choiceType) + ( abs_chTy = nat_choiceType))%type
      }.

    Definition chElement : chUniverse -> choiceType := fun relChTy =>
      match relChTy with
      |mk_chUniverse T unlock_T =>
      match unlock_T with
      |inl unlock_bool => bool_choiceType
      |inr unlock_nat => nat_choiceType
      end
      end.

  This restriction to a small subtype of choiceType is needed for universe consistency reasons: The
  set of all operations can not be defined by quantifying over all
  choiceTypes (This type is too "big") so we use chUniverse instead. *)
  (*problematic example here: *)
  (* Fail Check @Free (@sigT choiceType _). *)

  (*Our set S, depending over the above probE interface*)

  Definition Prob_ops_collection := @sigT
    chUniverse (fun rchT => probE (chElement rchT)).

  Definition Prob_arities : Prob_ops_collection -> choiceType := fun op =>
    match op with
    | existT envType opp => chElement envType
    end.

End Translation.


Section Unary_free_prob_monad.
  Context (probE : Type -> Type).
  Context (chUniverse : Type) (chElement : chUniverse -> choiceType).
  Context (Hch : forall r : chUniverse, chElement r).


  (*Here I recylce ancient code*)
  Definition rFreePr := @rFree
    (Prob_ops_collection probE chUniverse chElement)
    (Prob_arities probE chUniverse chElement).


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

  Context (probE : Type -> Type).
  Context (chUniverse : Type)
  (chElement : chUniverse -> choiceType).


  Definition rFreeProb_squ_fromProd :=
    product_rmon
      (rFreePr probE chUniverse chElement)
      (rFreePr probE chUniverse chElement).

  (*alias for retro compatibility*)
  Definition rFreeProb_squ := rFreeProb_squ_fromProd.

End Pairs_of_probabilistic_computations.
