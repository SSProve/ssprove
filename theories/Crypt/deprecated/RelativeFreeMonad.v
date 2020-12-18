From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase SRelationClasses SMorphisms SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
From mathcomp Require Import all_ssreflect all_algebra reals distr.

Import SPropNotations.


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

Section BaseFunctor.
(*the base functor for or relative version of the free monad*)
  Program Definition choice_incl := @mkOrdFunctor ord_choiceType TypeCat
    (fun (A:ord_choiceType) => A)
    (fun (A B : ord_choiceType) f => f)
    _ _ _.
  Next Obligation. cbv ; intuition. Qed.

End BaseFunctor.

Section RelativeFreeMonad.
(* A signature where S is the type of operations and P describes the
     arity of each operations *)
  Context (S : Type) (P : S  -> Type).


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

  Import SPropAxioms. Import FunctionalExtensionality.
  Program Definition rFree : ord_relativeMonad choice_incl :=
    @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl rFreeF _ _ _ _ _ _.
  Next Obligation. constructor. assumption. Defined.
  Next Obligation. exact (bindrFree X0 X). Defined.
  Next Obligation.
    cbv ; intuition. f_sEqual. reflexivity.
    apply funext_sprop. assumption.
  Qed.
  Next Obligation.
    apply functional_extensionality.
    intro c. elim: c.
      simpl. reflexivity.
    intros s ar IH. simpl. f_equal. apply functional_extensionality.
    assumption.
  Qed.
  Next Obligation.
    apply functional_extensionality. intro c. induction c.
      simpl. reflexivity.
    simpl. f_equal. apply functional_extensionality. intro p.
    eapply H.
  Qed.

(*
we could adapt the following user friendly stuff in the future
  Definition op (s : S) : Free (P s) :=
    opr s (@retFree _).

  Definition trace := list { s : S & P s }.

  Program Definition from_free (M:Monad) (f:forall s, M (P s))
    : MonadMorphism Free M :=
    @mkMorphism _ _
                (fix from_free A (m:Free A) {struct m} :=
                  match m return M A with
                  | retFree a => ret a
                  | opr s k => bind (f s) (fun x => from_free A (k x))
                  end
               ) _ _.
  Next Obligation.
    induction m=> //=.
    rewrite /bind monad_law1 //.
    rewrite /bind monad_law3.
    f_equal. extensionality a. apply H.
  Qed.
*)
End RelativeFreeMonad.
