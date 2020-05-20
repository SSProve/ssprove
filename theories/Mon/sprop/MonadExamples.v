From Coq Require Import ssreflect ssrfun ssrbool List.
From Mon Require Export Base.
From Coq Require Import Relation_Definitions Morphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.


(* The identity monad *)
Program Definition Identity : Monad :=
  @mkMonad (fun X => X) (fun _ x => x) (fun X Y x f => f x) _ _ _.

(* The identity monad has a monad morphism to any other monad *)
Section IdentityInitial.
  Context (M:Monad).

  Program Definition ret_mmorph : MonadMorphism Identity M :=
    @mkMorphism _ _ (@ret M) _ _.
  Next Obligation. rewrite /bind monad_law1 //. Qed.
  (* We just prove the existence, not the unicity... *)

End IdentityInitial.


Section State.
  Context (S: Type).

  Program Definition St : Monad :=
    @mkMonad (fun X => S -> X × S) (fun A a s => ⟨a, s⟩)
             (fun A B m f s => let ms := m s in f (nfst ms) (nsnd ms))
             _ _ _.
  Definition get : St S := fun s => ⟨s, s⟩.
  Definition put (s:S) : St unit := fun s0 => ⟨tt, s⟩.
End State.

Section Update.
  Context (M:monoid) (X:monoid_action M).

  Definition UpdFromLaws pf1 pf2 pf3 : Monad :=
    @mkMonad (fun A => X -> A × M) (fun A a x => ⟨a, e M⟩)
             (fun A B m f x => let mx := m x in
                            let fx := f (nfst mx) (nsnd mx ⧕ x) in
                            ⟨nfst fx, nsnd fx ⋅ nsnd mx⟩) pf1 pf2 pf3.
  Import FunctionalExtensionality.
  Program Definition Upd : Monad :=
    UpdFromLaws _ _ _.
  Next Obligation.
    extensionality x ; rewrite monact_unit monoid_law2 //.
  Qed.
  Next Obligation.
    extensionality x; rewrite monoid_law1 //.
  Qed.
  Next Obligation.
    extensionality x. rewrite - !monact_mult !monoid_law3 //. 
  Qed.
End Update.


Section FreeMonad.

  (* A signature where S is the type of operations and P describes the
     arity of each operations *)
  Context (S : Type) (P : S  -> Type).

  Inductive FreeF A : Type :=
  | retFree : A -> FreeF A
  | opr     : forall s, (P s -> FreeF A) -> FreeF A.

  Arguments opr [A] _ _.

  Fixpoint bindFree A B (c : FreeF A) (f : A -> FreeF B) : FreeF B :=
    match c with
    | retFree a => f a
    | opr s k   => opr s (fun p => bindFree (k p) f)
    end.

  Import FunctionalExtensionality.
  Program Definition Free : Monad :=
    @mkMonad FreeF retFree bindFree _ _ _.
  Next Obligation.
    elim c => //= ? ? IH ; f_equal ; extensionality p ; apply IH.
  Qed.
  Next Obligation.
    elim c => //= ? ? IH ; f_equal ; extensionality p ; apply IH.
  Qed.

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
End FreeMonad.


Section Partiality.
  Inductive DivS := Omega.
  Definition DivAr : DivS -> Type := fun 'Omega => False.

  Definition Div := @Free DivS DivAr.
  Definition Ω : Div False := op _ Omega.
End Partiality.

Section Exceptions.
  Context (E:Type).

  Inductive ExnS := Raise of E.
  Definition ExnAr : ExnS -> Type := fun '(Raise _) => False.

  Definition Exn := @Free ExnS ExnAr.
  Definition raise : E -> Exn False := fun e => op _ (Raise e).
  Definition catch {A} (m : Exn A) (merr : E -> Exn A) : Exn A :=
    match m with
    | retFree a => m
    | @opr _ _ _ (Raise e) _ => merr e
    end.
End Exceptions.

Section NonDeterminismSet.
  Import SPropNotations FunctionalExtensionality SPropAxioms.

  Program Definition NDSet : Monad :=
    @mkMonad (fun X => X -> Prop)
             (fun X x => fun x' => x ≡ x')
             (fun X Y c f => fun y => s∃ x, c x s/\ f x y) _ _ _.
  Next Obligation.
    extensionality y; apply sprop_ext; do 2 split.
    + intros [x [eq H]]; induction eq=> //.
    + intro; exists a; intuition. compute. intuition.
  Qed.
  Next Obligation.
    extensionality y; apply sprop_ext; do 2 split.
    + intros [x [H eq]]. induction eq=> //.
    + intro. exists y. intuition. compute. intuition.
  Qed.
  Next Obligation.
    extensionality y; apply sprop_ext; do 2 split.
    + intros [b [[a [H1 H2]] H3]].
      eexists ; split ; [|eexists;split]; eassumption.
    + intros [a [H1 [b [H2 H3]]]].
      eexists ; split ; [eexists;split|]; eassumption.
  Qed.

  Definition pick_set : NDSet bool := fun b => True.
End NonDeterminismSet.

Section NonDeterminismList.

  Lemma concat_map_nil : forall A (l : list A),
    concat (List.map (fun x => x :: nil) l) = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  Qed.

  Program Definition ListM : Monad :=
    @mkMonad (fun A => list A)
             (fun A a => a :: nil)
             (fun A B m f => concat (List.map f m)) _ _ _.
  Next Obligation. apply app_nil_r. Qed.
  Next Obligation. apply concat_map_nil. Qed.
  Next Obligation.
    induction c=> //=.
    rewrite map_app concat_app IHc //.
  Qed.

  Definition choose {A} (l : list A) : ListM A := l.
  Definition pick : ListM bool := true :: false :: nil.

End NonDeterminismList.

Section IO.
  Context (Inp Oup : Type).

  Inductive IOS : Type := Read : IOS | Write : Oup -> IOS.
  Definition IOAr (op : IOS) : Type :=
    match op with
    | Read => Inp
    | Write _ => unit
    end.

  Definition IO := @Free IOS IOAr. 

  Definition read : IO Inp := op _ Read. 
  Definition write (o:Oup) : IO unit := op _ (Write o).
End IO.
