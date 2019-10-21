From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import RelativeMonads OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

Set Primitive Projections.
Set Universe Polymorphism.

Section ImpMonad.
  Context (S:Type).

  Set Implicit Arguments.
  Inductive Imp (A:Type) :=
  | ImpRet : A -> Imp A
  | ImpGet : (S -> Imp A) -> Imp A
  | ImpSet : S -> Imp A -> Imp A
  | ImpDoWhile : Imp bool -> Imp A -> Imp A.

  Fixpoint Imp_bind {A B : Type} (m : Imp A) (f : A -> Imp B) {struct m} : Imp B :=
    match m with
    | ImpRet v => f v
    | ImpGet k => ImpGet (fun s => Imp_bind (k s) f)
    | ImpSet s k => ImpSet s (Imp_bind k f)
    | ImpDoWhile c k => ImpDoWhile c (Imp_bind k f)
    end.

  Import FunctionalExtensionality.
  Program Definition Imp_monad : Monad := @mkMonad Imp ImpRet (@Imp_bind) _ _ _.
  Next Obligation.
    move: c.
    refine (fix IH (c: Imp A) {struct c} := _).
    case:c => //= [?|? ?|? ?]; f_equal; first extensionality s; apply: IH.
  Qed.
  Next Obligation.
    move: c.
    refine (fix IH (c: Imp A) {struct c} := _).
    case:c => //= [?|? ?|? ?]; f_equal; first extensionality s; apply: IH.
  Qed.


  Definition WrelSt := ordmonad_to_relspecmon0 (STCont (S×S)).

  Let W A := dfst (WrelSt A).

  Import SPropNotations.
  Program Definition ffix {A} (f : W A -> W A) : W A := ⦑fun post => fun s0 => forall w, f w ≤ w -> Spr1 w post s0 ⦒.
  Next Obligation.
    cbv; intuition.
    move: (H0 w H1). apply (Spr2 w x y H a)=> //.
  Qed.

  Let one : Type := unit.
  Let bool : Type := bool.

  Definition do_while (body : Imp bool) : Imp unit := ImpDoWhile body (ImpRet tt).

  Program Definition OrdCat_prodlift {A1 A2 B} (f : A1 -> A2 -> dfst B)
    : OrdCat⦅Jprod ⟨A1,A2⟩; B⦆ :=
    Sexists _ (fun '(npair a1 a2) => f a1 a2) _.
  Next Obligation. intros [? ?] [? ?] eq; inversion eq. sreflexivity. Qed.

  Eval cbv in W ⟨one,one⟩.

  Definition Wun := STCont S.

  Eval cbv in (Wun bool).

  Let R := (@omon_rel Wun).

  Program Definition ffixun {A} (f : Wun A -> Wun A) : Wun A := ⦑fun post s0 => forall w, R (f w) w -> Spr1 w post s0 ⦒.
  Next Obligation.
    cbv; intuition.
    move: (H0 w H1). apply (Spr2 w x y H a)=> //.
  Qed.

  Eval cbv in (Wun bool).

  Program Definition Wunget {A : Type} (k : S -> Wun A) : Wun A := ⦑fun post s0 => Spr1 (k s0) post s0⦒.
  Next Obligation. cbv.  intros x y H s H'. destruct (k s). cbv in Spr2.  apply (Spr2 x y); intuition. Qed.

  Program Definition Wunset {A : Type} (s : S) (k : Wun A) : Wun A := ⦑fun post _ => Spr1 k post s⦒.
  Next Obligation. cbv. intros x y H s0 H''. destruct k. cbv in Spr2. apply (Spr2 x y); intuition.  Qed.

  Fixpoint θun (A : Type) (c: Imp A) {struct c} : Wun A :=
      match c with
      | ImpRet a => @ret Wun _ a
      | ImpGet k => Wunget (fun s => θun (k s))
      | ImpSet s k => Wunset s (θun k)
      | ImpDoWhile body k =>
        let loop (wcont : Wun bool) : Wun bool := @bind Wun _ _ (θun body) (fun b => if b then wcont else @ret Wun bool false) in
            (@bind Wun _ _ (ffixun loop) (fun _ => (θun k)))
      end.

  Program Definition θun_mm : MonadMorphism Imp_monad Wun := @mkMorphism Imp_monad _ θun _ _.
  Next Obligation.
    move: m.
    refine (fix IH (m: Imp A) {struct m} := _).
    case:m => //= [?|? ?|? ?] ;unfold MonoCont_bind ; apply Ssig_eq; extensionality k=> /=; extensionality s0; rewrite IH //.
  Qed.

  Let M1 := Imp_monad.
  Let M2 := Imp_monad.

  Program Definition θrel := commute_effObs Wun M1 M2 θun_mm θun_mm _.
  Next Obligation. admit. Admitted.

End ImpMonad.
