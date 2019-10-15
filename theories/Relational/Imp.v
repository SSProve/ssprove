From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import RelativeMonads RelativeMonadExamples GenericRulesSimple.

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

  (* Program Definition OrdCat_prodlift {A1 A2 B} (f : A1 -> A2 -> dfst B) *)
  (*   : OrdCat⦅Jprod ⟨A1,A2⟩; B⦆ := *)
  (*   Sexists _ (fun '(npair a1 a2) => f a1 a2) _. *)
  (* Next Obligation. induction H; sreflexivity. Qed. *)

  (* Fixpoint θ1 {A} (c: Imp A) {struct c} : W ⟨A,one⟩ := *)
  (*   fun s0 => *)
  (*     match c with *)
  (*     | ImpRet a => Spr1 (relmon_unit WrelSt ⟨A,one⟩) ⟨a,tt⟩ s0 *)
  (*     | ImpGet k => θ1 (k (nfst s0)) s0 *)
  (*     | ImpSet s k => θ1 k ⟨s, nsnd s0⟩ *)
  (*     | ImpDoWhile body k => *)
  (*       let loop (wcont : W ⟨bool,one⟩) : W ⟨bool,one⟩ := *)
  (*           let cont := *)
  (*               OrdCat_prodlift (fun b 'tt => *)
  (*                              if b then wcont *)
  (*                              else Spr1 (relmon_unit WrelSt ⟨bool,one⟩) ⟨false,tt⟩ *)
  (*                           ) in *)
  (*           Spr1 (relmon_bind WrelSt cont) (θ1 body) *)
  (*       in *)
  (*       Spr1 (relmon_bind WrelSt (OrdCat_cst (θ1 k))) (ffix loop) s0 *)
  (*     end. *)

  (* Fixpoint θ2 {A} (c: Imp A) {struct c} : W ⟨one, A⟩ := *)
  (*   fun s0 => *)
  (*     match c with *)
  (*     | ImpRet a => Spr1 (relmon_unit WrelSt ⟨one,A⟩) ⟨tt, a⟩ s0 *)
  (*     | ImpGet k => θ2 (k (nsnd s0)) s0 *)
  (*     | ImpSet s k => θ2 k ⟨nfst s0, s⟩ *)
  (*     | ImpDoWhile body k => *)
  (*       let loop (wcont : W ⟨one,bool⟩) : W ⟨one,bool⟩ := *)
  (*           let cont := *)
  (*               OrdCat_prodlift (fun 'tt b => *)
  (*                              if b then wcont *)
  (*                              else Spr1 (relmon_unit WrelSt ⟨one,bool⟩) ⟨tt,false⟩ *)
  (*                           ) in *)
  (*           Spr1 (relmon_bind WrelSt cont) (θ2 body) *)
  (*       in *)
  (*       Spr1 (relmon_bind WrelSt (OrdCat_cst (θ2 k))) (ffix loop) s0 *)
  (*     end. *)

  (* Let rret {A1 A2} (a1:A1) (a2:A2) : W ⟨A1,A2⟩ :=  *)
  (*   Spr1 (relmon_unit WrelSt ⟨A1,A2⟩) ⟨a1, a2⟩. *)

  (* Let rbind {A B} : W A -> (nfst A -> nsnd A -> W B) -> W B := *)
  (*   fun wm wf => Spr1 (relmon_bind WrelSt (OrdCat_prodlift wf)) wm. *)

End ImpMonad.
