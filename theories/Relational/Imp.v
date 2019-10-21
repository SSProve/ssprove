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

  Definition Wun := STCont (S × S).

  Eval cbv in (Wun bool).

  Let R (A : Type) := (@omon_rel Wun A).

  Program Definition ffixun {A} (f : Wun A -> Wun A) : Wun A := ⦑fun post s0 => forall w, R (f w) w -> Spr1 w post s0 ⦒.
  Next Obligation.
    cbv; intuition.
    move: (H0 w H1). apply (Spr2 w x y H a)=> //.
  Qed.

  Eval cbv in (Wun bool).

  Program Definition WungetL {A : Type} (k : S -> Wun A) : Wun A := ⦑fun post s0 => Spr1 (k (nfst s0)) post s0⦒.
  Next Obligation. cbv. intros x y H [sl sr] H'.
                   destruct (k sl). cbv in Spr2. apply (Spr2 x y); intuition.
  Qed.

  Program Definition WungetR {A : Type} (k : S -> Wun A) : Wun A := ⦑fun post s0 => Spr1 (k (nsnd s0)) post s0⦒.
  Next Obligation. cbv.  intros x y H [sl sr] H'. destruct (k sr). cbv in Spr2.  apply (Spr2 x y); intuition. Qed.

  Program Definition WunsetL {A : Type} (s : S) (k : Wun A) : Wun A := ⦑fun post s0 => Spr1 k post (npair s (nsnd s0))⦒.
  Next Obligation. cbv. intros x y H s0 H''. destruct k. cbv in Spr2. apply (Spr2 x y); intuition.  Qed.
  Program Definition WunsetR {A : Type} (s : S) (k : Wun A) : Wun A := ⦑fun post s0 => Spr1 k post (npair (nfst s0) s)⦒.
  Next Obligation. cbv. intros x y H s0 H''. destruct k. cbv in Spr2. apply (Spr2 x y); intuition.  Qed.

  Fixpoint θunL (A : Type) (c: Imp A) {struct c} : Wun A :=
      match c with
      | ImpRet a => @ret Wun _ a
      | ImpGet k => WungetL (fun s => θunL (k s))
      | ImpSet s k => WunsetL s (θunL k)
      | ImpDoWhile body k =>
        let loop (wcont : Wun bool) : Wun bool := @bind Wun _ _ (θunL body) (fun b => if b then wcont else @ret Wun bool false) in
            (@bind Wun _ _ (ffixun loop) (fun _ => (θunL k)))
      end.

  Fixpoint θunR (A : Type) (c: Imp A) {struct c} : Wun A :=
      match c with
      | ImpRet a => @ret Wun _ a
      | ImpGet k => WungetR (fun s => θunR (k s))
      | ImpSet s k => WunsetR s (θunR k)
      | ImpDoWhile body k =>
        let loop (wcont : Wun bool) : Wun bool := @bind Wun _ _ (θunR body) (fun b => if b then wcont else @ret Wun bool false) in
            (@bind Wun _ _ (ffixun loop) (fun _ => (θunR k)))
      end.

  Program Definition θunL_mm : MonadMorphism Imp_monad Wun := @mkMorphism Imp_monad _ θunL _ _.
  Next Obligation.
    move: m.
    refine (fix IH (m: Imp A) {struct m} := _).
    case:m => //= [?|? ?|? ?] ;unfold MonoCont_bind ; apply Ssig_eq; extensionality k=> /=; extensionality s0; rewrite IH //.
  Qed.

  Program Definition θunR_mm : MonadMorphism Imp_monad Wun := @mkMorphism Imp_monad _ θunR _ _.
  Next Obligation.
    move: m.
    refine (fix IH (m: Imp A) {struct m} := _).
    case:m => //= [?|? ?|? ?] ;unfold MonoCont_bind ; apply Ssig_eq; extensionality k=> /=; extensionality s0; rewrite IH //.
  Qed.

  Let M1 := Imp_monad.
  Let M2 := Imp_monad.

  Program Definition θrel := commute_effObs Wun M1 M2 θunL_mm θunR_mm _.
  Next Obligation. admit.
    (* move: c1 c2. *)
    (* refine (fix IH1 (c1: Imp A1) {struct c1} := _). *)
    (* refine (fix IH2 (c2: Imp A2) {struct c2} := _). *)
    (* case c1; case c2. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - intros i i0. *)
    (*   unfold commute. simpl. unfold MonoCont_bind. simpl. *)
  Admitted.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θrel _ _ c1 c2 w).

  Definition omega_seq (A : ordType) := nat -> dfst A.

  Definition omega_chain (A : ordType) := { c : omega_seq A ≫ forall (n : nat), c n ≤ c (n + 1) }.

  Definition upper_seq (A : ordType) (c : omega_seq A) (v : dfst A) : SProp :=
    s∀ n, c n ≤ v.

  Definition sup_seq (A : ordType) (c : omega_seq A) (v : dfst A) : SProp :=
    upper_seq c v s/\ s∀ v', upper_seq c v' -> v ≤ v'.

  Definition apply_seq (A B : ordType) (c : omega_seq A) (f : dfst A -> dfst B) : omega_seq B := fun n => f (c n).


  Definition omega_continuous {A : ordType} (f : dfst A -> dfst A) :=
    s∀ (c : omega_chain A) v, sup_seq (Spr1 c) v -> sup_seq (apply_seq _ (Spr1 c) f) (f v).


  Definition loop (w0 : Wun bool) (wcont : Wun bool) : Wun bool := @bind Wun _ _ w0 (fun b => if b then wcont else @ret Wun bool false).

  Definition preorder_from_type (A : Type) : {R : srelation (Wun A) ≫ PreOrder R}.
    econstructor.
    apply (omon_order Wun A).
  Defined.
  Definition ordertype_from_type (A : Type) : ordType.
    econstructor.
    apply (preorder_from_type A).
  Defined.

  Program Definition bottom_Wun_seq {A : Type} : omega_chain (ordertype_from_type A) := ⦑fun n =>⦑ fun post s0 => sEmpty ⦒ ⦒.
  Next Obligation. cbv; intuition. Qed.
  Next Obligation. sreflexivity. Qed.


End ImpMonad.
