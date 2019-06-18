From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Mon.Relational Require Import RelativeMonads RelativeMonadExamples.

Set Primitive Projections.
Set Universe Polymorphism.

Section RelationalProgramLogicFromBimodule.
  Context (M1 M2 : Monad) (M12 := compPair M1 M2).
  Context (W : functor TypeCatSq OrdCat) (rmW : rightModuleStructure M12 W).
  Context (η : natTrans Jprod W) (σ := point_to_homomorphism Jprod rmW η).

  Notation "⊨ c1 ≈ c2 [{ w }]" := (Spr1 (σ ⟨_,_⟩) ⟨c1,c2⟩ ≤ w).

  Check (fun A B (c1 : M1 A) (c2: M2 B) w => ⊨ c1 ≈ c2 [{ w }] ).

  (* Notation "⊢ c1 ≈ c2 [{ w }]" := (Spr1 (σ ⟨_,_⟩) ⟨c1,c2⟩ ≤ w). *)

  Lemma weaken_rule {A B} {c1 : M1 A} {c2 : M2 B} {w w'} :
    ⊨ c1 ≈ c2 [{ w }] -> w ≤ w' -> ⊨ c1 ≈ c2 [{ w' }].
  Proof. move=> ? ? ; estransitivity ; eassumption. Qed.

  Lemma ret_rule {A B} {a : A} {b : B} :
    ⊨ ret a ≈ ret b [{ Spr1 (η ⟨A,B⟩) ⟨a,b⟩ }].
  Proof.
    move: (point_to_homomorphism_to_point Jprod rmW η ⟨A, B⟩ ⟨a,b⟩) => /= ->.
    sreflexivity.
  Qed.

  Definition bindW {A1 A2 B1 B2}
             (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2) (w : dfst (W ⟨A1,A2⟩)) :=
    Spr1 (rm_bind rmW (to_prod f1 f2)) w.

  Lemma bind_act_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {w} :
    ⊨ m1 ≈ m2 [{ w }] -> forall (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2),
      ⊨ bind m1 f1 ≈ bind m2 f2 [{ bindW f1 f2 w }].
  Proof.
    move=> H f1 f2.
    pose (rm_homo _ rmW σ (to_prod f1 f2) ⟨m1, m2⟩) as t.
    move: t => /= ->. unfold bindW.
    apply (Spr2 (rm_bind rmW (to_prod f1 f2)))=> //=.
  Qed.

  Lemma if_rule {A1 A2} {m1: M1 A1} {m2 : M2 A2} {w w'} (b:bool) :
      (if b then ⊨ m1 ≈ m2 [{ w }] else ⊨ m1 ≈ m2 [{ w' }])
      -> ⊨ m1 ≈ m2 [{ if b then w else w' }].
  Proof. destruct b=> //. Qed.

  Lemma nat_rect_rule {A1 A2} {m1: nat -> M1 A1} {m2 : nat -> M2 A2} {w0 wsuc}
        (w := nat_rect (fun=> dfst (W ⟨A1, A2⟩)) w0 wsuc) :
    ⊨ m1 0 ≈ m2 0 [{ w0 }] ->
    (forall n, ⊨ m1 n ≈ m2 n [{ w n }] -> ⊨ m1 (S n) ≈ m2 (S n) [{ wsuc n (w n) }]) ->
    forall n, ⊨ m1 n ≈ m2 n [{ w n }].
  Proof. induction n => //=. apply H0=> //. Qed.

End RelationalProgramLogicFromBimodule.

Section RelationalProgramLogicFromRelativeMonadZero.
  Context (M1 M2 : Monad) (M12 := compPair M1 M2).
  Context (W : RelationalSpecMonad0) `{BindMonotonicRelationalSpecMonad0 W}
          (θ : RelationalEffectObservation0 M1 M2 W).

  Definition semantic_judgement A1 A2 c1 c2 w := Spr1 (θ ⟨A1,A2⟩) ⟨c1,c2⟩ ≤ w.
  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ c1 c2 w).

  Check (fun A B (c1 : M1 A) (c2: M2 B) w => ⊨ c1 ≈ c2 [{ w }] ).

  Import SPropNotations.
  Lemma seq_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W ⟨B1, B2⟩⦆} :
    ⊨ m1 ≈ m2 [{ wm }] -> (forall a1 a2, ⊨ f1 a1 ≈ f2 a2 [{ Spr1 wf ⟨a1, a2⟩ }]) ->
    ⊨ bind m1 f1 ≈ bind m2 f2 [{ Spr1 (relmon_bind W wf) wm }].
  Proof.
    intros Hm Hf.
    rewrite /semantic_judgement.
    move: (rmm_law2 _ _ M12 W θ _ _ (to_prod f1 f2) ⟨m1, m2⟩) => /= ->.
    estransitivity.
    apply (rsm0_bind_monotonic (θ ⟨B1, B2⟩ ∙ fmap Jprod (to_prod f1 f2)) wf) ; move=> [? ?] ; apply Hf.
    eapply (Spr2 (relmon_bind W _) _ _)=> //.
  Qed.

  Lemma weaken_rule2 {A B} {c1 : M1 A} {c2 : M2 B} {w w'} :
    ⊨ c1 ≈ c2 [{ w }] -> w ≤ w' -> ⊨ c1 ≈ c2 [{ w' }].
  Proof. rewrite /semantic_judgement. move=> ? ? ; estransitivity ; eassumption.
  Qed.

  Lemma ret_rule2 {A B} {a : A} {b : B} :
    ⊨ ret a ≈ ret b [{ Spr1 (relmon_unit W ⟨A , B⟩) ⟨a,b⟩ }].
  Proof.
    rewrite /semantic_judgement.
    cbv.
    rewrite <- (rmm_law1 _ _ M12 W θ ⟨A , B⟩).
    sreflexivity.
  Qed.

End RelationalProgramLogicFromRelativeMonadZero.
