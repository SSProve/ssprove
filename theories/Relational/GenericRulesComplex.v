From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Mon.Relational Require Import RelativeMonads RelativeMonadExamples.

Set Primitive Projections.
Set Universe Polymorphism.

From Coq Require Import RelationClasses Morphisms.

Section RelationalProgramLogicFromRelativeMonad.
  Context (M1 M2 : Monad) (M12 := compPair M1 M2).
  Context (W10 W20 : OrderedMonad)
          (W1 := ordmonad_to_relmon W10)
          (W2 := ordmonad_to_relmon W20).
  Context (θ10 : MonadMorphism M1 W10) (θ20 : MonadMorphism M2 W20)
          (θ1 := mmorph_to_rmmorph θ10) (θ2 := mmorph_to_rmmorph θ20).

  Context (W0 : TypeCatSq -> OrdCat) (η : forall A, OrdCat⦅Jprod A;W0 A⦆)
          (actW : forall {A1 A2 B1 B2},
              OrdCat⦅discr A1;W1 B1⦆ ->
              OrdCat⦅discr A2;W2 B2⦆ ->
              OrdCat⦅Jprod ⟨A1,A2⟩; W0 ⟨B1,B2⟩⦆ ->
              OrdCat⦅W0 ⟨A1,A2⟩; W0 ⟨B1,B2⟩⦆).
  Context (actW_proper : forall {A1 A2 B1 B2},
              Proper (sim _ ==> sim _ ==> sim _ ==> sim _) (@actW A1 A2 B1 B2)).
  Context (HW_law1 : forall A1 A2, actW _ _ _ _
                                 (relmon_unit W1 A1)
                                 (relmon_unit W2 A2)
                                 (η ⟨A1,A2⟩) ∼ Id _).
  Context (HW_law2 : forall A1 A2 B1 B2 f1 f2 f,
              actW A1 A2 B1 B2 f1 f2 f ∙ η _ ∼ f).
  Context (HW_law3 : forall A1 A2 B1 B2 C1 C2 f1 f2 f g1 g2 g,
              actW A1 A2 C1 C2
                   (relmon_bind W1 g1 ∙ f1)
                   (relmon_bind W2 g2 ∙ f2)
                   (actW B1 B2 C1 C2 g1 g2 g ∙ f)
                   ∼ (actW B1 B2 C1 C2 g1 g2 g) ∙ (actW A1 A2 B1 B2 f1 f2 f)).
  Context (actW_mon : forall A1 A2 B1 B2 f1 f1' f2 f2' f f',
              f1 ≼ f1' -> f2 ≼ f2' -> f ≼ f' ->
              actW A1 A2 B1 B2 f1 f2 f ≼ actW A1 A2 B1 B2 f1' f2' f').
  Import SPropNotations.

  Program Definition W : RelationalSpecMonad :=
    mkRelativeMonad (fun A => ⟨⟨W1 (nfst A), W2 (nsnd A)⟩, W0 A⟩)
                    (fun A => ⟨⟨relmon_unit W1 (nfst A), relmon_unit W2 (nsnd A)⟩,
                           η A⟩)
                    (fun A B f =>
                       ⟨⟨relmon_bind W1 (nfst (nfst f)),
                         relmon_bind W2 (nsnd (nfst f))⟩,
                       actW _ _ _ _ (nfst (nfst f)) (nsnd (nfst f)) (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation.
    cbv ; intuition.
    rewrite (funext H)=> //.
    rewrite (funext H2)=> //.
    congr (Spr1 (actW _ _ _ _ _ _ _) _); apply Ssig_eq ; apply funext=> //.
  Qed.
  Next Obligation.
    intuition; [refine (relmon_law1 W1 _ _)
               |refine (relmon_law1 W2 _ _)
               |apply HW_law1].
  Qed.
  Next Obligation.
    intuition; [refine (relmon_law2 W1 _ _ _ _)
               |refine (relmon_law2 W2 _ _ _ _)
               |apply HW_law2].
  Qed.
  Next Obligation.
    intuition; [refine (relmon_law3 W1 _ _ _ _ _ _)
               |refine (relmon_law3 W2 _ _ _ _ _ _)
               |apply HW_law3].
  Qed.

  Context (θW : forall {A}, OrdCat⦅Jprod (M12 A);W0 A⦆).
  Context (HθW_law1 : forall {A},
              θW _ ∙ fmap Jprod (relmon_unit M12 A)
                 ∼ η A).
  Context (HθW_law2 : forall {A B} (f:TypeCatSq⦅A;M12 B⦆),
              θW _ ∙ fmap Jprod (relmon_bind M12 f)
                 ∼ actW _ _ _ _
                         (θ1 _ ∙ fmap discr (nfst f))
                         (θ2 _ ∙ fmap discr (nsnd f))
                         (θW _ ∙ fmap Jprod f) ∙ θW _).

  Program Definition θ : RelationalEffectObservation M1 M2 W :=
    mkRelMonMorph _ _ _ _ (fun A => ⟨⟨θ1 (nfst A), θ2 (nsnd A)⟩, θW A⟩) _ _.
  Next Obligation.
    intuition; [apply (rmm_law1 _ _ _ _ θ1)
               |apply (rmm_law1 _ _ _ _ θ2)
               |apply HθW_law1].
  Qed.
  Next Obligation.
    intuition; [apply (rmm_law2 _ _ _ _ θ1) |apply (rmm_law2 _ _ _ _ θ2)|].
    move: (HθW_law2 _ _ ⟨nfst, nsnd⟩ ⟨nfst0, nsnd0⟩)=> /= -> //.
  Qed.

  (* Context (W : RelationalSpecMonad) `{BindMonotonicRelationalSpecMonad W} *)
  (*         (θ : RelationalEffectObservation M1 M2 W). *)

  (* Import EqNotations. *)
  (* Context (HeqW1 : forall A1 A2, nfst (nfst (W ⟨A1,A2⟩)) = W1 A1) *)
  (*         (Heq_unitW1 : forall A1 A2, nfst (nfst (relmon_unit W ⟨A1, A2⟩)) ∼ rew <- (HeqW1 A1 A2) in relmon_unit W1 A1) *)
  (*         (Heq_bindW1 : forall A1 A2 B1 B2,) *)
  (* . *)
  (*         (HeqW2 : forall A1 A2, nsnd (nfst W ⟨A1,A2⟩) = W1 A2) *)


  (* Notation "⊨ c1 ≈ c2 [{ w1 , w2 , w }]" := *)
  (*   (Spr1 (θ1 _) c1 ≤ w1 s/\ Spr1 (θ2 _) c2 ≤ w2 s/\ Spr1 (θW ⟨_,_⟩) ⟨c1,c2⟩ ≤ w). *)

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    ((forall γ1 : nfst Γ, Spr1 (θ1 _) (c1 γ1) ≤ Spr1 w1 γ1) s/\
    (forall γ2 : nsnd Γ, Spr1 (θ2 _) (c2 γ2) ≤ Spr1 w2 γ2) s/\
    (forall γ : typeCat_prod Γ, Spr1 (θW ⟨_,_⟩) ⟨c1 (nfst γ), c2 (nsnd γ)⟩ ≤ Spr1 w γ)) (at level 85).

  Program Definition OrdCat_cst {A B} (b:dfst B) : OrdCat⦅A; B⦆ := ⦑fun=> b⦒.
  Next Obligation. cbv; intuition. Qed.

  Notation "⋅⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    (⟨unit,unit⟩ ⊫ (fun=> c1) ≈ (fun=> c2) [{ @OrdCat_cst (discr unit) _ w1,
                                        @OrdCat_cst (discr unit) _ w2,
                                        @OrdCat_cst (discr (unit × unit)) _ w}]).

  Check (fun A B (c1 : M1 A) (c2: M2 B) (w1:dfst (W1 A)) (w2:dfst (W2 B)) (w3:dfst (W0 ⟨A,B⟩)) => ⋅⊫ c1 ≈ c2 [{ w1, w2, w3 }] ).

  Import SPropNotations.
  Lemma full_seq_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm1 wm2 wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf1 : OrdCat⦅discr A1; W1 B1⦆} {wf2:OrdCat⦅discr A2;W2 B2⦆}
        (* {wf1 : A1 -> W1 B1} {wf2 : A2 -> W2 B2} *)
        (* {wf : A1 × A2 -> W ⟨B1, B2⟩} *)
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W0 ⟨B1, B2⟩⦆} :
    ⋅⊫ m1 ≈ m2 [{ wm1, wm2, wm }] ->
    (⟨A1,A2⟩ ⊫ f1 ≈ f2 [{ wf1, wf2,  wf }]) ->
    ⋅⊫ bind m1 f1 ≈ bind m2 f2 [{ Spr1 (relmon_bind W1 wf1) wm1,
                                  Spr1 (relmon_bind W2 wf2) wm2,
                                  Spr1 (actW _ _ _ _ wf1 wf2 wf) wm }].
  Proof.
    intros [[Hm1 Hm2] Hm] [[Hf1 Hf2] Hf].
    move: (rmm_law2 _ _ M12 W θ _ _ (to_prod f1 f2)) => /= [[-> ->] H12] ; intuition.
    apply omon_bind=> //; apply (Hm1 tt).
    apply omon_bind=> //; apply (Hm2 tt).
    rewrite (H12 ⟨m1, m2⟩).

    estransitivity.
    simpl in Hf1.
    unfold ordcattr_hom_ord in Hf1.
    refine (actW_mon A1 A2 B1 B2
                    (θ1 _ ∙ fmap discr f1) wf1
                    (θ2 _ ∙ fmap discr f2) wf2
                    (θW _ ∙ fmap Jprod (to_prod f1 f2)) wf
                    _ _ _ _).
    move=> ? ; apply Hf1.
    move=> ? ; apply Hf2.
    move=> ? ; apply Hf.
    eapply (Spr2 (actW _ _ _ _ _ _ _))=> //.
    apply (Hm ⟨tt,tt⟩).
  Qed.
End RelationalProgramLogicFromRelativeMonad.