From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Rel.

Set Primitive Projections.
Set Universe Polymorphism.

From Coq Require Import RelationClasses Morphisms.

(* In this file we verify the correctness of the bind rule in the full setting *)

Section RelationalProgramLogicFromRelativeMonad.

  (* The context takes all components of a (full) relational specification monad *)

  (* Basic setup for each side: computational monad, unary specification monad
  and an effect observation relating these *)

  Context (W10 W20 : OrderedMonad).
  Let W1 := ordmonad_to_relmon W10.
  Let W2 := ordmonad_to_relmon W20.

  Context (M1 M2 : Monad)
          (θ10 : MonadMorphism M1 W10) (θ20 : MonadMorphism M2 W20).

  Let M12 := compPair M1 M2.
  Let θ1 := mmorph_to_rmmorph θ10.
  Let θ2 := mmorph_to_rmmorph θ20.

  Context (Wrel : rsm_components W1 W2).
  Notation W0 := (rsmc_carrier _ _ Wrel).
  Notation η := (rsmc_return _ _ Wrel).
  Notation actW := (rsmc_act _ _ Wrel).

  Import SPropNotations.

  (* We show that we can define the sur-approximation of this coq-development from that data *)

  Program Definition W : preRelationalSpecMonad :=
    mkOrdRelativeMonad (fun A => ⟨⟨W1 (nfst A), W2 (nsnd A)⟩, W0 A⟩)
                    (fun A => ⟨⟨ord_relmon_unit W1 (nfst A), ord_relmon_unit W2 (nsnd A)⟩,
                           η A⟩)
                    (fun A B f =>
                       ⟨⟨ord_relmon_bind W1 (nfst (nfst f)),
                         ord_relmon_bind W2 (nsnd (nfst f))⟩,
                       actW(nfst (nfst f)) (nsnd (nfst f)) (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation.
    cbv ; intuition.
    1-2:apply omon_bind; [sreflexivity| cbv=> ? ; auto].
    apply: rsmc_act_proper=> ?; [apply p0| apply q0| apply q].
  Qed.
  Next Obligation.
    f_equal ; [f_equal|]; rewrite /actW ?rsmc_law1 //;
      apply Ssig_eq ;apply: funext=> a /=; apply: monad_law2.
  Qed.
  Next Obligation.
    move: f => [[f1 f2] frel].
    f_equal ; [f_equal|] ; apply Ssig_eq.
    1-2:apply: funext=> a /=; apply: monad_law1.
    apply (f_equal Spr1). apply: rsmc_law2.
  Qed.
  Next Obligation.
    f_equal ; [f_equal|] ; apply Ssig_eq.
    1-2: apply: funext=> a /=; rewrite /bind monad_law3 //.
    apply (f_equal Spr1). apply: rsmc_law3.
  Qed.


  Context (θrc : reo_components θ1 θ2 Wrel).
  Notation θW := (@reoc_carrier _ _ _ _ _ _ _ θrc ⟨_,_⟩).


  Program Definition θ : preRelationalEffectObservation M1 M2 W :=
    mkpreREO M1 M2 W (fun A => ⟨⟨θ1 (nfst A), θ2 (nsnd A)⟩, θW⟩) _ _.
  Next Obligation.
    f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1).
    apply (rmm_law1 _ _ _ _ θ1).
    apply (rmm_law1 _ _ _ _ θ2).
    apply: reoc_law1.
  Qed.
  Next Obligation.
    f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1).
    apply (rmm_law2 _ _ _ _ θ1).
    apply (rmm_law2 _ _ _ _ θ2).
    apply (reoc_law2 θ1 θ2).
  Qed.


  Import RelNotations.

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    ((forall γ1 : πl Γ, (θ1 _)∙1 (c1 γ1) ≤ Spr1 w1 γ1) s/\
    (forall γ2 : πr Γ, (θ2 _)∙1 (c2 γ2) ≤ Spr1 w2 γ2) s/\
    (forall γ : ⟬Γ⟭, θW∙1 ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ Spr1 w (dfst γ)))
      (at level 85).

  Notation "⋅⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    (Hi unit ⊫ (fun=> c1) ≈ (fun=> c2) [{ @OrdCat_cst (discr unit) _ w1,
                                    @OrdCat_cst (discr unit) _ w2,
                                    @OrdCat_cst (discr (unit × unit)) _ w}]).

  Check (fun A B (c1 : M1 A) (c2: M2 B) (w1:dfst (W1 A)) (w2:dfst (W2 B)) (w3:dfst (W0 ⟨A,B⟩)) => ⋅⊫ c1 ≈ c2 [{ w1, w2, w3 }] ).

  (* And we prove the rule for binding computations *)

  Import SPropNotations.
  Lemma full_seq_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm1 wm2 wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf1 : OrdCat⦅discr A1; W1 B1⦆} {wf2:OrdCat⦅discr A2;W2 B2⦆}
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W0 ⟨B1, B2⟩⦆} :
    ⋅⊫ m1 ≈ m2 [{ wm1, wm2, wm }] ->
    (⦑A1,A2|fun=>fun=>unit|TyRel⦒ ⊫ f1 ≈ f2 [{ wf1, wf2,  wf }]) ->
    ⋅⊫ bind m1 f1 ≈ bind m2 f2 [{ wm1 ≫= wf1,
                                  wm2 ≫= wf2,
                                  (actW wf1 wf2 wf)∙1 wm }].
  Proof.
    intros [[Hm1 Hm2] Hm] [[Hf1 Hf2] Hf].
    move: (rmm_law2 _ _ M12 W θ _ _ (to_prod f1 f2))=> /= [[H1 H2] H12].
    intuition.
    move: (f_equal (fun h => h m1) H1)=> /= ->.
    apply omon_bind=> //; apply (Hm1 tt).
    move: (f_equal (fun h => h m2) H2)=> /= ->.
    apply omon_bind=> //; apply (Hm2 tt).
    move: (f_equal (fun h => h ⟨m1, m2⟩) H12) => /= -> //=.
    estransitivity.
    simpl in Hf1.
    apply: rsmc_act_proper.
    move=> ? ; apply Hf1.
    move=> ? ; apply Hf2.
    move=> [? ?] /=; eapply (Hf ⦑ _ , _ | tt⦒).
    eapply (Spr2 (actW _ _ _))=> //.
    apply (Hm ⦑tt,tt|I⦒).
  Qed.

  Import RelNotations.

  (* Definition bindStrongRSM {Γ A1 A2 B1 B2} *)
  (*            (wm1 : πl Γ -> W1 A1) *)
  (*            (wm2 : πr Γ -> W2 A2) *)
  (*            (wmrel : ⟬Γ⟭ -> W A1 A2) *)
  (*            (wf1 : πl Γ × A1 -> W1 B1) *)
  (*            (wf2 : πr Γ × A2 -> W2 B2) *)
  (*            (wfrel : ⟬extends Γ A1 A2⟭ -> W B1 B2) *)
  (* : ⟬Γ⟭ -> Wrel B1 B2 *)


End RelationalProgramLogicFromRelativeMonad.
