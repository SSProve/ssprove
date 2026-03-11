From Stdlib Require Import ssreflect.
From SSProve.Mon Require Import SPropBase.
From SSProve.Relational Require Import OrderEnrichedCategory.

Import SPropNotations.


(*
In this file we build the composition of two lax relative monad morphisms.
We also prove a pointwise associativity for lax relative monad morphisms.
There is also support for whisekring a pointwise inequality θi ⪷ κi with another relative monad morpihsm.
*)

(*Some auxiliary lemma*)
Section CompVsOrder.

  Context {C : ord_category}.
  Context {a b c : Obj C}.
  Context (f1 f2 : C⦅ a ; b ⦆) (g1 g2 : C⦅ b ; c ⦆).
  Context (Hf : f1 ⪷ f2) (Hg : g1 ⪷ g2).
  Lemma compVsOrder : g1 ∙ f1 ⪷ g2 ∙ f2.
  Proof.
    eapply (Comp_proper C). assumption. assumption.
  Qed.

End CompVsOrder.

(*To compose two lax relative monad morphisms we must first compose their base squares (nat isos)*)
Section BaseSqu.

  Context {C D1 D2 D3 : ord_category}
          {J1 : ord_functor C D1}
          {J2 : ord_functor C D2}
          {J3 : ord_functor C D3}
          (J12 : ord_functor D1 D2)
          (J23 : ord_functor D2 D3)
          (phi12 : natIso J2 (ord_functor_comp J1 J12)) (psi12 := ni_inv phi12)
          (phi23 : natIso J3 (ord_functor_comp J2 J23)) (psi23 := ni_inv phi23).

  Let J13 := ord_functor_comp J12 J23.

  Let J23CircPhi12 := natIso_whisker_right J23 phi12.

  Let associator := natIso_sym (ord_functor_assoc J1 J12 J23).

  Definition phi13 := natIso_comp phi23 (natIso_comp J23CircPhi12 associator).

End BaseSqu.

(*Composition of two lax relative monad morphisms*)
Section Comp.

  Context {C D1 D2 D3 : ord_category}
          {J1 : ord_functor C D1}
          {J2 : ord_functor C D2}
          {J3 : ord_functor C D3}
          (J12 : ord_functor D1 D2)
          (J23 : ord_functor D2 D3)
          (phi12 : natIso J2 (ord_functor_comp J1 J12)) (psi12 := ni_inv phi12)
          (phi23 : natIso J3 (ord_functor_comp J2 J23)) (psi23 := ni_inv phi23)
          (M1 : ord_relativeMonad J1) (M2: ord_relativeMonad J2) (M3: ord_relativeMonad J3).

  Let J13 := ord_functor_comp J12 J23.
  Let phi13 := phi13 J12 J23 phi12 phi23.


  Program Definition rlmm_comp
  (θ12 : relativeLaxMonadMorphism J12 phi12 M1 M2)
  (θ23 : relativeLaxMonadMorphism J23 phi23 M2 M3)
  : relativeLaxMonadMorphism J13 phi13 M1 M3 :=
    mkRelLaxMonMorph _ _ _ _ _ _ _.
  Next Obligation.
    eapply Comp. eapply θ23. eapply ofmap. eapply θ12.
  Defined.
  Next Obligation.
    cbv.
    move: θ12 => [θ12_rlmm_map θ12_rlmm_law1 _].
    move: θ23 => [θ23_rlmm_map θ23_rlmm_law1 _].
    rewrite -{1}ord_cat_law3. rewrite -{1}ord_functor_law2.
    etransitivity. eapply (Comp_proper D3). reflexivity.
    eapply (ofmap_proper D2 D3 J23). apply θ12_rlmm_law1.
    rewrite {1}ord_functor_law2. rewrite {1}ord_cat_law3.
    rewrite [ θ23_rlmm_map A ∙ ( _ ∙ _)]ord_cat_law3.
    eapply compVsOrder.
      rewrite ord_cat_law2. reflexivity.
    apply θ23_rlmm_law1.
  Qed.
  Next Obligation.
    cbv.
    move: θ12 => [θ12_rlmm_map θ12_rlmm_law1 θ12_rlmm_law2].
    move: θ23 => [θ23_rlmm_map θ23_rlmm_law1 θ23_rlmm_law2].
    rewrite -{1}ord_cat_law3. rewrite -{1}ord_functor_law2.
    etransitivity. eapply (Comp_proper D3). reflexivity.
    eapply (ofmap_proper D2 D3 J23). eapply θ12_rlmm_law2.
    rewrite [ofmap J23 (_ ∙ _)]ord_functor_law2.
    rewrite [θ23_rlmm_map B ∙ (_ ∙ _)]ord_cat_law3.
    etransitivity. eapply compVsOrder. reflexivity. eapply θ23_rlmm_law2.
    rewrite [_ ∙ (θ23_rlmm_map A ∙ _)]ord_cat_law3.
    eapply compVsOrder. reflexivity.
    rewrite ord_cat_law1. eapply compVsOrder. reflexivity.
    eapply ord_relmon_bind_proper.
    rewrite [_ ∙ (_ ∙ phi23 A)]ord_cat_law3.
    eapply compVsOrder. reflexivity.
    rewrite -[(θ23_rlmm_map B ∙ _) ∙ _]ord_cat_law3.
    rewrite -[(θ23_rlmm_map B ∙ _) ∙ _]ord_cat_law3.
    eapply compVsOrder. rewrite ord_functor_law2. rewrite ord_functor_law2.
    reflexivity. reflexivity.
  Qed.

End Comp.

(*Pointwise associativity for lax relative monad morphisms*)
Section Assoc.

  Context {I C1 C2 C3 C4: ord_category}
          {J1 : ord_functor I C1}
          {J2 : ord_functor I C2}
          {J3 : ord_functor I C3}
          {J4 : ord_functor I C4}
          {J12 : ord_functor C1 C2}
          {J23 : ord_functor C2 C3}
          {J34 : ord_functor C3 C4}
          {phi12 : natIso J2 (ord_functor_comp J1 J12)} (psi12 := ni_inv phi12)
          {phi23 : natIso J3 (ord_functor_comp J2 J23)} (psi23 := ni_inv phi23)
          {phi34 : natIso J4 (ord_functor_comp J3 J34)} (psi34 := ni_inv phi34)
          {M1 : ord_relativeMonad J1} {M2: ord_relativeMonad J2}
          {M3: ord_relativeMonad J3} {M4 : ord_relativeMonad J4}.

  (*Three consecutive morphisms*)
  Context (θ12 : relativeLaxMonadMorphism J12 phi12 M1 M2)
          (θ23 : relativeLaxMonadMorphism J23 phi23 M2 M3)
          (θ34 : relativeLaxMonadMorphism J34 phi34 M3 M4).

  Let θleft := rlmm_comp _ _ _ _ _ _ _ θ12 θ23. (*θ23 ∘ θ12*)
  Let θright := rlmm_comp _ _ _ _ _ _ _ θ23 θ34.  (*θ34 ∘ θ23 *)
  (*below (θ34 ∘ θ23) ∘ θ12 *)
  Definition left_assoc_rlmm_comp :=
  rlmm_comp _ _ _ _ _ _ _ θ12 θright.
  (*below θ34 ∘ (θ23 ∘ θ12) *)
  Definition right_assoc_rlmm_comp :=
  rlmm_comp _ _ _ _ _ _ _ θleft θ34.

  Lemma rlmm_comp_assoc : forall i : I,
  left_assoc_rlmm_comp i = right_assoc_rlmm_comp i.
  Proof.
    move=> i.
    cbv.
    rewrite -!ord_cat_law3. f_equal.
    rewrite ord_functor_law2. reflexivity.
  Qed.


End Assoc.


(*whisekring ⪷*)
Section Proper_rlmm_comp.
  Notation "β \O α" := (rlmm_comp _ _ _ _ _ _ _ α β) (at level 70).

  Context {I C1 C2 C3: ord_category}
          {J1 : ord_functor I C1}
          {J2 : ord_functor I C2}
          {J3 : ord_functor I C3}
          {J12 : ord_functor C1 C2}
          {J23 : ord_functor C2 C3}
          {phi12 : natIso J2 (ord_functor_comp J1 J12)} (psi12 := ni_inv phi12)
          {phi23 : natIso J3 (ord_functor_comp J2 J23)} (psi23 := ni_inv phi23)
          {M1 : ord_relativeMonad J1} {M2: ord_relativeMonad J2}
          {M3: ord_relativeMonad J3}.

  (*two morphisms θ, κ : M1 -> M2, and two morphisms θ' , κ' : M2 -> M3*)
  Context (θ : relativeLaxMonadMorphism J12 phi12 M1 M2)
          (κ : relativeLaxMonadMorphism J12 phi12 M1 M2)
          (θ' : relativeLaxMonadMorphism J23 phi23 M2 M3)
          (κ' : relativeLaxMonadMorphism J23 phi23 M2 M3).

  (*θ = κ → θ' ∘ θ = θ' ∘ κ*)
  Lemma preeq_rlmm_proper :
  forall i : I, θ i = κ i -> (θ' \O θ) i = (θ' \O κ) i.
  Proof.
    move=> i.
    move=> Heq.
    cbv. rewrite Heq. reflexivity.
  Qed.

  Lemma preeq_rlmm_proper' :
  (forall i : I, θ i = κ i) -> (forall i : I , (θ' \O θ) i = (θ' \O κ) i ).
  Proof.
    move=> Heq. move=> i. move: Heq => /(_ i) Heq.
    cbv. rewrite Heq. reflexivity.
  Qed.

  Lemma posteq_rlmm_proper :
  forall i : I, θ' i = κ' i -> (θ' \O θ) i = (κ' \O θ) i.
  Proof.
    move=> i. cbv.
    move=> Heq. rewrite Heq.
    reflexivity.
  Qed.

  (*θ ⪷1 κ → θ' ∘ θ ⪷1 θ' ∘ κ*)
  Lemma preLeq_rlmm_proper :
  forall i : I, θ i ⪷ κ i -> (θ' \O θ) i ⪷ (θ' \O κ) i.
  Proof.
    cbv. move=> i Hleq.
    apply Comp_proper. reflexivity.
    apply ofmap_proper. assumption.
  Qed.


  Lemma postLeq_rlmm_proper :
  forall i : I, θ' i ⪷ κ' i -> (θ' \O θ) i ⪷ (κ' \O θ) i.
  Proof.
    cbv. move=> i Hleq.
    apply Comp_proper.
      assumption.
      reflexivity.
  Qed.


End Proper_rlmm_comp.


(*a small rewriting lemma for convenience*)
Section PointwiseFormula.
  Notation "β \O α" := (rlmm_comp _ _ _ _ _ _ _ α β) (at level 70).

  Context {I C1 C2 C3: ord_category}
          {J1 : ord_functor I C1}
          {J2 : ord_functor I C2}
          {J3 : ord_functor I C3}
          {J12 : ord_functor C1 C2}
          {J23 : ord_functor C2 C3}
          {phi12 : natIso J2 (ord_functor_comp J1 J12)} (psi12 := ni_inv phi12)
          {phi23 : natIso J3 (ord_functor_comp J2 J23)} (psi23 := ni_inv phi23)
          {M1 : ord_relativeMonad J1} {M2: ord_relativeMonad J2}
          {M3: ord_relativeMonad J3}.


  Context (θ : relativeLaxMonadMorphism J12 phi12 M1 M2)
          (θ' : relativeLaxMonadMorphism J23 phi23 M2 M3).


  Lemma rlmm_comp_pointwise_formula :
  forall i, (θ' \O θ) i = θ' i ∙ ofmap J23 (θ i).
  Proof.
    cbv. reflexivity.
  Qed.


End PointwiseFormula.
