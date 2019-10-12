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
  Context (M1 M2 : Monad) (W10 W20 : OrderedMonad)
          (θ10 : MonadMorphism M1 W10) (θ20 : MonadMorphism M2 W20).

  Let M12 := compPair M1 M2.
  Let W1 := ordmonad_to_relmon W10.
  Let W2 := ordmonad_to_relmon W20.
  Let θ1 := mmorph_to_rmmorph θ10.
  Let θ2 := mmorph_to_rmmorph θ20.


  (* Now, we want a relational lifting of W1 × W2 *)
  Context (W0 : TypeCatSq -> OrdCat) (η : forall A, OrdCat⦅Jprod A;W0 A⦆)
          (actW : forall {A1 A2 B1 B2},
              OrdCat⦅discr A1;W1 B1⦆ ->
              OrdCat⦅discr A2;W2 B2⦆ ->
              OrdCat⦅Jprod ⟨A1,A2⟩; W0 ⟨B1,B2⟩⦆ ->
              OrdCat⦅W0 ⟨A1,A2⟩; W0 ⟨B1,B2⟩⦆).
  Context (actW_proper : forall {A1 A2 B1 B2},
              SProper (ord_cat_le _ s==> ord_cat_le _ s==> ord_cat_le _ s==> ord_cat_le _) (@actW A1 A2 B1 B2)).
  Context (HW_law1 : forall A1 A2, actW _ _ _ _
                                 (ord_relmon_unit W1 A1)
                                 (ord_relmon_unit W2 A2)
                                 (η ⟨A1,A2⟩) = Id _).
  Context (HW_law2 : forall A1 A2 B1 B2 f1 f2 f,
              actW A1 A2 B1 B2 f1 f2 f ∙ η _ = f).
  Context (HW_law3 : forall A1 A2 B1 B2 C1 C2 f1 f2 f g1 g2 g,
              actW A1 A2 C1 C2
                   (ord_relmon_bind W1 g1 ∙ f1)
                   (ord_relmon_bind W2 g2 ∙ f2)
                   (actW B1 B2 C1 C2 g1 g2 g ∙ f)
                   = (actW B1 B2 C1 C2 g1 g2 g) ∙ (actW A1 A2 B1 B2 f1 f2 f)).
  Context (actW_mon : forall A1 A2 B1 B2 f1 f1' f2 f2' f f',
              f1 ⪷ f1' -> f2 ⪷ f2' -> f ⪷ f' ->
              actW A1 A2 B1 B2 f1 f2 f ⪷ actW A1 A2 B1 B2 f1' f2' f').
  Import SPropNotations.

  (* We show that we can define the sur-approximation of this coq-development from that data *)

  Program Definition W : preRelationalSpecMonad :=
    mkOrdRelativeMonad (fun A => ⟨⟨W1 (nfst A), W2 (nsnd A)⟩, W0 A⟩)
                    (fun A => ⟨⟨ord_relmon_unit W1 (nfst A), ord_relmon_unit W2 (nsnd A)⟩,
                           η A⟩)
                    (fun A B f =>
                       ⟨⟨ord_relmon_bind W1 (nfst (nfst f)),
                         ord_relmon_bind W2 (nsnd (nfst f))⟩,
                       actW _ _ _ _ (nfst (nfst f)) (nsnd (nfst f)) (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation.
    cbv ; intuition.
    1-2:apply omon_bind; [sreflexivity| cbv=> ? ; auto].
    apply: actW_mon=> ?; [apply p0| apply q0| apply q].
  Qed.
  Next Obligation.
    f_equal ; [f_equal|]; rewrite ?HW_law1 //;
      apply Ssig_eq ;apply: funext=> a /=; apply: monad_law2.
  Qed.
  Next Obligation.
    move: f => [[f1 f2] frel].
    f_equal ; [f_equal|] ; apply Ssig_eq.
    1-2:apply: funext=> a /=; apply: monad_law1.
    apply (f_equal Spr1). apply: HW_law2.
  Qed.
  Next Obligation.
    f_equal ; [f_equal|] ; apply Ssig_eq.
    1-2: apply: funext=> a /=; rewrite /bind monad_law3 //.
    apply (f_equal Spr1). apply: HW_law3.
  Qed.

  Context (θW : forall {A}, OrdCat⦅Jprod (M12 A);W0 A⦆).
  Context (HθW_law1 : forall {A},
              θW _ ∙ ofmap Jprod (ord_relmon_unit M12 A)
                 = η A).
  Context (HθW_law2 : forall {A B} (f:TypeCatSq⦅A;M12 B⦆),
              θW _ ∙ ofmap Jprod (ord_relmon_bind M12 f)
                 = actW _ _ _ _
                         (θ1 _ ∙ ofmap discr (nfst f))
                         (θ2 _ ∙ ofmap discr (nsnd f))
                         (θW _ ∙ ofmap Jprod f) ∙ θW _).

  Program Definition θ : preRelationalEffectObservation M1 M2 W :=
    mkpreREO M1 M2 W (fun A => ⟨⟨θ1 (nfst A), θ2 (nsnd A)⟩, θW A⟩) _ _.
  Next Obligation.
    f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1).
    apply (rmm_law1 _ _ _ _ θ1).
    apply (rmm_law1 _ _ _ _ θ2).
    apply HθW_law1.
  Qed.
  Next Obligation.
    f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1).
    apply (rmm_law2 _ _ _ _ θ1).
    apply (rmm_law2 _ _ _ _ θ2).
    apply: HθW_law2.
  Qed.


  Import RelNotations.

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    ((forall γ1 : πl Γ, Spr1 (θ1 _) (c1 γ1) ≤ Spr1 w1 γ1) s/\
    (forall γ2 : πr Γ, Spr1 (θ2 _) (c2 γ2) ≤ Spr1 w2 γ2) s/\
    (forall γ : ⟬Γ⟭, Spr1 (θW ⟨_,_⟩) ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ Spr1 w (dfst γ)))
      (at level 85).

  Notation "⋅⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    (Hi unit ⊫ (fun=> c1) ≈ (fun=> c2) [{ @OrdCat_cst (discr unit) _ w1,
                                    @OrdCat_cst (discr unit) _ w2,
                                    @OrdCat_cst (discr (unit × unit)) _ w}]).

  Check (fun A B (c1 : M1 A) (c2: M2 B) (w1:dfst (W1 A)) (w2:dfst (W2 B)) (w3:dfst (W0 ⟨A,B⟩)) => ⋅⊫ c1 ≈ c2 [{ w1, w2, w3 }] ).

  (* And we prove the rule for binding computations *)

  Import SPropNotations.
  Arguments actW {_ _ _ _} _ _ _.
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
    refine (actW_mon A1 A2 B1 B2
                    (θ1 _ ∙ ofmap discr f1) wf1
                    (θ2 _ ∙ ofmap discr f2) wf2
                    (θW _ ∙ ofmap Jprod (to_prod f1 f2)) wf
                    _ _ _ _).
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
