From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Rel.

Set Primitive Projections.
Set Universe Polymorphism.


(* In this file we verify the correctness of the bind rule in the full setting *)

Section RelationalProgramLogicFromRelativeMonad.

  (* The context takes all components of a (full) relational specification monad *)

  (* Basic setup for each side: computational monad, unary specification monad
  and an effect observation relating these *)


  Context (M01 M02 : Monad).
  Definition M1 := (monad_to_relmon M01).
  Definition M2 := (monad_to_relmon M02).

  Context (W : RelationalSpecMonad)
          (θ : relationalEffectObservation M1 M2 W).

  Notation W1 := (rsm_left W).
  Notation W2 := (rsm_right W).
  Notation M12 := (compPair M01 M02).
  Notation θ1 := (reo_left θ).
  Notation θ2 := (reo_right θ).
  Notation Wrel := (rsm_rel W).
  Notation W0 := (rsmc_carrier Wrel).
  Notation η := (rsmc_return Wrel).
  Notation actW := (rsmc_act Wrel).


  Notation θrc := (reo_rel θ).
  Notation θW := (@reoc_carrier _ _ _ _ _ _ _ θrc ⟨_,_⟩).

  Import SPropNotations.
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


  Lemma equal_f {A B} (x:A) (f g : forall x:A, B x) : f = g -> f x = g x.
  Proof. move=> ? ; f_equal=> //. Qed.

  Lemma ordCat_helper {A B} (f g : OrdCat⦅A;B⦆) : f ⪷ g -> forall (x y:dfst A), x ≤ y -> f∙1 x ≤ g∙1 y.
  Proof.
    move=> Hfg x y Hxy; estransitivity.
    apply: (f∙2); exact: Hxy.
    apply: Hfg.
  Qed.

  (* And we prove the rule for binding computations *)

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
    split;[split|]=> ?.
    - move: (rmm_law2 _ _ _ _ θ1 _ _ f1)=> /(f_equal (fun f=> f∙1 m1)) /= ->.
      apply: ordCat_helper; last by apply: Hm1.
      apply: (ord_relmon_bind_proper W1); apply: Hf1.
    - move: (rmm_law2 _ _ _ _ θ2 _ _ f2)=> /(f_equal (fun f=> f∙1 m2)) /= ->.
      apply: ordCat_helper; last by apply: Hm2.
      apply: (ord_relmon_bind_proper W2); apply: Hf2.
    - move: (reoc_law2 _ _ _ _ _ θrc (to_prod f1 f2))
        => /(f_equal (fun f=> f∙1 ⟨m1,m2⟩)) /= ->; estransitivity.
      apply: rsmc_act_proper;
        [apply: Hf1| apply: Hf2| move=> [? ?] /=; eapply (Hf ⦑ _ , _ | tt⦒)].
      eapply ((actW _ _ _)∙2)=> //; apply (Hm ⦑tt,tt|I⦒).
  Qed.


    (* move: (rmm_law2 _ _ M12 (W' W) θ _ _ (to_prod f1 f2))=> /= [[H1 H2] H12]. *)
    (* intuition. *)
    (* move: (f_equal (fun h => h m1) H1)=> /= ->. *)
    (* apply omon_bind=> //; apply (Hm1 tt). *)
    (* move: (f_equal (fun h => h m2) H2)=> /= ->. *)
    (* apply omon_bind=> //; apply (Hm2 tt). *)
    (* move: (f_equal (fun h => h ⟨m1, m2⟩) H12) => /= -> //=. *)
    (* estransitivity. *)
    (* simpl in Hf1. *)
    (* apply: rsmc_act_proper. *)
    (* move=> ? ; apply Hf1. *)
    (* move=> ? ; apply Hf2. *)
    (* move=> [? ?] /=; eapply (Hf ⦑ _ , _ | tt⦒). *)
    (* eapply (Spr2 (actW _ _ _))=> //. *)
    (* apply (Hm ⦑tt,tt|I⦒). *)


  (* Definition bindStrongRSM {Γ A1 A2 B1 B2} *)
  (*            (wm1 : πl Γ -> W1 A1) *)
  (*            (wm2 : πr Γ -> W2 A2) *)
  (*            (wmrel : ⟬Γ⟭ -> W A1 A2) *)
  (*            (wf1 : πl Γ × A1 -> W1 B1) *)
  (*            (wf2 : πr Γ × A2 -> W2 B2) *)
  (*            (wfrel : ⟬extends Γ A1 A2⟭ -> W B1 B2) *)
  (* : ⟬Γ⟭ -> Wrel B1 B2 *)

  (* Definition to_ordProd (Γ : ) *)
  (*            (c1 : OrdCat⦅πl Γ;M1 A1⦆) *)
  (*            (c2 : OrdCat⦅πr Γ;M2 A2⦆) *)
  (*            OrdCat⦅⟬Γ⟭; Jprod ⟨M1 A1, M2 A2⟩⦆ *)


  (* Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" := *)
  (*   ((θ1 _ ∙ c1 ⪷ w1) s/\ (θ2 _ ∙ c2 ⪷ w2) s/\ *)
  (*    (orall γ : ⟬Γ⟭, θW∙1 ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ w∙1 (dfst γ))) *)
  (*     (at level 85). *)


End RelationalProgramLogicFromRelativeMonad.
